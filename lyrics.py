"""
The Visualizer - lyrics engine

This module is intentionally separate from the main visualizer.
It handles:
    - synced-lyrics fetching
    - SQLite caching
    - timestamp parsing
    - very cheap current-line lookup during playback

The playback loop should NEVER call the network. Fetching happens once when
lyrics are requested for a song; playback only uses get_current_line().
"""

import bisect
import os
import re
import sqlite3
import time
import threading
import shutil
import subprocess
import tempfile
import sys
import json

import requests


# ---------------------------------------------------------------------------
# SETTINGS
# ---------------------------------------------------------------------------

LYRICS_USER_AGENT = "TheVisualizer-Lyrics/1.0 (local music visualizer project)"
LRCLIB_URL = "https://lrclib.net/api/get"
LRCLIB_SEARCH_URL = "https://lrclib.net/api/search"
KARALYR_API_BASE = "https://karalyr.com/api"
KARALYR_GET_URL = KARALYR_API_BASE + "/get"
KARALYR_SEARCH_URL = KARALYR_API_BASE + "/search"
LRCAPI_BASE = "https://api.lrc.cx/api/v1/lyrics"
LRCAPI_SINGLE_URL = LRCAPI_BASE + "/single"
LRCAPI_SEARCH_URL = LRCAPI_BASE + "/advance"
SYNCLRC_API_BASE = "https://api.synclrc.dev"
SYNCLRC_SEARCH_URL = SYNCLRC_API_BASE + "/search"
SYNCLRC_LYRICS_URL = SYNCLRC_API_BASE + "/lyrics"
LRCMUX_API_BASE = "https://api.lrcmux.dev"
LRCMUX_GET_URL = LRCMUX_API_BASE + "/get"
REQUEST_TIMEOUT = (10, 30)
LRCLIB_REQUEST_GAP = 0.35
LRCLIB_RETRIES = 3
LRCLIB_RETRY_DELAY = 1.5
CACHE_MAX_AGE = 30 * 24 * 60 * 60  # Refresh cached lyrics after 30 days.
LYRICS_CACHE_VERSION = "v8"

# If the main vibe database module is available, use its database.  This keeps
# lyrics in the same SQLite database as the rest of The Visualizer without
# hard-coding a database filename here.
DEFAULT_DB_FILENAME = "the_visualizer.db"

# syncedlyrics is a dedicated multi-provider LRC searcher.  We invoke its
# --synced-only CLI first so plaintext lyrics can never be mistaken for
# synchronized lyrics.  The package itself supports multiple providers such
# as LRCLIB, Musixmatch, NetEase and Megalobiz.
SYNCEDLYRICS_COMMAND_TIMEOUT = 45
SYNCEDLYRICS_MAX_QUERIES = 12
MUSICBRAINZ_SEARCH_URL = "https://musicbrainz.org/ws/2/recording/"
MUSICBRAINZ_REQUEST_GAP = 0.35



# ---------------------------------------------------------------------------
# YOUTUBE MUSIC FALLBACK
# ---------------------------------------------------------------------------

# YouTube Music access is optional.  We use the maintained ytmusicapi package
# rather than scraping HTML ourselves.  It supports unauthenticated search and
# lyrics retrieval; authentication is only needed for account/library actions.
# If the package is not installed, this provider is simply skipped and the
# existing providers continue normally.
YTMUSIC_MAX_CANDIDATES = 5
YTMUSIC_SEARCH_TIMEOUT = (5, 15)


def _duration_from_ytmusic_result(item):
    """Return YouTube Music result duration in seconds when available."""
    for key in ("duration_seconds", "durationSeconds"):
        value = item.get(key) if isinstance(item, dict) else None
        number = _safe_float(value)
        if number and number > 0:
            return number

    duration = item.get("duration") if isinstance(item, dict) else None
    if isinstance(duration, (int, float)):
        return float(duration)
    if isinstance(duration, str):
        parts = duration.strip().split(":")
        try:
            if len(parts) == 2:
                return int(parts[0]) * 60 + float(parts[1])
            if len(parts) == 3:
                return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
        except (TypeError, ValueError):
            pass
    return None


def _ytmusic_artist_names(item):
    artists = item.get("artists") if isinstance(item, dict) else None
    if isinstance(artists, list):
        names = []
        for artist_item in artists:
            if isinstance(artist_item, dict):
                name = str(artist_item.get("name") or "").strip()
            else:
                name = str(artist_item or "").strip()
            if name:
                names.append(name)
        if names:
            return ", ".join(names)

    for key in ("artist", "author"):
        value = item.get(key) if isinstance(item, dict) else None
        if value:
            return str(value).strip()
    return ""


def _ytmusic_extract_lyrics_browse_id(value):
    """Find a YouTube Music lyrics browse id inside a watch-list response."""
    if isinstance(value, dict):
        for key, child in value.items():
            key_text = str(key).casefold()
            if key_text in {"lyrics", "lyricsbrowseid", "lyrics_browse_id"}:
                if isinstance(child, str) and child.startswith("MPLY"):
                    return child
                if isinstance(child, dict):
                    found = _ytmusic_extract_lyrics_browse_id(child)
                    if found:
                        return found
            found = _ytmusic_extract_lyrics_browse_id(child)
            if found:
                return found
    elif isinstance(value, list):
        for child in value:
            found = _ytmusic_extract_lyrics_browse_id(child)
            if found:
                return found
    return None


def _ytmusic_timed_lyrics_to_lrc(lyrics_lines):
    """Convert ytmusicapi timed lyric objects to ordinary line-synced LRC."""
    if not isinstance(lyrics_lines, list):
        return ""

    output = []
    for line in lyrics_lines:
        if isinstance(line, dict):
            text = str(line.get("text") or "").strip()
            start = line.get("start_time", line.get("startTime"))
        else:
            text = str(getattr(line, "text", "") or "").strip()
            start = getattr(line, "start_time", None)

        if not text or start is None:
            continue
        try:
            # ytmusicapi reports timed lyric positions in milliseconds.
            seconds = float(start) / 1000.0
        except (TypeError, ValueError):
            continue
        if seconds < 0:
            continue
        output.append(f"[{_format_lrc_time(seconds)}]{text}")

    return "\n".join(output)


def _fetch_lyrics_youtube_music(title, artist="", album="", duration=None,
                                timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Search YouTube Music and retrieve its own timed lyrics.

    This provider is deliberately after LRCLIB.  Search results are validated
    against the requested title/artist/duration before their lyrics are used,
    so an unrelated YouTube upload cannot silently become the lyric source.

    Requires the optional ``ytmusicapi`` package.  No login/cookies are used.
    """
    try:
        from ytmusicapi import YTMusic
    except Exception as exc:
        return None, f"ytmusicapi is not installed: {exc}"

    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title:
        return None, None

    queries = []
    if artist and artist.casefold() not in {"unknown artist", "unknown", "n/a", "none"}:
        queries.append(f"{artist} {title}")
    queries.append(title)
    for query in extra_queries or []:
        if query:
            queries.append(str(query).strip())

    unique_queries = []
    seen = set()
    for query in queries:
        key = normalize_text(query)
        if key and key not in seen:
            seen.add(key)
            unique_queries.append(query)

    try:
        yt = YTMusic()
    except Exception as exc:
        return None, f"YouTube Music initialization failed: {exc}"

    requested_duration = _safe_float(duration)
    errors = []
    candidates = []

    for query in unique_queries[:3]:
        try:
            print(f"YouTube Music search: {query}")
            results = yt.search(query, filter="songs", limit=YTMUSIC_MAX_CANDIDATES)
        except TypeError:
            try:
                results = yt.search(query, filter="songs")
            except Exception as exc:
                errors.append(f"search {query}: {exc}")
                continue
        except Exception as exc:
            errors.append(f"search {query}: {exc}")
            continue

        if not isinstance(results, list):
            continue
        for item in results[:YTMUSIC_MAX_CANDIDATES]:
            if not isinstance(item, dict) or not item.get("videoId"):
                continue
            candidate_title = str(item.get("title") or "").strip()
            candidate_artist = _ytmusic_artist_names(item)
            candidate_album = ""
            album_value = item.get("album")
            if isinstance(album_value, dict):
                candidate_album = str(album_value.get("name") or "").strip()
            elif album_value:
                candidate_album = str(album_value).strip()
            candidate_duration = _duration_from_ytmusic_result(item)

            result = {
                "success": False,
                "status": "not_found",
                "source": "youtube_music",
                "matched_title": candidate_title,
                "matched_artist": candidate_artist,
                "matched_album": candidate_album,
                "duration": candidate_duration,
                "synced_lyrics": "",
                "plain_lyrics": "",
                "video_id": item.get("videoId"),
            }
            ok, reason, _ = _provider_result_matches_request(
                result, title, artist, album, requested_duration,
                strict_duration=False,
            )
            if ok:
                candidates.append(result)

    # Highest-scoring candidates are checked first.  This avoids making a
    # request for lyrics for every search result.
    candidates.sort(key=lambda item: _provider_result_matches_request(
        item, title, artist, album, requested_duration, strict_duration=False
    )[2], reverse=True)

    for candidate in candidates[:YTMUSIC_MAX_CANDIDATES]:
        video_id = candidate.get("video_id")
        try:
            watch = yt.get_watch_playlist(videoId=video_id, limit=1)
            lyrics_browse_id = _ytmusic_extract_lyrics_browse_id(watch)
            if not lyrics_browse_id:
                print(f"YouTube Music: no lyrics browse id for {video_id}")
                continue

            lyrics_data = yt.get_lyrics(lyrics_browse_id, timestamps=True)
            if not lyrics_data:
                continue

            raw_lines = lyrics_data.get("lyrics") if isinstance(lyrics_data, dict) else None
            lrc = _ytmusic_timed_lyrics_to_lrc(raw_lines)
            if not lrc or not parse_synced_lyrics_compact(lrc):
                continue

            result = _lrc_text_to_result(
                lrc, title, artist, album,
                source="youtube_music",
            )
            if not result:
                continue
            result.update({
                "matched_title": candidate.get("matched_title") or title,
                "matched_artist": candidate.get("matched_artist") or artist,
                "matched_album": candidate.get("matched_album") or album,
                "duration": candidate.get("duration"),
                "video_id": video_id,
                "fallback": "youtube_music",
            })
            ok, reason, _ = _provider_result_matches_request(
                result, title, artist, album, requested_duration,
                strict_duration=False,
            )
            if ok:
                print(
                    "Lyrics FOUND: YouTube Music — "
                    f"{result.get('matched_title')} / {result.get('matched_artist')}"
                )
                return result, None
            print(f"YouTube Music result rejected after lyrics fetch: {reason}")
        except Exception as exc:
            errors.append(f"video {video_id}: {exc}")

    if errors:
        return None, " | ".join(errors)[-5000:]
    return None, None


# ---------------------------------------------------------------------------
# DATABASE
# ---------------------------------------------------------------------------


def get_default_database_path():
    """Return the project's existing SQLite database when possible."""
    try:
        import identify_song_and_vibe as vibe_detector

        initializer = getattr(vibe_detector, "initialize_vibe_database", None)
        if callable(initializer):
            path = initializer()
            if path:
                return os.path.abspath(path)
    except Exception:
        # lyrics.py must still work as a standalone module.
        pass

    return os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        DEFAULT_DB_FILENAME,
    )


def ensure_lyrics_table(connection):
    """Create the lyrics cache table if it does not already exist."""
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS visualizer_song_lyrics (
            fingerprint_key TEXT PRIMARY KEY,
            title TEXT NOT NULL DEFAULT '',
            artist TEXT NOT NULL DEFAULT '',
            album TEXT NOT NULL DEFAULT '',
            duration REAL,
            synced_lyrics TEXT NOT NULL DEFAULT '',
            plain_lyrics TEXT NOT NULL DEFAULT '',
            source TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'not_found',
            updated_at REAL NOT NULL
        )
        """
    )
    connection.commit()


def _open_database(db_path=None):
    path = os.path.abspath(db_path or get_default_database_path())
    connection = sqlite3.connect(path)
    ensure_lyrics_table(connection)
    return connection


# ---------------------------------------------------------------------------
# NORMALIZATION / CACHE KEY
# ---------------------------------------------------------------------------


def normalize_text(value):
    """Normalize text for matching/searching without changing display text."""
    value = str(value or "").lower()
    value = value.replace("&", "and")
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return " ".join(value.split())


def make_cache_key(title, artist, album="", duration=None):
    """Make a stable key for a song's lyrics cache entry."""
    title_key = normalize_text(title)
    artist_key = normalize_text(artist)
    album_key = normalize_text(album)

    # Duration is deliberately rounded.  Small differences between embedded
    # metadata and the API should not create duplicate lyric entries.
    if duration is None:
        duration_key = ""
    else:
        try:
            duration_key = str(int(round(float(duration))))
        except (TypeError, ValueError):
            duration_key = ""

    return "|".join((LYRICS_CACHE_VERSION, artist_key, title_key, album_key, duration_key))


# ---------------------------------------------------------------------------
# SYNCED LYRIC PARSER
# ---------------------------------------------------------------------------

# Supports normal LRC timestamps such as:
# [00:17.12]Hello
# [01:02.500]World
# It also supports multiple timestamps on one line:
# [00:10.00][00:20.00]Repeated line
LRC_TIMESTAMP_RE = re.compile(r"\[(\d{1,3}):(\d{2})(?:[.:](\d{1,3}))?\]")


def _timestamp_to_seconds(match):
    minutes = int(match.group(1))
    seconds = int(match.group(2))
    fraction_text = match.group(3) or "0"

    # LRC commonly uses hundredths, but accepting 1-3 digits makes this
    # tolerant of both .1, .12 and .123 styles.
    fraction = int(fraction_text) / (10 ** len(fraction_text))
    return minutes * 60.0 + seconds + fraction


def parse_enhanced_lyrics(synced_lyrics):
    """Parse Enhanced LRC with per-word timestamps.

    Supported form:
        [00:12.34]<00:12.34>Hello <00:12.70>world

    Returns line dictionaries with ``time``, ``text`` and ``words``.  Each
    word entry is ``{"time": seconds, "text": word}``.
    """
    if not synced_lyrics:
        return []

    word_re = re.compile(r"<(?P<time>\d{1,3}:\d{2}(?:\.\d{1,3})?)>")
    lines = []
    for raw_line in str(synced_lyrics).splitlines():
        line_times = list(LRC_TIMESTAMP_RE.finditer(raw_line))
        if not line_times:
            continue
        line_time = _timestamp_to_seconds(line_times[0])
        body = LRC_TIMESTAMP_RE.sub("", raw_line).strip()
        matches = list(word_re.finditer(body))
        if not matches:
            continue

        words = []
        for i, match in enumerate(matches):
            word_time = _parse_inline_timestamp(match.group("time"))
            if word_time is None:
                continue
            end = matches[i + 1].start() if i + 1 < len(matches) else len(body)
            word_text = body[match.end():end]
            words.append({"time": word_time, "text": word_text})

        if words:
            text = "".join(item["text"] for item in words).strip()
            lines.append({"time": line_time, "text": text, "words": words})

    lines.sort(key=lambda item: item["time"])
    return lines


def _parse_inline_timestamp(value):
    try:
        parts = str(value).split(":")
        if len(parts) != 2:
            return None
        return (float(parts[0]) * 60.0) + float(parts[1])
    except (TypeError, ValueError):
        return None


def parse_synced_lyrics(synced_lyrics):
    """
    Parse LRC text into a sorted list of dictionaries:

        [{"time": 12.34, "text": "First line"}, ...]

    Metadata-only LRC lines such as [ar:Artist] are ignored.
    Empty lyric lines are retained when they have a timestamp because they
    can be meaningful as a deliberate pause between lyric lines.
    """
    if not synced_lyrics:
        return []

    parsed = []

    for raw_line in str(synced_lyrics).splitlines():
        matches = list(LRC_TIMESTAMP_RE.finditer(raw_line))
        if not matches:
            continue

        text = LRC_TIMESTAMP_RE.sub("", raw_line).strip()

        for match in matches:
            parsed.append(
                {
                    "time": _timestamp_to_seconds(match),
                    "text": text,
                }
            )

    parsed.sort(key=lambda item: item["time"])
    return parsed


def parse_synced_lyrics_compact(synced_lyrics):
    """
    Parse LRC into the compact representation used by playback:

        [(timestamp_seconds, text), ...]

    This is the representation recommended for the visualizer because it is
    small and works directly with bisect_right().
    """
    parsed = parse_synced_lyrics(synced_lyrics)
    return [(item["time"], item["text"]) for item in parsed]


# ---------------------------------------------------------------------------
# SCRIPT -> ROMANIZED LYRICS
# ---------------------------------------------------------------------------

# Devanagari transliteration is intentionally local and dependency-free.  It
# converts Hindi lyrics to readable Latin text (pronunciation), not English
# meaning.  The original lyrics are never modified in the cache.
_DEVANAGARI_VOWELS = {
    "अ": "a", "आ": "aa", "इ": "i", "ई": "ee", "उ": "u", "ऊ": "oo",
    "ऋ": "ri", "ए": "e", "ऐ": "ai", "ओ": "o", "औ": "au",
    "ऑ": "o", "ॲ": "a",
}
_DEVANAGARI_MATRAS = {
    "ा": "aa", "ि": "i", "ी": "ee", "ु": "u", "ू": "oo",
    "ृ": "ri", "े": "e", "ै": "ai", "ो": "o", "ौ": "au",
    "ॉ": "o", "ॅ": "a",
}
_DEVANAGARI_CONSONANTS = {
    "क": "k", "ख": "kh", "ग": "g", "घ": "gh", "ङ": "ng",
    "च": "ch", "छ": "chh", "ज": "j", "झ": "jh", "ञ": "ny",
    "ट": "t", "ठ": "th", "ड": "d", "ढ": "dh", "ण": "n",
    "त": "t", "थ": "th", "द": "d", "ध": "dh", "न": "n",
    "प": "p", "फ": "ph", "ब": "b", "भ": "bh", "म": "m",
    "य": "y", "र": "r", "ल": "l", "व": "v", "श": "sh",
    "ष": "sh", "स": "s", "ह": "h",
    "क़": "q", "ख़": "kh", "ग़": "gh", "ज़": "z", "ड़": "r",
    "ढ़": "rh", "फ़": "f", "य़": "y",
}
_DEVANAGARI_SIGNS = {
    "ं": "n", "ँ": "n", "ः": "h", "ऽ": "'", "्": "",
}
_DEVANAGARI_DIGITS = str.maketrans("०१२३४५६७८९", "0123456789")


def transliterate_devanagari(text):
    """Romanize Devanagari text for pronunciation, without translating it."""
    text = str(text or "")
    if not text:
        return ""

    output = []
    i = 0
    while i < len(text):
        char = text[i]
        consonant = _DEVANAGARI_CONSONANTS.get(char)

        if consonant is not None:
            # A consonant normally carries the inherent 'a'.  A following
            # halant removes it; a following matra replaces it.
            if i + 1 < len(text) and text[i + 1] == "्":
                output.append(consonant)
                i += 2
                continue
            if i + 1 < len(text) and text[i + 1] in _DEVANAGARI_MATRAS:
                output.append(consonant + _DEVANAGARI_MATRAS[text[i + 1]])
                i += 2
                continue
            output.append(consonant + "a")
            i += 1
            continue

        if char in _DEVANAGARI_VOWELS:
            output.append(_DEVANAGARI_VOWELS[char])
            i += 1
            continue

        if char in _DEVANAGARI_SIGNS:
            output.append(_DEVANAGARI_SIGNS[char])
            i += 1
            continue

        output.append(char.translate(_DEVANAGARI_DIGITS))
        i += 1

    # A few common Hindi orthographic endings are conventionally pronounced
    # without the final schwa.  Keep this conservative rather than trying to
    # infer full Hindi phonology from spelling.
    result = "".join(output)
    result = re.sub(r"(?<=[bcdfghjklmnpqrstvwxyz])a(?=\s|$|[,.!?;:])", "", result, flags=re.I)
    result = re.sub(r"\s+", " ", result)
    return result.strip()


def transliterate_lyrics_line(text):
    """Romanize supported Indian-script lyrics while leaving other scripts unchanged."""
    text = str(text or "")
    if not text:
        return ""
    if any("\u0900" <= char <= "\u097f" for char in text):
        return transliterate_devanagari(text)
    return text

# ---------------------------------------------------------------------------
# CURRENT-LINE LOOKUP
# ---------------------------------------------------------------------------


def prepare_lyrics(lines):
    """Prepare line and optional word-level timestamps for cheap playback lookup."""
    if not lines:
        return {"times": [], "lines": [], "words": []}

    compact = []
    for item in lines:
        if isinstance(item, dict):
            words = []
            for word in item.get("words") or []:
                try:
                    words.append((float(word["time"]), str(word.get("text", ""))))
                except (KeyError, TypeError, ValueError):
                    pass
            compact.append((float(item["time"]), str(item.get("text", "")), words))
        else:
            compact.append((float(item[0]), str(item[1]), []))

    compact.sort(key=lambda item: item[0])
    return {
        "times": [item[0] for item in compact],
        "lines": [item[1] for item in compact],
        "words": [item[2] for item in compact],
        "word_times": [[word[0] for word in item[2]] for item in compact],
        "has_word_sync": any(item[2] for item in compact),
    }


def get_current_line(prepared_lyrics, playback_seconds):
    """Return the lyric line active at playback_seconds."""
    if not prepared_lyrics:
        return None
    times = prepared_lyrics.get("times", [])
    lines = prepared_lyrics.get("lines", [])
    if not times:
        return None
    try:
        position = float(playback_seconds)
    except (TypeError, ValueError):
        return None
    index = bisect.bisect_right(times, position) - 1
    return lines[index] if index >= 0 else None


def get_current_word_index(prepared_lyrics, playback_seconds, line_index=None):
    """Return the active word index inside the active line, or -1."""
    if not prepared_lyrics:
        return -1
    if line_index is None:
        line_index = get_current_line_index(prepared_lyrics, playback_seconds)
    if line_index < 0:
        return -1
    word_times = prepared_lyrics.get("word_times", [])
    if line_index >= len(word_times) or not word_times[line_index]:
        return -1
    position = float(playback_seconds)
    return bisect.bisect_right(word_times[line_index], position) - 1


def get_current_word(prepared_lyrics, playback_seconds):
    line_index = get_current_line_index(prepared_lyrics, playback_seconds)
    word_index = get_current_word_index(prepared_lyrics, playback_seconds, line_index)
    if line_index < 0 or word_index < 0:
        return None
    return prepared_lyrics["words"][line_index][word_index][1]

def get_current_line_index(prepared_lyrics, playback_seconds):
    """Return the active lyric index, or -1 before the first line."""
    if not prepared_lyrics:
        return -1

    times = prepared_lyrics.get("times", [])
    if not times:
        return -1

    try:
        position = float(playback_seconds)
    except (TypeError, ValueError):
        return -1

    return bisect.bisect_right(times, position) - 1


# ---------------------------------------------------------------------------
# LRCLIB
# ---------------------------------------------------------------------------


def _safe_float(value):
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _metadata_unknown(value):
    return normalize_text(value) in {"", "unknown", "unknown artist", "unknown album", "n a", "none"}


def _strip_artist_qualifiers(value):
    """Normalize common collaboration/feature suffixes for artist matching."""
    value = normalize_text(value)
    if not value:
        return ""
    # Keep the primary performer before common feature/collaboration markers.
    value = re.split(r"\b(?:feat|featuring|ft)\b", value, maxsplit=1)[0].strip()
    value = re.sub(r"\s+(?:and|with)\s+.*$", "", value).strip()
    return value


def _title_match_score(requested, matched):
    """Return 0 for exact title, 1 for a safe edition/qualifier match, else None."""
    requested = normalize_text(requested)
    matched = normalize_text(matched)
    if not requested or not matched:
        return None
    if requested == matched:
        return 0

    # Providers sometimes append edition labels such as 'remastered', 'radio edit',
    # 'live', etc.  Only accept those when the requested title is the complete base
    # title; never accept an unrelated title that merely shares a token.
    removable = {
        "remastered", "remaster", "radio", "edit", "version", "mix", "acoustic",
        "live", "demo", "instrumental", "mono", "stereo", "deluxe", "bonus",
        "official", "music", "video", "single", "album", "from", "original",
        "soundtrack", "ost", "reissue",
    }
    requested_tokens = requested.split()
    matched_tokens = matched.split()
    if matched_tokens[:len(requested_tokens)] == requested_tokens:
        suffix = [token for token in matched_tokens[len(requested_tokens):] if token not in removable]
        if not suffix:
            return 1
    if requested_tokens[:len(matched_tokens)] == matched_tokens:
        suffix = [token for token in requested_tokens[len(matched_tokens):] if token not in removable]
        if not suffix:
            return 1
    return None


def _artist_match(requested, matched):
    """Return True for the same performer, including common feature variants."""
    requested_n = normalize_text(requested)
    matched_n = normalize_text(matched)
    if not requested_n or not matched_n:
        return False
    if requested_n == matched_n:
        return True
    requested_base = _strip_artist_qualifiers(requested_n)
    matched_base = _strip_artist_qualifiers(matched_n)
    if requested_base == matched_base:
        return True
    # Accept a provider spelling that contains the requested primary artist,
    # e.g. 'Alan Walker K 391' for a query for 'Alan Walker'.
    if requested_base and requested_base in matched_n:
        return True
    if matched_base and matched_base in requested_n:
        return True
    return False


def _validate_matched_metadata(requested_title, requested_artist, requested_album,
                               requested_duration, matched_title, matched_artist,
                               matched_album=None, matched_duration=None,
                               strict_duration=False):
    """Return (ok, reason, score) for a provider's returned track metadata."""
    title_score = _title_match_score(requested_title, matched_title)
    if title_score is None:
        return False, f"title mismatch: requested={requested_title!r} returned={matched_title!r}", 999

    if not _metadata_unknown(requested_artist):
        if _metadata_unknown(matched_artist) or not _artist_match(requested_artist, matched_artist):
            return False, f"artist mismatch: requested={requested_artist!r} returned={matched_artist!r}", 999

    album_penalty = 0
    if not _metadata_unknown(requested_album) and not _metadata_unknown(matched_album):
        req_album = normalize_text(requested_album)
        got_album = normalize_text(matched_album)
        if req_album != got_album and req_album not in got_album and got_album not in req_album:
            album_penalty = 1

    duration_penalty = 0.0
    req_duration = _safe_float(requested_duration)
    got_duration = _safe_float(matched_duration)
    if req_duration and got_duration:
        duration_delta = abs(req_duration - got_duration)
        allowed = 3.0 if strict_duration else 10.0
        # Local files are often music videos, extended edits, or files with
        # intro/outro material while lyric providers store the normal audio
        # release.  When title + artist match, allow a larger difference in
        # non-strict searches so a 4:23 video of a 3:55 song is not rejected.
        # Strict exact lookups remain conservative.
        if not strict_duration and title_score == 0 and not _metadata_unknown(requested_artist):
            allowed = 45.0
        if duration_delta > allowed:
            return False, f"duration mismatch: requested={req_duration:.2f}s returned={got_duration:.2f}s", 999
        duration_penalty = duration_delta

    # Lower score is better. Exact title/artist/duration is preferred.
    return True, "ok", title_score * 20 + album_penalty * 5 + duration_penalty


def _provider_result_matches_request(result, title, artist, album="", duration=None,
                                     strict_duration=False):
    """Validate a normalized provider result against the requested recording."""
    if not isinstance(result, dict):
        return False, "provider returned no result"
    return _validate_matched_metadata(
        title, artist, album, duration,
        result.get("matched_title") or result.get("title"),
        result.get("matched_artist") or result.get("artist"),
        result.get("matched_album") or result.get("album"),
        result.get("matched_duration") if result.get("matched_duration") is not None else result.get("duration"),
        strict_duration=strict_duration,
    )


def _select_valid_lyrics_results(results, title, artist, album="", duration=None,
                                 strict_duration=False):
    """Filter provider candidates to only recordings that match the requested song."""
    valid = []
    for result in results or []:
        ok, reason, score = _provider_result_matches_request(
            result, title, artist, album, duration, strict_duration=strict_duration
        )
        if not ok:
            print(f"Lyrics candidate REJECTED: {reason}")
            continue
        if not result.get("synced_lyrics") and not result.get("plain_lyrics"):
            continue
        result = dict(result)
        result["match_score"] = score
        valid.append(result)
    valid.sort(key=lambda item: (0 if item.get("synced_lyrics") else 1, item.get("match_score", 999)))
    return valid


def _fetch_lyrics_lrclib_exact(title, artist, album="", duration=None, timeout=REQUEST_TIMEOUT):
    """Ask LRCLIB for the exact track signature before broad searches."""
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title or _metadata_unknown(artist):
        return None, None

    params = {"track_name": title, "artist_name": artist}
    if album and not _metadata_unknown(album):
        params["album_name"] = album
    duration_value = _safe_float(duration)
    if duration_value and duration_value > 0:
        params["duration"] = duration_value

    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    last_error = None
    for attempt in range(1, LRCLIB_RETRIES + 1):
        try:
            response = requests.get(LRCLIB_URL, params=params, headers=headers, timeout=timeout)
            if response.status_code == 404:
                return None, None
            if response.status_code == 429:
                retry_after = response.headers.get("Retry-After")
                try:
                    wait = max(0.5, min(float(retry_after), 10.0)) if retry_after else LRCLIB_RETRY_DELAY * attempt
                except (TypeError, ValueError):
                    wait = LRCLIB_RETRY_DELAY * attempt
                if attempt < LRCLIB_RETRIES:
                    time.sleep(wait)
                    continue
            response.raise_for_status()
            data = response.json()
            result = _lrclib_result_from_data(data, title, artist, album)
            if not result or not result.get("success"):
                return None, None
            result["matched_id"] = data.get("id")
            result["instrumental"] = bool(data.get("instrumental"))
            ok, reason, score = _provider_result_matches_request(
                result, title, artist, album, duration, strict_duration=True
            )
            if not ok:
                print(f"LRCLIB exact result rejected: {reason}")
                return None, None
            result["match_score"] = score
            result["fallback"] = "lrclib_exact"
            return result, None
        except requests.RequestException as exc:
            last_error = exc
            if attempt < LRCLIB_RETRIES:
                time.sleep(LRCLIB_RETRY_DELAY * attempt)
        except (ValueError, TypeError) as exc:
            last_error = exc
            break
    return None, last_error


def _lrclib_result_from_data(data, fallback_title, fallback_artist, fallback_album=""):
    """Convert one LRCLIB record into our normal lyric-result structure."""
    if not isinstance(data, dict):
        return None

    synced = str(data.get("syncedLyrics") or "").strip()
    plain = str(data.get("plainLyrics") or "").strip()

    if synced:
        status = "synced"
    elif plain:
        status = "plain_only"
    else:
        status = "not_found"

    return {
        "success": bool(synced or plain),
        "status": status,
        "source": "lrclib",
        "synced_lyrics": synced,
        "plain_lyrics": plain,
        "matched_title": data.get("trackName") or data.get("name") or fallback_title,
        "matched_artist": data.get("artistName") or fallback_artist,
        "matched_album": data.get("albumName") or fallback_album,
        "matched_duration": _safe_float(data.get("duration")),
    }


def _search_lrclib(title, artist="", album="", duration=None, timeout=REQUEST_TIMEOUT, headers=None, extra_queries=None):
    """Search LRCLIB using several increasingly broad queries and rank matches.

    LRCLIB's search API supports both ``track_name`` and ``q``.  ``q`` is
    especially useful when the title is known but the artist metadata is
    missing or unreliable, because it searches title, artist and album fields.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    duration_value = _safe_float(duration)

    if not title:
        return []

    session = requests.Session()
    session.headers.update(headers or {
        "User-Agent": LYRICS_USER_AGENT,
        "Accept": "application/json",
    })

    # Search the structured title first, then the broader free-text query.
    # Extra queries are used only as fallback (for example, a filename-derived
    # "Aashiyan Barfi" query when the detector only knows the filename).
    query_specs = [
        {"track_name": title, "q": title},
    ]

    if artist and artist.casefold() not in {"unknown artist", "unknown", "n/a"}:
        query_specs.append({"track_name": title, "artist_name": artist})

    if album and album.casefold() not in {"unknown album", "unknown", "n/a"}:
        query_specs.append({"track_name": title, "album_name": album})

    for extra in extra_queries or []:
        extra = str(extra or "").strip()
        if extra:
            query_specs.append({"q": extra})

    # De-duplicate equivalent requests while preserving the useful order.
    unique_specs = []
    seen_specs = set()
    for spec in query_specs:
        key = tuple(sorted(spec.items()))
        if key not in seen_specs:
            seen_specs.add(key)
            unique_specs.append(spec)

    all_results = []
    seen_ids = set()
    last_error = None

    for params in unique_specs:
        found_this_query = False

        for attempt in range(1, LRCLIB_RETRIES + 1):
            try:
                response = session.get(
                    LRCLIB_SEARCH_URL,
                    params=params,
                    timeout=timeout,
                )

                if response.status_code == 404:
                    break

                if response.status_code == 429:
                    retry_after = response.headers.get("Retry-After")
                    try:
                        wait = max(0.5, min(float(retry_after), 10.0)) if retry_after else LRCLIB_RETRY_DELAY * attempt
                    except (TypeError, ValueError):
                        wait = LRCLIB_RETRY_DELAY * attempt
                    last_error = requests.HTTPError("LRCLIB rate limited search (HTTP 429)")
                    if attempt < LRCLIB_RETRIES:
                        time.sleep(wait)
                        continue
                    break

                response.raise_for_status()
                data = response.json()

                if not isinstance(data, list):
                    last_error = ValueError("LRCLIB search returned a non-list response")
                    break

                for item in data:
                    if not isinstance(item, dict):
                        continue
                    item_id = item.get("id")
                    if item_id is not None:
                        dedupe_key = ("id", str(item_id))
                    else:
                        dedupe_key = (
                            "meta",
                            normalize_text(item.get("trackName") or item.get("name")),
                            normalize_text(item.get("artistName")),
                            str(_safe_float(item.get("duration")) or ""),
                        )
                    if dedupe_key in seen_ids:
                        continue
                    seen_ids.add(dedupe_key)
                    all_results.append(item)
                    found_this_query = True

                break

            except requests.RequestException as exc:
                last_error = exc
                if attempt < LRCLIB_RETRIES:
                    time.sleep(LRCLIB_RETRY_DELAY * attempt)
            except (ValueError, TypeError) as exc:
                last_error = exc
                break

        # Be polite to LRCLIB and avoid bursts that can trigger 429/503.
        if len(unique_specs) > 1:
            time.sleep(LRCLIB_REQUEST_GAP)

        # Do NOT stop merely because one broad query returned results. A broad
        # title search can return an unsynced/poorly-matched record first.
        # Continue through the remaining query specs so artist/album/context
        # searches can contribute a better synced match.

    if not all_results:
        return None if last_error is not None else []

    normalized_title = normalize_text(title)
    normalized_artist = normalize_text(artist)
    normalized_album = normalize_text(album)

    extra_token_sets = []
    for extra in extra_queries or []:
        extra_text = normalize_text(extra)
        if extra_text:
            extra_token_sets.append({token for token in extra_text.split() if len(token) >= 3 and token not in {"the", "and", "feat", "from", "with"}})

    def rank(item):
        item_title = normalize_text(item.get("trackName") or item.get("name"))
        item_artist = normalize_text(item.get("artistName"))
        item_album = normalize_text(item.get("albumName"))
        item_duration = _safe_float(item.get("duration"))

        if item_title == normalized_title:
            title_penalty = 0
        elif normalized_title and normalized_title in item_title:
            title_penalty = 1
        else:
            title_penalty = 3

        if normalized_artist and normalized_artist not in {"unknown artist", "unknown", "n a"}:
            artist_penalty = 0 if item_artist == normalized_artist else 2
        else:
            artist_penalty = 0

        album_penalty = 0
        if normalized_album:
            album_penalty = 0 if item_album == normalized_album else 1

        distance = (
            abs(item_duration - duration_value)
            if item_duration is not None and duration_value is not None
            else 999999.0
        )

        metadata_tokens = set((item_title + " " + item_artist + " " + item_album).split())
        extra_match_penalty = 99
        for token_set in extra_token_sets:
            if token_set:
                matched = len(token_set & metadata_tokens)
                extra_match_penalty = min(extra_match_penalty, len(token_set) - matched)
        if not extra_token_sets:
            extra_match_penalty = 0

        # A synced result is always preferred over a plain-only result.
        synced_penalty = 0 if str(item.get("syncedLyrics") or "").strip() else 1

        return (
            extra_match_penalty,
            title_penalty,
            artist_penalty,
            album_penalty,
            synced_penalty,
            distance,
        )

    return sorted(all_results, key=rank)

def _karalyr_result_from_data(data, fallback_title, fallback_artist, fallback_album=""):
    """Convert one Karalyr/LRCLIB-compatible record into our result format."""
    if not isinstance(data, dict):
        return None

    synced = str(data.get("syncedLyrics") or "").strip()
    plain = str(data.get("plainLyrics") or "").strip()
    if synced:
        status = "synced"
    elif plain:
        status = "plain_only"
    else:
        status = "not_found"

    return {
        "success": bool(synced or plain),
        "status": status,
        "source": "karalyr",
        "synced_lyrics": synced,
        "plain_lyrics": plain,
        "matched_title": data.get("trackName") or data.get("name") or fallback_title,
        "matched_artist": data.get("artistName") or fallback_artist,
        "matched_album": data.get("albumName") or fallback_album,
        "matched_duration": _safe_float(data.get("duration")),
    }


def _search_karalyr(title, artist="", album="", duration=None, timeout=REQUEST_TIMEOUT,
                    headers=None, extra_queries=None):
    """Search Karalyr as a secondary lyrics provider.

    Karalyr documents an LRCLIB-compatible public API and a fuzzy /api/search
    endpoint supporting q, artist_name, track_name and album_name.  It is used
    only after LRCLIB fails, so normal behavior and cache results remain
    LRCLIB-first.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    duration_value = _safe_float(duration)
    if not title:
        return []

    session = requests.Session()
    session.headers.update(headers or {
        "User-Agent": LYRICS_USER_AGENT,
        "Accept": "application/json",
    })

    query_specs = [{"track_name": title}, {"q": title}]
    if artist and artist.casefold() not in {"unknown artist", "unknown", "n/a"}:
        query_specs.append({"track_name": title, "artist_name": artist})
    if album and album.casefold() not in {"unknown album", "unknown", "n/a"}:
        query_specs.append({"track_name": title, "album_name": album})
    for extra in extra_queries or []:
        extra = str(extra or "").strip()
        if extra:
            query_specs.append({"q": extra})

    unique_specs = []
    seen = set()
    for spec in query_specs:
        key = tuple(sorted(spec.items()))
        if key not in seen:
            seen.add(key)
            unique_specs.append(spec)

    results = []
    seen_ids = set()
    last_error = None

    for params in unique_specs:
        try:
            response = session.get(KARALYR_SEARCH_URL, params=params, timeout=timeout)
            if response.status_code == 404:
                continue
            response.raise_for_status()
            data = response.json()
            if not isinstance(data, list):
                continue
            for item in data:
                if not isinstance(item, dict):
                    continue
                item_id = item.get("id")
                key = ("id", str(item_id)) if item_id is not None else (
                    "meta",
                    normalize_text(item.get("trackName") or item.get("name")),
                    normalize_text(item.get("artistName")),
                    str(_safe_float(item.get("duration")) or ""),
                )
                if key in seen_ids:
                    continue
                seen_ids.add(key)
                results.append(item)
        except requests.RequestException as exc:
            last_error = exc
            continue
        except (ValueError, TypeError) as exc:
            last_error = exc
            continue

    if not results:
        return None if last_error is not None else []

    normalized_title = normalize_text(title)
    normalized_artist = normalize_text(artist)
    normalized_album = normalize_text(album)

    def rank(item):
        item_title = normalize_text(item.get("trackName") or item.get("name"))
        item_artist = normalize_text(item.get("artistName"))
        item_album = normalize_text(item.get("albumName"))
        item_duration = _safe_float(item.get("duration"))

        if item_title == normalized_title:
            title_penalty = 0
        elif normalized_title and normalized_title in item_title:
            title_penalty = 1
        else:
            title_penalty = 3

        if normalized_artist and normalized_artist not in {"unknown artist", "unknown", "n a"}:
            artist_penalty = 0 if item_artist == normalized_artist else 2
        else:
            artist_penalty = 0

        album_penalty = 0 if not normalized_album else (0 if item_album == normalized_album else 1)
        distance = abs(item_duration - duration_value) if item_duration is not None and duration_value is not None else 999999.0
        synced_penalty = 0 if str(item.get("syncedLyrics") or "").strip() else 1
        return (title_penalty, artist_penalty, album_penalty, synced_penalty, distance)

    return sorted(results, key=rank)


def _fetch_lyrics_karalyr(title, artist, album="", duration=None, timeout=REQUEST_TIMEOUT,
                          extra_queries=None):
    """Try Karalyr after LRCLIB, returning (result, network_error)."""
    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    unknown_artist = artist.casefold() in {"", "unknown artist", "unknown", "n/a", "none"}

    # Exact lookup is only useful when an artist is known. Karalyr's exact
    # endpoint documents artist_name + track_name as required.
    if not unknown_artist:
        params = {"track_name": title, "artist_name": artist}
        if album:
            params["album_name"] = album
        duration_value = _safe_float(duration)
        if duration_value is not None and duration_value > 0:
            params["duration"] = duration_value
        try:
            response = requests.get(KARALYR_GET_URL, params=params, headers=headers, timeout=timeout)
            if response.status_code == 200:
                result = _karalyr_result_from_data(response.json(), title, artist, album)
                if result and result.get("success"):
                    return result, None
            elif response.status_code not in (404, 400):
                response.raise_for_status()
        except requests.RequestException as exc:
            # Continue to broad search; a search can recover from an exact
            # lookup failure when the provider is reachable.
            exact_error = exc
        except (ValueError, TypeError):
            exact_error = None
    else:
        exact_error = None

    matches = _search_karalyr(
        title, artist=artist, album=album, duration=duration,
        timeout=timeout, headers=headers, extra_queries=extra_queries,
    )
    if matches:
        for match in matches:
            result = _karalyr_result_from_data(match, title, artist, album)
            if result and result.get("success"):
                result["fallback"] = "karalyr_search"
                return result, None

    return None, locals().get("exact_error")



# ---------------------------------------------------------------------------
# LRCAPI / SYNCLRC FALLBACK PROVIDERS
# ---------------------------------------------------------------------------


def _lrc_text_to_result(lrc_text, fallback_title, fallback_artist, fallback_album="", source="lrcapi"):
    """Turn raw LRC text into the common result structure."""
    text = str(lrc_text or "").strip()
    if not text:
        return None
    parsed = parse_synced_lyrics_compact(text)
    if not parsed:
        return None
    plain = "\n".join(line for _, line in parsed)
    return {
        "success": True,
        "status": "synced",
        "source": source,
        "synced_lyrics": text,
        "plain_lyrics": plain,
        "matched_title": fallback_title,
        "matched_artist": fallback_artist,
        "matched_album": fallback_album,
        "matched_duration": None,
    }


def _search_lrcapi(title, artist="", album="", duration=None, timeout=REQUEST_TIMEOUT,
                    extra_queries=None):
    """Search LrcAPI's JSON endpoint and return ranked LRC candidates.

    LrcAPI returns actual LRC text, which means a successful match is already
    synchronized and can go directly through our existing parser.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title:
        return []

    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    specs = [{"title": title, "artist": artist, "album": album}]
    if extra_queries:
        for q in extra_queries:
            q = str(q or "").strip()
            if q:
                specs.append({"title": q, "artist": artist, "album": album})

    results = []
    last_error = None
    seen = set()

    for params in specs:
        params = {k: v for k, v in params.items() if v}
        try:
            response = requests.get(LRCAPI_SEARCH_URL, params=params, headers=headers, timeout=timeout)
            response.raise_for_status()
            data = response.json()
            if not isinstance(data, list):
                continue
            for item in data:
                if not isinstance(item, dict):
                    continue
                lrc = str(item.get("lyrics") or "").strip()
                if not lrc:
                    continue
                key = item.get("id") or (normalize_text(item.get("title")), normalize_text(item.get("artist")), lrc[:80])
                if key in seen:
                    continue
                seen.add(key)
                results.append({
                    "lyrics": lrc,
                    "title": item.get("title") or title,
                    "artist": item.get("artist") or artist,
                    "album": item.get("album") or album,
                    "duration": item.get("duration"),
                })
        except requests.RequestException as exc:
            last_error = exc
        except (ValueError, TypeError):
            continue

    if not results:
        return None if last_error is not None else []

    wanted_title = normalize_text(title)
    wanted_artist = normalize_text(artist)
    wanted_album = normalize_text(album)

    def rank(item):
        item_title = normalize_text(item.get("title"))
        item_artist = normalize_text(item.get("artist"))
        title_penalty = 0 if item_title == wanted_title else (1 if wanted_title in item_title else 3)
        artist_penalty = 0 if not wanted_artist or wanted_artist in {"unknown", "unknown artist", "n a"} else (0 if item_artist == wanted_artist else 2)
        album_penalty = 0 if not wanted_album else 1
        return (title_penalty, artist_penalty, album_penalty)

    return sorted(results, key=rank)


def _fetch_lyrics_lrcapi(title, artist, album="", duration=None, timeout=REQUEST_TIMEOUT,
                         extra_queries=None):
    """Fetch synchronized LRC from LrcAPI, accepting only verified metadata matches."""
    matches = _search_lrcapi(title, artist, album, duration, timeout, extra_queries)
    if matches:
        candidates = []
        for match in matches:
            result = _lrc_text_to_result(
                match["lyrics"], match["title"], match["artist"], match.get("album") or album, source="lrcapi"
            )
            if result:
                result["matched_duration"] = _safe_float(match.get("duration"))
                candidates.append(result)
        valid = _select_valid_lyrics_results(candidates, title, artist, album, duration)
        if valid:
            valid[0]["fallback"] = "lrcapi"
            return valid[0], None
    return None, matches is None


def _synclrc_item_to_result(item, fallback_title, fallback_artist, fallback_album=""):
    if not isinstance(item, dict):
        return None
    lyrics = item.get("lyrics") if isinstance(item.get("lyrics"), dict) else {}
    synced = str(lyrics.get("synced") or item.get("synced") or "").strip()
    plain = str(lyrics.get("plain") or item.get("plain") or "").strip()
    title = item.get("track") or item.get("title") or fallback_title
    artist = item.get("artist") or fallback_artist
    album = item.get("album") or fallback_album
    duration = _safe_float(item.get("duration"))
    if synced and parse_synced_lyrics_compact(synced):
        return {
            "success": True,
            "status": "synced",
            "source": "synclrc",
            "synced_lyrics": synced,
            "plain_lyrics": plain,
            "matched_title": title,
            "matched_artist": artist,
            "matched_album": album,
            "matched_duration": duration,
        }
    if plain:
        return {
            "success": True,
            "status": "plain_only",
            "source": "synclrc",
            "synced_lyrics": "",
            "plain_lyrics": plain,
            "matched_title": title,
            "matched_artist": artist,
            "matched_album": album,
            "matched_duration": duration,
        }
    return None


def _fetch_lyrics_synclrc(title, artist, album="", duration=None, timeout=REQUEST_TIMEOUT,
                          extra_queries=None):
    """Use SyncLRC's public search and track endpoints as another fallback."""
    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    duration_value = _safe_float(duration)
    queries = [title]
    for q in extra_queries or []:
        q = str(q or "").strip()
        if q and normalize_text(q) not in {normalize_text(x) for x in queries}:
            queries.append(q)
    last_error = None
    candidates = []

    for query in queries:
        try:
            response = requests.get(
                SYNCLRC_SEARCH_URL,
                params={"q": query, "limit": 10, "offset": 0},
                headers=headers,
                timeout=timeout,
            )
            response.raise_for_status()
            data = response.json()
            items = data.get("results", []) if isinstance(data, dict) else data
            if isinstance(items, list):
                candidates.extend(items)
        except requests.RequestException as exc:
            last_error = exc
        except (ValueError, TypeError):
            continue

    # If search produced candidates, rank them by metadata before using them.
    wanted_title = normalize_text(title)
    wanted_artist = normalize_text(artist)
    wanted_album = normalize_text(album)

    def rank(item):
        item_title = normalize_text(item.get("track") or item.get("title"))
        item_artist = normalize_text(item.get("artist"))
        item_album = normalize_text(item.get("album"))
        item_duration = _safe_float(item.get("duration"))
        title_penalty = 0 if item_title == wanted_title else (1 if wanted_title and wanted_title in item_title else 3)
        artist_penalty = 0 if not wanted_artist or wanted_artist in {"unknown", "unknown artist", "n a"} else (0 if item_artist == wanted_artist else 2)
        album_penalty = 0 if not wanted_album else (0 if item_album == wanted_album else 1)
        duration_penalty = abs(item_duration - duration_value) if item_duration is not None and duration_value is not None else 999999.0
        lyrics = item.get("lyrics") if isinstance(item.get("lyrics"), dict) else {}
        synced_penalty = 0 if str(lyrics.get("synced") or item.get("synced") or "").strip() else 1
        return (title_penalty, artist_penalty, album_penalty, synced_penalty, duration_penalty)

    candidates.sort(key=rank)
    seen = set()
    for item in candidates:
        key = item.get("id") or (normalize_text(item.get("track") or item.get("title")), normalize_text(item.get("artist")))
        if key in seen:
            continue
        seen.add(key)

        # Search responses already include lyrics according to SyncLRC docs.
        result = _synclrc_item_to_result(item, title, artist, album)
        if result and result.get("success"):
            result["fallback"] = "synclrc_search"
            return result, None

        item_id = item.get("id")
        if item_id:
            try:
                response = requests.get(
                    f"{SYNCLRC_LYRICS_URL}/{item_id}",
                    params={"type": "synced"},
                    headers=headers,
                    timeout=timeout,
                )
                if response.ok:
                    data = response.json()
                    result = _synclrc_item_to_result(data, title, artist, album)
                    if result and result.get("success"):
                        result["fallback"] = "synclrc_id"
                        return result, None
            except requests.RequestException as exc:
                last_error = exc
            except (ValueError, TypeError):
                pass

    if not candidates and last_error is not None:
        return None, last_error
    return None, None

def _musicbrainz_resolve_recording(title, album="", duration=None, extra_queries=None,
                                    timeout=REQUEST_TIMEOUT):
    """Resolve missing artist metadata before the synced-lyrics search."""
    title = str(title or "").strip()
    album = str(album or "").strip()
    if not title:
        return None

    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    duration_value = _safe_float(duration)
    queries = [title]
    # If the filename supplied a useful second token such as "Barfi", turn it
    # into a release hint instead of searching for a literal track named
    # "Aashiyan Barfi".
    for q in extra_queries or []:
        q = str(q or "").strip()
        if q and normalize_text(q) not in {normalize_text(x) for x in queries}:
            queries.append(q)
    best = None
    last_error = None

    for query_text in queries[:6]:
        terms = [f'recording:"{query_text}"']
        # A phrase containing the title plus another filename token is useful
        # as a broad recording search; the exact title is still preferred.
        if album:
            terms.append(f'release:"{album}"')
        params = {"query": " AND ".join(terms), "fmt": "json", "limit": 15}
        try:
            response = requests.get(
                MUSICBRAINZ_SEARCH_URL,
                params=params,
                headers=headers,
                timeout=timeout,
            )
            response.raise_for_status()
            data = response.json()
            recordings = data.get("recordings", []) if isinstance(data, dict) else []
            if not isinstance(recordings, list):
                continue

            wanted_title = normalize_text(title)
            wanted_album = normalize_text(album)
            for item in recordings:
                if not isinstance(item, dict):
                    continue
                item_title = normalize_text(item.get("title"))
                if not item_title:
                    continue
                title_penalty = 0 if item_title == wanted_title else (1 if wanted_title in item_title else 6)

                releases = item.get("releases") or []
                release_names = [normalize_text(r.get("title")) for r in releases if isinstance(r, dict)]
                if wanted_album:
                    album_penalty = 0 if wanted_album in release_names else 3
                else:
                    album_penalty = 0

                length_ms = _safe_float(item.get("length"))
                duration_penalty = 999999.0
                if duration_value and length_ms:
                    duration_penalty = abs((length_ms / 1000.0) - duration_value)

                score = _safe_float(item.get("score")) or 0.0
                credits = item.get("artist-credit") or []
                artist_parts = []
                for credit in credits:
                    if not isinstance(credit, dict):
                        continue
                    artist_obj = credit.get("artist") or {}
                    artist_name = str(artist_obj.get("name") or "").strip()
                    if artist_name:
                        artist_parts.append(artist_name)
                    artist_parts.append(str(credit.get("joinphrase") or ""))
                artist_name = "".join(artist_parts).strip()
                if not artist_name:
                    continue

                release_name = album
                if wanted_album:
                    for release in releases:
                        if isinstance(release, dict) and normalize_text(release.get("title")) == wanted_album:
                            release_name = str(release.get("title") or album)
                            break
                elif releases and isinstance(releases[0], dict):
                    release_name = str(releases[0].get("title") or "")

                candidate = {
                    "title": str(item.get("title") or title),
                    "artist": artist_name,
                    "album": release_name,
                    "duration": (length_ms / 1000.0 if length_ms else duration_value),
                    "rank": (title_penalty, album_penalty, duration_penalty, -score),
                }
                if best is None or candidate["rank"] < best["rank"]:
                    best = candidate

            if best is not None and best["rank"][0] == 0 and best["rank"][1] == 0:
                break
        except requests.RequestException as exc:
            last_error = exc
        except (ValueError, TypeError):
            continue
        time.sleep(MUSICBRAINZ_REQUEST_GAP)

    return best


def _find_syncedlyrics_command():
    """Find the syncedlyrics command installed for this Python environment."""
    candidates = []

    found = shutil.which("syncedlyrics")
    if found:
        candidates.append(found)

    # On Windows pip normally places console scripts beside python.exe.
    python_dir = os.path.dirname(os.path.abspath(sys.executable))
    for name in ("syncedlyrics.exe", "syncedlyrics.cmd", "syncedlyrics"):
        path = os.path.join(python_dir, name)
        if os.path.isfile(path):
            candidates.append(path)

    seen = set()
    for candidate in candidates:
        key = os.path.normcase(os.path.abspath(candidate))
        if key not in seen:
            seen.add(key)
            return candidate
    return None


def _run_syncedlyrics_search(query, timeout=REQUEST_TIMEOUT):
    """Run syncedlyrics with --synced-only and return raw LRC text.

    The CLI flag is intentional.  We do not use the library's default search
    mode because that mode may return plaintext when synchronized lyrics are
    unavailable.  The result is accepted only if our own LRC parser can find
    timestamped lines too.
    """
    query = str(query or "").strip()
    if not query:
        return None, None

    command = _find_syncedlyrics_command()
    if not command:
        return None, "syncedlyrics is not installed"

    try:
        timeout_seconds = timeout[1] if isinstance(timeout, tuple) else timeout
        timeout_seconds = max(10, min(float(timeout_seconds), SYNCEDLYRICS_COMMAND_TIMEOUT))
        completed = subprocess.run(
            [command, "--synced-only", query],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_seconds,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            check=False,
        )
    except FileNotFoundError:
        return None, "syncedlyrics command was not found"
    except subprocess.TimeoutExpired:
        return None, f"syncedlyrics timed out after {timeout_seconds:g}s"
    except OSError as exc:
        return None, str(exc)

    output = (completed.stdout or "").strip()
    if output and parse_synced_lyrics_compact(output):
        return output, None

    stderr = (completed.stderr or "").strip()
    if completed.returncode != 0 and stderr:
        return None, stderr[-1000:]

    # A zero exit code with no timestamped LRC simply means this provider
    # search did not find synchronized lyrics.
    return None, None



# ---------------------------------------------------------------------------
# MUSIXMATCH RICHSYNC (TRUE WORD-LEVEL TIMING)
# ---------------------------------------------------------------------------

_MUSIXMATCH_API_URL = "https://apic-desktop.musixmatch.com/ws/1.1/"
_MUSIXMATCH_TOKEN = None
_MUSIXMATCH_TOKEN_TIME = 0.0
_MUSIXMATCH_TOKEN_LOCK = threading.Lock()
_MUSIXMATCH_TOKEN_MAX_AGE = 20 * 60


def _musixmatch_request(session, method, params, timeout, usertoken=None):
    request_params = {
        "app_id": "web-desktop-app-v1.0",
        "format": "json",
    }
    if usertoken:
        request_params["usertoken"] = usertoken
    request_params.update(params or {})
    response = session.get(
        _MUSIXMATCH_API_URL + method,
        params=request_params,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/153.0.0.0 Safari/537.36"
            ),
            "Accept": "application/json",
            "Cookie": "AWSELB=0; AWSELBCORS=0; x-mxm-token-guid=",
        },
        timeout=timeout,
    )
    response.raise_for_status()
    data = response.json()
    message = data.get("message") if isinstance(data, dict) else None
    header = message.get("header") if isinstance(message, dict) else None
    status_code = header.get("status_code") if isinstance(header, dict) else None
    if status_code == 401:
        raise PermissionError(str(header.get("hint") or "Musixmatch token rejected"))
    if status_code != 200:
        raise RuntimeError(str(header.get("hint") or f"Musixmatch status {status_code}"))
    return message.get("body") if isinstance(message, dict) else None


def _musixmatch_get_token(session, timeout, force=False):
    global _MUSIXMATCH_TOKEN, _MUSIXMATCH_TOKEN_TIME
    with _MUSIXMATCH_TOKEN_LOCK:
        if (
            not force
            and _MUSIXMATCH_TOKEN
            and (time.time() - _MUSIXMATCH_TOKEN_TIME) < _MUSIXMATCH_TOKEN_MAX_AGE
        ):
            return _MUSIXMATCH_TOKEN

        response = session.get(
            _MUSIXMATCH_API_URL + "token.get",
            params={
                "user_language": "en",
                "app_id": "web-desktop-app-v1.0",
            },
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/153.0.0.0 Safari/537.36"
                ),
                "Accept": "application/json",
            },
            timeout=timeout,
        )
        response.raise_for_status()
        data = response.json()
        message = data.get("message") if isinstance(data, dict) else None
        header = message.get("header") if isinstance(message, dict) else None
        if not isinstance(header, dict) or header.get("status_code") != 200:
            hint = header.get("hint") if isinstance(header, dict) else "unknown error"
            raise RuntimeError(f"Musixmatch token: {hint}")
        body = message.get("body") if isinstance(message, dict) else {}
        token = str((body or {}).get("user_token") or "").strip()
        if not token or token.startswith("UpgradeOnly"):
            raise RuntimeError("Musixmatch returned no usable anonymous token")
        _MUSIXMATCH_TOKEN = token
        _MUSIXMATCH_TOKEN_TIME = time.time()
        return token


def _musixmatch_richsync_to_lrc(richsync_body):
    """Convert Musixmatch richsync JSON to Enhanced LRC without inventing timing."""
    if isinstance(richsync_body, str):
        try:
            richsync_body = json.loads(richsync_body)
        except (TypeError, ValueError):
            return ""
    if not isinstance(richsync_body, list):
        return ""

    output = []
    for line in richsync_body:
        if not isinstance(line, dict):
            continue
        try:
            line_start = float(line.get("ts"))
        except (TypeError, ValueError):
            continue
        words = line.get("l")
        if not isinstance(words, list):
            continue

        parts = []
        for item in words:
            if not isinstance(item, dict):
                continue
            text = str(item.get("c") or "")
            if not text:
                continue
            try:
                offset = float(item.get("o"))
            except (TypeError, ValueError):
                continue
            absolute = line_start + offset
            parts.append(f"<{_format_lrc_time(absolute)}>{text}")

        if parts:
            output.append(f"[{_format_lrc_time(line_start)}]" + "".join(parts))

    return "\n".join(output)


def _format_lrc_time(seconds):
    seconds = max(0.0, float(seconds))
    minutes = int(seconds // 60)
    remainder = seconds - (minutes * 60)
    return f"{minutes:02d}:{remainder:05.2f}"


def _extract_musixmatch_richsync(body):
    """Extract richsync JSON from macro.subtitles.get response."""
    if not isinstance(body, dict):
        return ""
    macro = body.get("macro_calls") if isinstance(body.get("macro_calls"), dict) else body
    call = macro.get("track.richsync.get") if isinstance(macro, dict) else None
    if not isinstance(call, dict):
        return ""
    message = call.get("message") or {}
    body_data = message.get("body") or {}
    richsync = body_data.get("richsync") if isinstance(body_data, dict) else None
    if not isinstance(richsync, dict):
        return ""
    return str(richsync.get("richsync_body") or "")


def _extract_musixmatch_matched_track(body):
    """Extract the recording metadata returned by Musixmatch's matcher."""
    if not isinstance(body, dict):
        return None
    macro = body.get("macro_calls") if isinstance(body.get("macro_calls"), dict) else {}
    matcher = macro.get("matcher.track.get") if isinstance(macro, dict) else None
    matcher_body = (matcher.get("message") or {}).get("body") if isinstance(matcher, dict) else None
    track = (matcher_body or {}).get("track") if isinstance(matcher_body, dict) else None
    if not isinstance(track, dict):
        # Some response shapes expose the matched track directly.
        direct = body.get("track")
        if isinstance(direct, dict):
            track = direct
    if not isinstance(track, dict):
        return None

    return {
        "matched_title": track.get("track_name") or track.get("trackName") or track.get("name"),
        "matched_artist": track.get("artist_name") or track.get("artistName"),
        "matched_album": track.get("album_name") or track.get("albumName"),
        "matched_duration": _safe_float(
            track.get("track_length") or track.get("duration")
        ),
        "matched_track_id": track.get("track_id"),
        "matched_commontrack_id": track.get("commontrack_id"),
    }


def _youtube_vtt_to_lrc(vtt_text):
    """Convert YouTube WebVTT captions into ordinary line-timed LRC."""
    if not vtt_text:
        return ""

    timestamp_re = re.compile(
        r"(?m)^(\d{2}:\d{2}(?::\d{2})?\.\d{3})\s+-->\s+(\d{2}:\d{2}(?::\d{2})?\.\d{3}).*$"
    )

    def vtt_time_to_seconds(value):
        parts = value.replace(',', '.').split(':')
        try:
            if len(parts) == 3:
                hours, minutes, seconds = parts
                return float(hours) * 3600 + float(minutes) * 60 + float(seconds)
            minutes, seconds = parts
            return float(minutes) * 60 + float(seconds)
        except (ValueError, TypeError):
            return None

    lines = vtt_text.replace('\r\n', '\n').replace('\r', '\n').split('\n')
    entries = []
    i = 0
    while i < len(lines):
        match = timestamp_re.match(lines[i].strip())
        if not match:
            i += 1
            continue
        start = vtt_time_to_seconds(match.group(1))
        i += 1
        text_lines = []
        while i < len(lines) and lines[i].strip():
            line = re.sub(r"<[^>]+>", "", lines[i]).strip()
            if line and not line.startswith(('NOTE', 'STYLE', 'REGION')):
                text_lines.append(line)
            i += 1
        text = re.sub(r"\s+", " ", " ".join(text_lines)).strip()
        text = re.sub(r"\[?Music\]?", "", text, flags=re.IGNORECASE).strip()
        if start is not None and text:
            entries.append((start, text))
        i += 1

    if not entries:
        return ""

    # YouTube captions frequently repeat the same cumulative caption over
    # several adjacent cues. Keep the first occurrence of identical text.
    compact = []
    last_text = None
    for start, text in entries:
        if text == last_text:
            continue
        compact.append((start, text))
        last_text = text

    return "\n".join(
        f"[{int(start // 60):02d}:{start % 60:05.2f}] {text}"
        for start, text in compact
    )


def _fetch_lyrics_youtube_captions(title, artist="", album="", duration=None,
                                   timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Use YouTube video captions as a last-resort timed-lyrics source.

    This is intentionally below YouTube Music and the dedicated lyrics APIs.
    It uses yt-dlp only for searching a likely official/lyrics upload and
    retrieving its captions; it never downloads the media itself.
    """
    try:
        import yt_dlp
    except Exception as exc:
        return None, f"yt-dlp is not installed: {exc}"

    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title:
        return None, None

    queries = []
    if artist and artist.casefold() not in {"unknown artist", "unknown", "n/a", "none"}:
        queries.extend([
            f"{artist} {title} lyrics",
            f"{artist} {title} official",
            f"{artist} {title}",
        ])
    else:
        queries.append(f"{title} lyrics")
    for query in extra_queries or []:
        if query:
            queries.append(str(query).strip())

    seen = set()
    queries = [q for q in queries if q and not (normalize_text(q) in seen or seen.add(normalize_text(q)))]

    requested_duration = _safe_float(duration)
    candidates = []
    errors = []

    search_opts = {
        "quiet": True,
        "skip_download": True,
        "extract_flat": True,
        "noplaylist": True,
        "socket_timeout": timeout[1] if isinstance(timeout, tuple) else timeout,
    }

    try:
        with yt_dlp.YoutubeDL(search_opts) as ydl:
            for query in queries[:4]:
                try:
                    info = ydl.extract_info(f"ytsearch5:{query}", download=False)
                except Exception as exc:
                    errors.append(f"search {query}: {exc}")
                    continue
                entries = (info or {}).get("entries") or []
                for item in entries:
                    if not isinstance(item, dict):
                        continue
                    video_id = item.get("id")
                    if not video_id:
                        continue
                    candidate_title = str(item.get("title") or "").strip()
                    uploader = str(item.get("uploader") or item.get("channel") or "").strip()
                    candidate_duration = _safe_float(item.get("duration"))
                    haystack = normalize_text(f"{candidate_title} {uploader}")
                    title_key = normalize_text(title)
                    artist_key = normalize_text(artist)
                    if title_key and title_key not in haystack:
                        continue
                    if artist_key and artist_key not in {"unknown artist", "unknown", "n/a", "none"}:
                        # Artist text may be absent from the video title, so
                        # accept the candidate when the search itself was
                        # artist-qualified. Duration and title still matter.
                        artist_hint_ok = artist_key in haystack or normalize_text(query).find(artist_key) >= 0
                        if not artist_hint_ok:
                            continue
                    result = {
                        "success": False,
                        "status": "not_found",
                        "source": "youtube_captions",
                        "matched_title": candidate_title,
                        "matched_artist": uploader or artist,
                        "matched_album": album,
                        "duration": candidate_duration,
                        "video_id": video_id,
                        "synced_lyrics": "",
                        "plain_lyrics": "",
                    }
                    ok, reason, score = _provider_result_matches_request(
                        result, title, artist, album, requested_duration,
                        strict_duration=False,
                    )
                    if ok:
                        result["match_score"] = score
                        candidates.append(result)
    except Exception as exc:
        return None, f"yt-dlp search failed: {exc}"

    # Prefer duration-compatible results and likely lyrics/official uploads.
    def candidate_score(item):
        score = float(item.get("match_score") or 0.0)
        text = normalize_text(item.get("matched_title") or "")
        if "lyrics" in text:
            score += 4.0
        if "official" in text:
            score += 2.0
        return score

    candidates.sort(key=candidate_score, reverse=True)
    seen_ids = set()

    caption_opts = {
        "quiet": True,
        "skip_download": True,
        "writesubtitles": True,
        "writeautomaticsub": True,
        "subtitleslangs": ["en", "en.*"],
        "subtitlesformat": "vtt/best",
        "noplaylist": True,
        "socket_timeout": timeout[1] if isinstance(timeout, tuple) else timeout,
    }

    for candidate in candidates[:6]:
        video_id = candidate.get("video_id")
        if not video_id or video_id in seen_ids:
            continue
        seen_ids.add(video_id)
        try:
            with yt_dlp.YoutubeDL(caption_opts) as ydl:
                info = ydl.extract_info(
                    f"https://www.youtube.com/watch?v={video_id}", download=False
                )
            subtitles = (info or {}).get("subtitles") or {}
            automatic = (info or {}).get("automatic_captions") or {}
            tracks = subtitles.get("en") or automatic.get("en") or []
            if not tracks:
                # Pick the first English-like track if YouTube used a locale
                # such as en-US or en-GB.
                for key, value in {**subtitles, **automatic}.items():
                    if str(key).lower().startswith("en") and value:
                        tracks = value
                        break
            if not tracks:
                continue

            vtt_url = None
            for track in tracks:
                if not isinstance(track, dict):
                    continue
                if str(track.get("ext") or "").lower() == "vtt":
                    vtt_url = track.get("url")
                    break
                vtt_url = vtt_url or track.get("url")
            if not vtt_url:
                continue

            response = requests.get(
                vtt_url,
                headers={"User-Agent": LYRICS_USER_AGENT},
                timeout=timeout,
            )
            response.raise_for_status()
            lrc = _youtube_vtt_to_lrc(response.text)
            if not lrc or not parse_synced_lyrics_compact(lrc):
                continue

            result = _lrc_text_to_result(
                lrc, title, artist, album, source="youtube_captions"
            )
            if not result:
                continue
            result.update({
                "matched_title": candidate.get("matched_title") or title,
                "matched_artist": artist or candidate.get("matched_artist") or "",
                "matched_album": candidate.get("matched_album") or album,
                "duration": candidate.get("duration"),
                "video_id": video_id,
                "fallback": "youtube_captions",
                "caption_type": "manual" if subtitles.get("en") else "automatic",
            })
            ok, reason, _ = _provider_result_matches_request(
                result, title, artist, album, requested_duration,
                strict_duration=False,
            )
            if ok:
                print(
                    "Lyrics FOUND: YouTube captions — "
                    f"{result.get('matched_title')} / {result.get('matched_artist')}"
                )
                return result, None
            print(f"YouTube captions rejected after lyrics fetch: {reason}")
        except Exception as exc:
            errors.append(f"video {video_id}: {exc}")

    if errors:
        return None, " | ".join(errors)[-5000:]
    return None, None


def _fetch_lyrics_musixmatch_word_sync(title, artist="", album="", duration=None,
                                       timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Fetch genuine Musixmatch richsync word timing.

    This is intentionally separate from syncedlyrics.  syncedlyrics can return
    ordinary LRC even when enhanced lyrics were requested; this function only
    returns a result after explicit Musixmatch richsync word timestamps exist.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title:
        return None, None

    timeout_seconds = timeout[1] if isinstance(timeout, tuple) else timeout
    session = requests.Session()
    duration_value = _safe_float(duration)
    unknown_artist = artist.casefold() in {"", "unknown artist", "unknown", "n/a", "none"}

    lookup_pairs = []
    if not unknown_artist:
        lookup_pairs.append((title, artist))
        if album:
            lookup_pairs.append((title, artist))

    # Filename-derived performer queries can be passed as extra_queries.
    # Convert "Aashiyan Shreya Nikhil Paul George" into track=Aashiyan,
    # artist=Shreya Nikhil Paul George for the Musixmatch matcher.
    for query in extra_queries or []:
        query = str(query or "").strip()
        if not query:
            continue
        if unknown_artist and normalize_text(query).startswith(normalize_text(title)):
            remainder = query[len(title):].strip(" -_")
            if remainder:
                lookup_pairs.append((title, remainder))
        else:
            lookup_pairs.append((query, artist))

    if not lookup_pairs:
        print("Musixmatch word-sync skipped: no reliable artist/performer metadata")
        return None, None

    seen = set()
    deduped = []
    for track_name, artist_name in lookup_pairs:
        key = (normalize_text(track_name), normalize_text(artist_name))
        if key not in seen:
            seen.add(key)
            deduped.append((track_name, artist_name))

    try:
        token = _musixmatch_get_token(session, timeout_seconds)
    except Exception as exc:
        return None, f"Musixmatch token: {exc}"

    last_error = None
    # Different filename/metadata queries can resolve to the exact same
    # Musixmatch track. Once we have requested RichSync for a track ID, do not
    # request it again during this lookup.
    attempted_richsync_keys = set()
    for track_name, artist_name in deduped[:8]:
        params = {
            "namespace": "lyrics_richsynched",
            "subtitle_format": "mxm",
            "optional_calls": "track.richsync",
            "q_track": track_name,
            "q_artist": artist_name,
            "q_artists": artist_name,
        }
        if album:
            params["q_album"] = album
        if duration_value and duration_value > 0:
            params["q_duration"] = duration_value
            params["f_subtitle_length"] = int(duration_value)

        try:
            body = _musixmatch_request(
                session, "macro.subtitles.get", params, timeout_seconds, token
            )
        except PermissionError:
            try:
                token = _musixmatch_get_token(session, timeout_seconds, force=True)
                body = _musixmatch_request(
                    session, "macro.subtitles.get", params, timeout_seconds, token
                )
            except Exception as exc:
                last_error = exc
                continue
        except Exception as exc:
            last_error = exc
            continue

        matched_track = _extract_musixmatch_matched_track(body)
        if not matched_track:
            print("Musixmatch rejected: response did not expose matched track metadata")
            continue

        ok, reason, match_score = _validate_matched_metadata(
            track_name, artist_name, album, duration,
            matched_track.get("matched_title"),
            matched_track.get("matched_artist"),
            matched_track.get("matched_album"),
            matched_track.get("matched_duration"),
            strict_duration=False,
        )
        if not ok:
            print(f"Musixmatch track REJECTED: {reason}")
            continue

        print(
            "Musixmatch matched: "
            f"{matched_track.get('matched_title') or '?'} / "
            f"{matched_track.get('matched_artist') or '?'} / "
            f"{matched_track.get('matched_duration') or '?'}s"
        )

        richsync_raw = _extract_musixmatch_richsync(body)

        # Some responses do not include the optional call despite requesting it.
        # In that case use the matched commontrack_id and make the dedicated
        # richsync request.
        if not richsync_raw:
            try:
                macro = body.get("macro_calls", {}) if isinstance(body, dict) else {}
                matcher = macro.get("matcher.track.get", {}) if isinstance(macro, dict) else {}
                matcher_body = (matcher.get("message") or {}).get("body") or {}
                track = matcher_body.get("track") or {}
                commontrack_id = track.get("commontrack_id")
                track_id = track.get("track_id")
                track_length = track.get("track_length") or duration_value or 0
                if commontrack_id or track_id:
                    richsync_key = (str(track_id or ""), str(commontrack_id or ""))
                    if richsync_key in attempted_richsync_keys:
                        continue
                    attempted_richsync_keys.add(richsync_key)

                    rich_params = {
                        "subtitle_format": "mxm",
                        "q_duration": track_length,
                        "f_richsync_length": track_length,
                        "f_richsync_length_max_deviation": 1,
                    }
                    if commontrack_id:
                        rich_params["commontrack_id"] = commontrack_id
                    if track_id:
                        rich_params["track_id"] = track_id
                    print(f"Musixmatch richsync request: track_id={track_id or '-'} commontrack_id={commontrack_id or '-'}")
                    rich_body = _musixmatch_request(session, "track.richsync.get", rich_params, timeout_seconds, token)
                    richsync = rich_body.get("richsync") if isinstance(rich_body, dict) else None
                    if isinstance(richsync, dict):
                        richsync_raw = str(richsync.get("richsync_body") or "")
                        print(f"Musixmatch richsync response: payload={'yes' if richsync_raw else 'no'}")
            except Exception as exc:
                last_error = exc

        enhanced = _musixmatch_richsync_to_lrc(richsync_raw)
        if enhanced:
            word_count = sum(len(re.findall(r"<\d{2}:\d{2}\.\d{2}>", line)) for line in enhanced.splitlines())
            print(f"Musixmatch richsync parsed: {word_count} word timestamps")
        else:
            print("Musixmatch richsync parsed: 0 word timestamps")
        if enhanced and _has_true_word_sync(enhanced):
            print(f"Musixmatch WORD SYNC FOUND: {track_name} / {artist_name or '(artist unknown)'}")
            result = _lrc_text_to_result(
                enhanced, title, artist, album, source="musixmatch_richsync"
            )
            if result:
                result["has_word_sync"] = True
                result["matched_query"] = f"{track_name} {artist_name}".strip()
                result["matched_title"] = matched_track.get("matched_title") or title
                result["matched_artist"] = matched_track.get("matched_artist") or artist
                result["matched_album"] = matched_track.get("matched_album") or album
                result["matched_duration"] = matched_track.get("matched_duration")
                result["matched_track_id"] = matched_track.get("matched_track_id")
                result["matched_commontrack_id"] = matched_track.get("matched_commontrack_id")
                result["match_score"] = match_score
                result["fallback"] = "musixmatch_richsync"
                return result, None

    return None, last_error


def _fetch_lyrics_syncedlyrics(title, artist="", album="", duration=None,
                               timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Search syncedlyrics directly, then fall back to its --synced-only CLI.

    The direct Python API avoids Windows console-script/PATH problems.  We
    still reject plaintext results ourselves: only LRC text containing real
    timestamps is accepted.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()
    if not title:
        return None, None

    queries = []
    known_artist = bool(artist) and artist.casefold() not in {"unknown artist", "unknown", "n/a", "none"}

    if known_artist:
        queries.append(f"{title} {artist}")
        if album:
            queries.append(f"{title} {artist} {album}")

    # When the detector only knows a filename, filename-derived performer
    # queries are much more trustworthy than a bare title.  Put those first
    # so a generic title cannot accidentally match a different recording.
    # For example, Aashiyan_..._Shreya_Nikhil_Paul_George gives us:
    #   Aashiyan Shreya Nikhil Paul George
    # which is a much stronger lookup than simply "Aashiyan".
    extras = []
    for extra in extra_queries or []:
        extra = str(extra or "").strip()
        if extra:
            extras.append(extra)
            if known_artist:
                extras.append(f"{extra} {artist}")

    if not known_artist:
        queries.extend(extras)

    queries.append(title)
    if album:
        queries.append(f"{title} {album}")

    if known_artist:
        queries.extend(extras)

    unique_queries = []
    seen = set()
    for query in queries:
        key = normalize_text(query)
        if key and key not in seen:
            seen.add(key)
            unique_queries.append(query)
    unique_queries = unique_queries[:SYNCEDLYRICS_MAX_QUERIES]

    errors = []
    try:
        import syncedlyrics as syncedlyrics_module
    except Exception as exc:
        syncedlyrics_module = None
        errors.append(f"Python API import: {exc}")

    print("\nLyrics syncedlyrics queries:")
    for query in unique_queries:
        print(f"  -> {query}")

    for query in unique_queries:
        # Preferred path: direct library call.  syncedlyrics' documented
        # Python API returns an LRC string; if it returns plain text, our LRC
        # parser rejects it, which gives us the same effective behavior as
        # --synced-only without depending on a Windows console executable.
        if syncedlyrics_module is not None:
            try:
                # IMPORTANT: explicitly request synchronized lyrics.
                # The direct test that works for Aashiyan uses this exact
                # mode, so do not rely on syncedlyrics' default behavior.
                lrc = syncedlyrics_module.search(
                    query,
                    enhanced=True,
                    providers=["musixmatch", "lrclib", "netease"],
                    synced_only=True,
                )
                if lrc and parse_synced_lyrics_compact(lrc):
                    print(f"Lyrics syncedlyrics FOUND: {query}")
                    result = _lrc_text_to_result(lrc, title, artist, album, source="syncedlyrics")
                    if result:
                        result["fallback"] = "syncedlyrics_python"
                        result["matched_query"] = query
                        return result, None
            except Exception as exc:
                print(f"Lyrics syncedlyrics ERROR: {query} -> {exc}")
                errors.append(f"{query} (Python API): {exc}")

        # Secondary path: exact CLI mode requested by the user.
        lrc, error = _run_syncedlyrics_search(query, timeout=timeout)
        if lrc:
            result = _lrc_text_to_result(lrc, title, artist, album, source="syncedlyrics")
            if result:
                result["fallback"] = "syncedlyrics_cli_synced_only"
                result["matched_query"] = query
                return result, None
        if error:
            print(f"Lyrics syncedlyrics CLI ERROR: {query} -> {error}")
            errors.append(f"{query} (CLI): {error}")

    if errors:
        print("Lyrics syncedlyrics exhausted all queries with errors.")
        return None, " | ".join(errors)[-5000:]
    return None, None


def _lrcmux_word_lrc_from_response(data):
    """Convert Lrcmux word-level JSON into enhanced LRC without estimating timing."""
    if not isinstance(data, dict):
        return ""
    meta = data.get("meta") or {}
    if str(meta.get("level") or "").casefold() != "word":
        return ""
    lines = data.get("lines")
    if not isinstance(lines, list):
        return ""

    output = []
    for line in lines:
        if not isinstance(line, dict):
            continue
        start = line.get("start")
        words = line.get("words")
        if start is None or not isinstance(words, list) or not words:
            continue
        try:
            line_start = float(start) / 1000.0
        except (TypeError, ValueError):
            continue

        parts = []
        valid_words = 0
        for word in words:
            if not isinstance(word, dict):
                continue
            text = str(word.get("text") or "")
            word_start = word.get("start")
            if not text or word_start is None:
                continue
            try:
                absolute = float(word_start) / 1000.0
            except (TypeError, ValueError):
                continue
            parts.append(f"<{_format_lrc_time(absolute)}>{text}")
            valid_words += 1

        if valid_words:
            output.append(f"[{_format_lrc_time(line_start)}]" + "".join(parts))

    return "\n".join(output)


def _fetch_lyrics_lrcmux_word_sync(title, artist="", album="", duration=None,
                                   timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Fetch genuine word-level timing from Lrcmux.

    Lrcmux explicitly reports meta.level='word' and returns per-word start/end
    values. We reject line-level responses and never infer missing word times.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()

    unknown_artists = {"", "unknown artist", "unknown", "n/a", "none"}
    candidates = []

    if title and artist.casefold() not in unknown_artists:
        candidates.append((title, artist))

    # When the detector has no artist, reuse the filename-derived search phrases
    # already produced by get_lyrics_for_audio().  These are search candidates,
    # not guessed metadata.  A query such as:
    #   Aashiyan Shreya Nikhil Paul George
    # becomes title="Aashiyan", artist="Shreya Nikhil Paul George".
    # We only do this for multi-word queries and never fall back to a bare title.
    seen = {(t.casefold(), a.casefold()) for t, a in candidates}
    if artist.casefold() in unknown_artists:
        for query in extra_queries or []:
            parts = str(query or "").strip().split()
            if len(parts) < 3:
                continue
            candidate_title = parts[0].strip()
            candidate_artist = " ".join(parts[1:]).strip()
            if not candidate_title or not candidate_artist:
                continue
            key = (candidate_title.casefold(), candidate_artist.casefold())
            if key not in seen:
                candidates.append((candidate_title, candidate_artist))
                seen.add(key)

    if not candidates:
        print("Lrcmux word-sync skipped: no reliable title/artist search pair")
        return None, None

    duration_value = _safe_float(duration)
    headers = {"User-Agent": LYRICS_USER_AGENT, "Accept": "application/json"}
    last_error = None

    for candidate_title, candidate_artist in candidates:
        params = {
            "artist": candidate_artist,
            "title": candidate_title,
            "album": album,
            "duration": int(round(duration_value)) if duration_value and duration_value > 0 else 0,
            "timestamps": "true",
            "word": "true",
        }
        try:
            print(f"Lrcmux word-sync request: {candidate_title} / {candidate_artist}")
            response = requests.get(
                LRCMUX_GET_URL, params=params, headers=headers, timeout=timeout
            )
            print(f"Lrcmux response: HTTP {response.status_code}")
            if response.status_code == 404:
                continue
            response.raise_for_status()
            data = response.json()
            meta = data.get("meta") if isinstance(data, dict) else {}
            level = str((meta or {}).get("level") or "").strip().lower()
            print(f"Lrcmux sync level: {level or 'none'}")

            # Strict rule: Lrcmux must explicitly say level="word".
            if level != "word":
                print("Lrcmux rejected: response is not word-level sync")
                continue

            enhanced = _lrcmux_word_lrc_from_response(data)
            if not enhanced or not _has_true_word_sync(enhanced):
                print("Lrcmux parsed: 0 usable word timestamps")
                continue

            word_count = sum(
                len(re.findall(r"<\d{2}:\d{2}\.\d{2}>", line))
                for line in enhanced.splitlines()
            )
            print(f"Lrcmux parsed: {word_count} word timestamps")
            result = _lrc_text_to_result(
                enhanced, candidate_title, candidate_artist, album,
                source="lrcmux_word_sync"
            )
            if result:
                result["has_word_sync"] = True
                result["fallback"] = "lrcmux_word_sync"
                return result, None
        except requests.RequestException as exc:
            print(f"Lrcmux ERROR: {exc}")
            last_error = str(exc)
            continue
        except (ValueError, TypeError) as exc:
            print(f"Lrcmux invalid response: {exc}")
            last_error = str(exc)
            continue

    return None, last_error


LYRICS_SELECTION_VERSION = "v1"


def _classify_lyrics_timing(result):
    """Classify only timing that is genuinely present in provider data."""
    if not isinstance(result, dict):
        return "plain"

    synced = str(result.get("synced_lyrics") or "").strip()
    if not synced:
        return "plain"

    # Enhanced LRC contains real per-word timestamps.  Do not create these
    # timestamps from ordinary line-synced LRC.
    try:
        enhanced = parse_enhanced_lyrics(synced)
        if enhanced and any(item.get("words") for item in enhanced):
            return "word"
    except Exception:
        pass

    try:
        if parse_synced_lyrics_compact(synced):
            return "line"
    except Exception:
        pass
    return "plain"


def _normalize_lyrics_candidate(result, source, title, artist, album, duration,
                                strict_duration=False, provider_priority=0):
    """Convert a provider result into the one internal selection format."""
    if not isinstance(result, dict) or not result.get("success"):
        return None

    ok, reason, match_score = _provider_result_matches_request(
        result, title, artist, album, duration,
        strict_duration=strict_duration,
    )
    if not ok:
        print(f"{source} candidate rejected: {reason}")
        return None

    synced = str(result.get("synced_lyrics") or "").strip()
    plain = str(result.get("plain_lyrics") or "").strip()
    if not synced and not plain:
        return None

    normalized = dict(result)
    normalized["source"] = normalized.get("source") or source
    normalized["timing_type"] = _classify_lyrics_timing(normalized)
    normalized["match_score"] = float(match_score)
    normalized["provider_priority"] = int(provider_priority)
    normalized["selection_version"] = LYRICS_SELECTION_VERSION
    normalized["normalized"] = True
    return normalized


def _lyrics_completeness_score(result):
    """Return a deterministic completeness score for tie-breaking."""
    synced = str(result.get("synced_lyrics") or "").strip()
    plain = str(result.get("plain_lyrics") or "").strip()
    if synced:
        parsed = parse_synced_lyrics_compact(synced)
        return (len(parsed), sum(bool(text.strip()) for _, text in parsed), len(synced))
    lines = [line for line in plain.splitlines() if line.strip()]
    return (len(lines), len(lines), len(plain))


def _select_best_lyrics_candidate(candidates):
    """Select lyrics using timing priority before all other quality factors.

    Fixed order:
        1. genuine line synchronization
        2. genuine word synchronization
        3. plain lyrics

    Match quality, completeness, and provider priority only break ties inside
    the same timing class. Provider order therefore cannot dictate the UI.
    """
    timing_priority = {"line": 3, "word": 2, "plain": 1}
    valid = [c for c in (candidates or []) if isinstance(c, dict)]
    if not valid:
        return None

    def key(candidate):
        complete = _lyrics_completeness_score(candidate)
        return (
            timing_priority.get(candidate.get("timing_type"), 0),
            -float(candidate.get("match_score", 999999.0)),
            complete[0],
            complete[1],
            complete[2],
            int(candidate.get("provider_priority", 0)),
        )

    return max(valid, key=key)


def fetch_lyrics(title, artist, album="", duration=None, timeout=REQUEST_TIMEOUT, extra_queries=None):
    """Fetch all enabled verified providers, then select one normalized result.

    Genuine line synchronization is Priority 1. Genuine word synchronization
    is Priority 2. Plain lyrics are Priority 3. No word timing is fabricated.
    """
    title = str(title or "").strip()
    artist = str(artist or "").strip()
    album = str(album or "").strip()

    if not title:
        return {"success": False, "status": "missing_metadata", "source": "",
                "synced_lyrics": "", "plain_lyrics": ""}

    print("\\nLyrics lookup: collecting verified provider candidates")
    candidates = []
    errors = []
    priorities = {
        "lrclib_exact": 100, "lrclib_search": 95, "youtube_music": 90,
        "youtube_captions": 50, "musixmatch_word_sync": 85,
        "lrcmux_word_sync": 80, "karalyr": 70, "lrcapi": 65,
        "synclrc": 60,
    }

    def add(result, source, strict_duration=False):
        if not result or not result.get("success"):
            return
        item = _normalize_lyrics_candidate(
            result, source, title, artist, album, duration,
            strict_duration=strict_duration,
            provider_priority=priorities.get(source, 0),
        )
        if item:
            candidates.append(item)
            print(f"Lyrics candidate accepted: {source} ({item['timing_type']})")

    exact, err = _fetch_lyrics_lrclib_exact(title, artist, album, duration, timeout=timeout)
    if exact:
        add(exact, "lrclib_exact", strict_duration=True)
    if err: errors.append(f"LRCLIB exact: {err}")

    try:
        matches = _search_lrclib(title, artist, album, duration, timeout=timeout,
                                 extra_queries=extra_queries)
        for item in matches or []:
            result = _lrclib_result_from_data(item, title, artist, album)
            if result:
                result["matched_id"] = item.get("id")
                result["instrumental"] = bool(item.get("instrumental"))
                add(result, "lrclib_search")
        if matches is None: errors.append("LRCLIB search returned no usable response")
    except Exception as exc:
        errors.append(f"LRCLIB search: {exc}")

    providers = [
        ("youtube_music", _fetch_lyrics_youtube_music),
        ("youtube_captions", _fetch_lyrics_youtube_captions),
        ("musixmatch_word_sync", _fetch_lyrics_musixmatch_word_sync),
        ("lrcmux_word_sync", _fetch_lyrics_lrcmux_word_sync),
        ("karalyr", _fetch_lyrics_karalyr),
        ("lrcapi", _fetch_lyrics_lrcapi),
        ("synclrc", _fetch_lyrics_synclrc),
    ]
    for source, provider in providers:
        try:
            result, err = provider(title, artist, album, duration, timeout=timeout,
                                   extra_queries=extra_queries)
            if result:
                add(result, source)
            if err: errors.append(f"{source}: {err}")
        except Exception as exc:
            errors.append(f"{source}: {exc}")

    selected = _select_best_lyrics_candidate(candidates)
    if selected:
        print(
            "Lyrics SELECTED: " + str(selected.get("source")) +
            " — " + str(selected.get("timing_type")) +
            " (line sync > word sync > plain)"
        )
        return selected

    return {
        "success": False, "status": "not_found", "source": "verified_lyrics_providers",
        "synced_lyrics": "", "plain_lyrics": "",
        "error": ("No verified lyrics match was found. " + " | ".join(errors)[-5000:])
                 if errors else "No verified lyrics match was found.",
    }


def load_cached_lyrics(title, artist, album="", duration=None, db_path=None,
                       max_age=CACHE_MAX_AGE):
    """Load a cached result. Returns None when no usable cache entry exists."""
    key = make_cache_key(title, artist, album, duration)

    try:
        with _open_database(db_path) as connection:
            row = connection.execute(
                """
                SELECT fingerprint_key, title, artist, album, duration,
                       synced_lyrics, plain_lyrics, source, status, updated_at
                FROM visualizer_song_lyrics
                WHERE fingerprint_key = ?
                """,
                (key,),
            ).fetchone()
    except sqlite3.Error:
        return None

    if row is None:
        return None

    # Never treat transient network/transport failures as a real lyric cache
    # result. A genuine "not_found" result IS cached, however: once all lyric
    # providers have been checked and the engine confirms that no lyrics exist,
    # remember that fact so the same song does not trigger another lookup every
    # time Lyrics is opened.
    if row[8] in ("network_error", "invalid_response", "word_sync_not_found"):
        return None

    updated_at = float(row[9] or 0.0)
    if max_age is not None and max_age >= 0:
        if time.time() - updated_at > max_age:
            return None

    cached_result = {
        "success": row[8] in ("synced", "plain_only"),
        "status": row[8],
        "source": row[7],
        "title": row[1],
        "artist": row[2],
        "album": row[3],
        "duration": row[4],
        "synced_lyrics": row[5] or "",
        "plain_lyrics": row[6] or "",
        "updated_at": updated_at,
        "cached": True,
    }

    # A synchronized result can be ordinary line-timed LRC or enhanced word-timed LRC.
    # The visualizer displays whole lines, so line timing is fully usable.
    if cached_result["status"] == "synced":
        parsed = parse_synced_lyrics_compact(cached_result["synced_lyrics"])
        if not parsed:
            return None
        cached_result["has_word_sync"] = _has_true_word_sync(cached_result["synced_lyrics"])

    return cached_result


def save_cached_lyrics(title, artist, album, duration, result, db_path=None):
    """Save a lyric result. Transient network failures are deliberately not cached."""
    # A network failure is not evidence that the song has no lyrics. Do not
    # cache it, otherwise a temporary connection problem can poison future
    # lyric lookups until the cache expires.
    # A confirmed "not_found" result is deliberately cached. It means the
    # complete lyrics search ran and found no usable lyrics for this song.
    # Network/transport failures remain transient and are never cached.
    transient_statuses = {"network_error", "invalid_response", "word_sync_not_found"}
    if str(result.get("status") or "") in transient_statuses:
        result = dict(result)
        result["cached"] = False
        return result

    key = make_cache_key(title, artist, album, duration)
    now = time.time()

    synced = str(result.get("synced_lyrics") or "")
    plain = str(result.get("plain_lyrics") or "")
    source = str(result.get("source") or "")
    status = str(result.get("status") or "not_found")

    with _open_database(db_path) as connection:
        connection.execute(
            """
            INSERT INTO visualizer_song_lyrics (
                fingerprint_key, title, artist, album, duration,
                synced_lyrics, plain_lyrics, source, status, updated_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(fingerprint_key) DO UPDATE SET
                title = excluded.title,
                artist = excluded.artist,
                album = excluded.album,
                duration = excluded.duration,
                synced_lyrics = excluded.synced_lyrics,
                plain_lyrics = excluded.plain_lyrics,
                source = excluded.source,
                status = excluded.status,
                updated_at = excluded.updated_at
            """,
            (
                key,
                title,
                artist,
                album,
                _safe_float(duration),
                synced,
                plain,
                source,
                status,
                now,
            ),
        )
        connection.commit()

    result = dict(result)
    result["cached"] = False
    result["updated_at"] = now
    return result


def _has_true_word_sync(synced_lyrics):
    """Return True only when the LRC contains explicit per-word timestamps."""
    if not synced_lyrics:
        return False
    try:
        parsed = parse_enhanced_lyrics(synced_lyrics)
    except Exception:
        return False
    return any(bool(item.get("words")) for item in parsed if isinstance(item, dict))


def _require_word_synced_result(result):
    """Normalize a lyric result; synchronized line timing is valid even without word timing."""
    if not isinstance(result, dict):
        return None
    if result.get("status") != "synced":
        return result
    synced = str(result.get("synced_lyrics") or "")
    if not parse_synced_lyrics_compact(synced):
        return None
    result = dict(result)
    result["has_word_sync"] = _has_true_word_sync(synced)
    return result


# ---------------------------------------------------------------------------
# MAIN PUBLIC API
# ---------------------------------------------------------------------------


def get_lyrics(title, artist, album="", duration=None, db_path=None,
               force_refresh=False, max_age=CACHE_MAX_AGE, extra_queries=None):
    """
    Get lyrics for a song.

    Cache is checked first.  Only a cache miss/expired entry performs a
    network request.  The returned dictionary is safe to pass to the main
    visualizer.
    """
    if not force_refresh:
        cached = load_cached_lyrics(
            title,
            artist,
            album,
            duration,
            db_path=db_path,
            max_age=max_age,
        )
        if cached is not None:
            return cached

    result = fetch_lyrics(title, artist, album, duration, extra_queries=extra_queries)
    result = _require_word_synced_result(result) or {
        "success": False,
        "status": "not_found",
        "source": "",
        "synced_lyrics": "",
        "plain_lyrics": "",
    }

    try:
        return save_cached_lyrics(
            title,
            artist,
            album,
            duration,
            result,
            db_path=db_path,
        )
    except sqlite3.Error:
        # Lyrics should never prevent the song from playing if the database
        # is temporarily unavailable.
        return result


def get_synced_lines(title, artist, album="", duration=None, db_path=None,
                     force_refresh=False):
    """Convenience function: fetch/cache lyrics and return prepared synced lines."""
    result = get_lyrics(
        title,
        artist,
        album,
        duration,
        db_path=db_path,
        force_refresh=force_refresh,
    )

    synced = result.get("synced_lyrics", "")
    if not synced:
        return result, prepare_lyrics([])

    enhanced = parse_enhanced_lyrics(synced)
    if enhanced:
        return result, prepare_lyrics(enhanced)
    return result, prepare_lyrics(parse_synced_lyrics_compact(synced))


class LyricsTrack:
    """
    Small playback helper.

    The expensive work happens during construction. During playback,
    current_line() is just a bisect lookup.
    """

    def __init__(self, result=None, lines=None):
        self.result = result or {}
        self.prepared = prepare_lyrics(lines or [])
        self.last_index = -1

    @property
    def has_synced_lyrics(self):
        return bool(self.prepared.get("times"))

    def current_index(self, playback_seconds):
        index = get_current_line_index(self.prepared, playback_seconds)
        self.last_index = index
        return index

    def current_line(self, playback_seconds):
        index = self.current_index(playback_seconds)
        if index < 0:
            return None
        return self.prepared["lines"][index]

    def current_line_romanized(self, playback_seconds):
        """Return the active line in pronunciation-friendly Latin text."""
        line = self.current_line(playback_seconds)
        return transliterate_lyrics_line(line) if line is not None else None

    def current_line_changed(self, playback_seconds):
        """
        Return (changed, index, text).

        This is useful for the renderer: rebuild the lyric text surface only
        when the active line changes instead of rebuilding it every frame.
        """
        index = get_current_line_index(self.prepared, playback_seconds)
        changed = index != self.last_index
        self.last_index = index

        if index < 0:
            return changed, -1, None

        return changed, index, self.prepared["lines"][index]


__all__ = [
    "ensure_lyrics_table",
    "get_default_database_path",
    "normalize_text",
    "make_cache_key",
    "parse_synced_lyrics",
    "parse_enhanced_lyrics",
    "parse_synced_lyrics_compact",
    "prepare_lyrics",
    "get_current_line",
    "get_current_line_index",
    "get_current_word_index",
    "get_current_word",
    "transliterate_devanagari",
    "transliterate_lyrics_line",
    "fetch_lyrics",
    "_fetch_lyrics_musixmatch_word_sync",
    "_fetch_lyrics_lrcmux_word_sync",
    "_fetch_lyrics_lrcapi",
    "_fetch_lyrics_synclrc",
    "load_cached_lyrics",
    "save_cached_lyrics",
    "get_lyrics",
    "get_synced_lines",
    "get_identified_song_info",
    "get_lyrics_for_audio",
    "get_synced_lines_for_audio",
    "LyricsTrack",
]

# ---------------------------------------------------------------------------
# SONG IDENTIFICATION BRIDGE
# ---------------------------------------------------------------------------


def get_identified_song_info(audio_path):
    """
    Use identify_song_and_vibe.py as the single source of truth for song
    identification, then return all details it exposes for the current song.

    This function deliberately does not duplicate AcoustID, MusicBrainz,
    embedded-metadata, or vibe-detection logic. The detector remains
    responsible for identifying the song; lyrics.py only consumes its result.

    Returns the detector's song-info dictionary, or a clean error result when
    identification cannot be completed.
    """
    audio_path = os.path.abspath(os.fspath(audio_path))

    try:
        import identify_song_and_vibe as vibe_detector
    except Exception as exc:
        return {
            "success": False,
            "status": "detector_import_error",
            "error": str(exc),
            "song_info": {},
        }

    try:
        # analyze_song_vibe() already performs the complete identification
        # pipeline and updates get_last_visualizer_song_info().
        vibe_detector.analyze_song_vibe(audio_path)

        getter = getattr(vibe_detector, "get_last_visualizer_song_info", None)
        if not callable(getter):
            return {
                "success": False,
                "status": "detector_api_missing",
                "error": "identify_song_and_vibe.py does not expose get_last_visualizer_song_info().",
                "song_info": {},
            }

        song_info = getter() or {}
        song_info = dict(song_info)

        title = str(song_info.get("title") or "").strip()
        artist = str(song_info.get("artist") or "").strip()

        if not title or not artist:
            return {
                "success": False,
                "status": "missing_song_metadata",
                "error": "Song identification did not provide both title and artist.",
                "song_info": song_info,
            }

        return {
            "success": True,
            "status": "identified",
            "song_info": song_info,
        }

    except Exception as exc:
        return {
            "success": False,
            "status": "identification_error",
            "error": str(exc),
            "song_info": {},
        }


def _filename_lyrics_identity(audio_path):
    """Return a strong ``Artist - Title`` identity from the audio filename.

    This is deliberately used only as a lyrics lookup hint.  It never
    replaces the fingerprint/song identity stored by identify_song_and_vibe.
    A common local-file pattern is:

        Artist - Title [Official Music Video].mp3

    The promotional suffix is removed before the identity is returned.
    """
    try:
        filename = os.path.basename(os.fspath(audio_path))
    except (TypeError, ValueError, OSError):
        return None

    stem = os.path.splitext(filename)[0].strip()
    if not stem or " - " not in stem:
        return None

    artist_part, title_part = stem.split(" - ", 1)
    artist_part = artist_part.strip(" ._-\t")
    title_part = title_part.strip(" ._-\t")

    # Remove common upload/promo suffixes, but leave meaningful parenthetical
    # title text alone when it is not clearly a video/lyrics tag.
    title_part = re.sub(
        r"\s*(?:\[(?:official\s+)?(?:music\s+)?video|\((?:official\s+)?(?:music\s+)?video|\[(?:official\s+)?lyrics?|\((?:official\s+)?lyrics?)\]?$",
        "",
        title_part,
        flags=re.IGNORECASE,
    ).strip(" ._-\t")
    title_part = re.sub(
        r"\s*(?:\[(?:official\s+)?(?:audio|video)|\((?:official\s+)?(?:audio|video))\]?$",
        "",
        title_part,
        flags=re.IGNORECASE,
    ).strip(" ._-\t")

    if not artist_part or not title_part:
        return None

    # Reject obviously non-identity filenames such as long technical names.
    # A real ``Artist - Title`` filename normally has short, human-readable
    # sides and contains letters rather than only numbers/symbols.
    if len(artist_part) > 120 or len(title_part) > 180:
        return None
    if not re.search(r"[A-Za-z\u0080-\uffff]", artist_part):
        return None
    if not re.search(r"[A-Za-z\u0080-\uffff]", title_part):
        return None

    return {"artist": artist_part, "title": title_part, "filename": filename}


def get_lyrics_for_audio(audio_path, db_path=None, force_refresh=False,
                         max_age=CACHE_MAX_AGE):
    """
    Identify an audio file with identify_song_and_vibe.py, then fetch/cache
    its lyrics using the identified song details.

    The returned dictionary contains:
        result["song_info"] -> full detector information
        result["lyrics"]    -> normal get_lyrics() result

    Lyrics lookup itself only uses the metadata LRCLIB needs (title, artist,
    album, duration). The complete identification result is preserved in the
    returned dictionary so the main visualizer can use it later without
    re-identifying the song.
    """
    identification = get_identified_song_info(audio_path)
    song_info = identification.get("song_info") or {}

    if not identification.get("success"):
        return {
            "success": False,
            "status": identification.get("status", "identification_error"),
            "error": identification.get("error", "Song identification failed."),
            "song_info": song_info,
            "lyrics": {
                "success": False,
                "status": identification.get("status", "identification_error"),
                "source": "",
                "synced_lyrics": "",
                "plain_lyrics": "",
            },
        }

    title = str(song_info.get("title") or "").strip()
    artist = str(song_info.get("artist") or "").strip()
    album = str(song_info.get("album") or "").strip()
    duration = song_info.get("duration")

    # Some cached fingerprint records preserve the filename itself as the
    # title, including the extension (for example ``Shape of You.m4a``).
    # That is not a real song title.  Normalize it before lyric lookup.
    if title and re.search(r"\.(?:mp3|wav|ogg|flac|m4a|aac|wma|opus)$", title, re.IGNORECASE):
        title = os.path.splitext(title)[0].strip()

    # A filename can contain a stronger human-readable identity than a stale
    # cached fingerprint.  This matters especially when the file has no
    # embedded tags: the fingerprint may identify a different performance of
    # the same title.  Use the filename ONLY for lyrics lookup; the detector's
    # song_info remains untouched for vibe/settings purposes.
    filename_identity = _filename_lyrics_identity(audio_path)
    filename_identity_used = False

    # Prefer a strong ``Artist - Title`` filename when its title agrees with
    # the detector title, or when the detector artist conflicts with it.  The
    # latter is the important safety case for files such as:
    #   Christina Perri - A Thousand Years [Official Music Video].mp3
    # where a cached fingerprint may return another performance/artist.
    if filename_identity:
        filename_title = normalize_text(filename_identity["title"])
        detected_title = normalize_text(title)
        filename_artist = normalize_text(filename_identity["artist"])
        detected_artist = normalize_text(artist)

        title_agrees = bool(filename_title and detected_title and (
            filename_title == detected_title
            or filename_title in detected_title
            or detected_title in filename_title
        ))
        artist_conflicts = bool(
            filename_artist and detected_artist
            and filename_artist != detected_artist
            and filename_artist not in detected_artist
            and detected_artist not in filename_artist
        )

        if title_agrees or artist_conflicts:
            title = filename_identity["title"]
            artist = filename_identity["artist"]
            filename_identity_used = True
            song_info = dict(song_info)
            song_info["lyrics_lookup_title"] = title
            song_info["lyrics_lookup_artist"] = artist
            song_info["lyrics_identity_source"] = "filename"
            print(
                "Lyrics identity from filename: "
                f"{artist} — {title}"
            )

    # The vibe detector can legitimately have a cached fingerprint whose
    # metadata is only the original filename (for example:
    # "Aashiyan_Barfi_Pritam_....m4a") and no artist.  In that situation an
    # exact LRCLIB lookup using the whole filename is almost guaranteed to
    # fail even though the song itself is well known.  Keep the detector as
    # the source of truth, but give the lyric lookup a small, generic
    # filename-based fallback.  This is especially useful for regional songs
    # whose local files were named with several underscore-separated tags.
    lookup_artist = artist
    if lookup_artist.casefold() in {"unknown artist", "unknown", "n/a"}:
        lookup_artist = ""

    filename_name = os.path.basename(audio_path).strip()
    filename_stem = os.path.splitext(filename_name)[0].strip()
    detector_title_is_filename = (
        bool(title)
        and bool(filename_stem)
        and title.casefold() in {
            filename_stem.casefold(),
            filename_name.casefold(),
        }
        and not filename_identity_used
    )

    # If the detector has only a filename-derived title and no reliable artist,
    # treat the clean filename stem as the actual title.  This covers files such
    # as ``Shape of You.m4a`` where there is no ``Artist - Title`` separator.
    if (not filename_identity_used and filename_stem and
            artist.casefold() in {"", "unknown artist", "unknown", "n/a", "none"} and
            normalize_text(title) == normalize_text(filename_stem)):
        title = filename_stem
        detector_title_is_filename = True

    # Build title candidates from the filename when the detector only has the
    # filename as its cached title.  IMPORTANT: put the short, likely song
    # title first.  Previously the full filename was tried first, which is
    # noisy and can lead to a final not_found even though the filename clearly
    # contains the real title.
    title_candidates = []
    filename_parts = []
    if detector_title_is_filename:
        filename_parts = [
            part.strip()
            for part in re.split(r"[_\-]+", filename_stem)
            if part.strip()
        ]

        if filename_parts:
            # Common local naming pattern:
            #   SongTitle_Movie_Artist_...
            # Try the first token by itself first, then the first two tokens
            # together for titles that contain a release/movie hint.
            for candidate in (
                filename_parts[0],
                " ".join(filename_parts[:2]) if len(filename_parts) >= 2 else "",
            ):
                if candidate and candidate.casefold() not in {
                    existing.casefold() for existing in title_candidates
                }:
                    title_candidates.append(candidate)

            # Also try text before common filename qualifiers.
            for separator in (" [", " (", " - "):
                if separator in filename_stem:
                    candidate = filename_stem.split(separator, 1)[0].strip()
                    if candidate and candidate.casefold() not in {
                        existing.casefold() for existing in title_candidates
                    }:
                        title_candidates.append(candidate)

        # Keep the detector's original title as the final fallback.
        if title and title.casefold() not in {
            existing.casefold() for existing in title_candidates
        }:
            title_candidates.append(title)
    else:
        title_candidates = [title] if title else []

    extra_queries = []
    if detector_title_is_filename and filename_parts:
        # These are search phrases only, not artist/title metadata.
        # They give the provider additional context without corrupting the
        # metadata returned by the song-identification module.
        # Many local Indian-song filenames contain the title/movie first and
        # then a run of performer names.  When the detector has no artist,
        # prioritize queries that combine the title with the later name tokens.
        # These are search phrases only; they never change the detector's
        # cached song metadata.
        if len(filename_parts) >= 5:
            # Build the strongest filename-derived performer queries first.
            # For Aashiyan_Barfi_Pritam_Shreya_Nikhil_Paul_George_... the
            # first query must be exactly:
            #     Aashiyan Shreya Nikhil Paul George
            # Do not let later filename names (actors/characters) contaminate
            # the artist query, and do not let a generic title win first.
            performer_queries = []
            for start_index, widths in ((3, (5, 4, 3)), (2, (5, 4, 3))):
                for width in widths:
                    end_index = start_index + width
                    if len(filename_parts) >= end_index:
                        performer_query = " ".join(
                            [filename_parts[0]] + filename_parts[start_index:end_index]
                        )
                        if performer_query.casefold() not in {
                            q.casefold() for q in performer_queries
                        }:
                            performer_queries.append(performer_query)

            # Put these ahead of every generic title query.
            extra_queries.extend(performer_queries)


        # Also try the short filename prefixes as a final fallback.
        for count in (2, 3):
            if len(filename_parts) >= count:
                query = " ".join(filename_parts[:count])
                if query.casefold() not in {q.casefold() for q in extra_queries}:
                    extra_queries.append(query)

    # Do not let a broad metadata resolver override a filename that already
    # contains useful performer information.  A broad MusicBrainz recording
    # search can return an unrelated artist for a common title such as
    # "Aashiyan".  The filename-derived queries above are more specific and
    # are passed to syncedlyrics first.
    #
    # MusicBrainz is still available for cases where the detector supplied a
    # real title but there is no filename-derived performer information.
    if not lookup_artist and title_candidates and not detector_title_is_filename:
        resolved = _musicbrainz_resolve_recording(
            title_candidates[0], album=album, duration=duration,
            extra_queries=extra_queries, timeout=REQUEST_TIMEOUT
        )
        if resolved and resolved.get("artist"):
            lookup_artist = resolved["artist"]
            song_info = dict(song_info)
            song_info["lyrics_resolved_artist"] = lookup_artist
            if resolved.get("title"):
                song_info["lyrics_resolved_title"] = resolved["title"]
            if resolved.get("album"):
                song_info["lyrics_resolved_album"] = resolved["album"]
            if resolved.get("duration"):
                song_info["lyrics_resolved_duration"] = resolved["duration"]
            print(f"Lyrics metadata resolved: {resolved.get('title')} — {lookup_artist}")
            if resolved.get("album"):
                print(f"Lyrics album resolved: {resolved.get('album')}")

    # Perform ONE lyrics lookup. All filename title candidates are passed as
    # additional queries instead of repeating the complete provider pipeline.
    primary_title = title_candidates[0] if title_candidates else title
    consolidated_queries = []
    seen_queries = set()
    for query in list(title_candidates[1:]) + list(extra_queries):
        query = str(query or "").strip()
        key = normalize_text(query)
        if key and key != normalize_text(primary_title) and key not in seen_queries:
            seen_queries.add(key)
            consolidated_queries.append(query)

    lyrics_result = get_lyrics(
        primary_title,
        lookup_artist,
        song_info.get("lyrics_resolved_album", album),
        duration,
        db_path=db_path,
        force_refresh=force_refresh,
        max_age=max_age,
        extra_queries=consolidated_queries,
    )

    if primary_title != title and lyrics_result.get("success"):
        song_info = dict(song_info)
        song_info["lyrics_lookup_title"] = primary_title

    return {
        "success": bool(lyrics_result.get("success")),
        "status": lyrics_result.get("status", "not_found"),
        "song_info": song_info,
        "lyrics": lyrics_result,
    }


def get_synced_lines_for_audio(audio_path, db_path=None, force_refresh=False,
                               max_age=CACHE_MAX_AGE):
    """
    Identify an audio file, get/cache its lyrics, and prepare synced lines.

    Returns:
        (combined_result, prepared_lines)
    """
    combined = get_lyrics_for_audio(
        audio_path,
        db_path=db_path,
        force_refresh=force_refresh,
        max_age=max_age,
    )

    lyrics_result = combined.get("lyrics") or {}
    synced = lyrics_result.get("synced_lyrics", "")

    if not synced:
        return combined, prepare_lyrics([])

    enhanced = parse_enhanced_lyrics(synced)
    if enhanced:
        return combined, prepare_lyrics(enhanced)
    return combined, prepare_lyrics(parse_synced_lyrics_compact(synced))


# ---------------------------------------------------------------------------
# STANDALONE TEST
# ---------------------------------------------------------------------------


def _format_timestamp(seconds):
    seconds = max(0.0, float(seconds))
    minutes = int(seconds // 60)
    remaining = seconds - (minutes * 60)
    return f"{minutes:02d}:{remaining:05.2f}"


def _run_connection_diagnostic():
    """Test basic HTTPS connectivity to LRCLIB without fetching lyrics."""
    import time

    print("=" * 56)
    print("The Visualizer - LRCLIB Connection Diagnostic")
    print("=" * 56)
    print()
    print("Target: https://lrclib.net/api/get")
    print("Testing HTTPS connection only; no lyrics lookup yet...")
    print()

    try:
        import requests
    except Exception as exc:
        print("FAILED: requests could not be imported.")
        print(f"Error: {type(exc).__name__}: {exc}")
        return

    headers = {
        "User-Agent": "TheVisualizer-Lyrics/1.0 (local music visualizer)",
        "Accept": "application/json",
    }

    started = time.perf_counter()
    try:
        response = requests.get(
            "https://lrclib.net/api/get",
            params={
                "track_name": "Faded",
                "artist_name": "Alan Walker",
                "album_name": "",
                "duration": 212,
            },
            headers=headers,
            timeout=(8, 15),
        )
        elapsed = time.perf_counter() - started

        print(f"HTTP status : {response.status_code}")
        print(f"Time        : {elapsed:.2f} seconds")
        print(f"Final URL   : {response.url}")
        print(f"Content type: {response.headers.get('content-type', 'unknown')}")
        print(f"Response size: {len(response.content)} bytes")
        print()

        if response.ok:
            print("SUCCESS: LRCLIB is reachable from Python requests.")
            print("The earlier failure was therefore likely specific to the previous request or connection state.")
        elif response.status_code == 404:
            print("SUCCESS: LRCLIB is reachable; the server simply returned 404 for this test lookup.")
        else:
            print(f"LRCLIB responded normally with HTTP {response.status_code}.")
            print("This is not a Windows connection-aborted error.")

        preview = response.text.replace("\n", " ")[:300]
        if preview:
            print()
            print("Response preview:")
            print(preview)

    except requests.exceptions.SSLError as exc:
        elapsed = time.perf_counter() - started
        print(f"FAILED after {elapsed:.2f} seconds: SSL/TLS error")
        print(f"{type(exc).__name__}: {exc}")
    except requests.exceptions.ProxyError as exc:
        elapsed = time.perf_counter() - started
        print(f"FAILED after {elapsed:.2f} seconds: proxy error")
        print(f"{type(exc).__name__}: {exc}")
    except requests.exceptions.Timeout as exc:
        elapsed = time.perf_counter() - started
        print(f"FAILED after {elapsed:.2f} seconds: timeout")
        print(f"{type(exc).__name__}: {exc}")
    except requests.exceptions.ConnectionError as exc:
        elapsed = time.perf_counter() - started
        print(f"FAILED after {elapsed:.2f} seconds: connection error")
        print(f"{type(exc).__name__}: {exc}")
        print()
        print("If this is WinError 10053 again, something on Windows/network security software is aborting the connection.")
    except Exception as exc:
        elapsed = time.perf_counter() - started
        print(f"FAILED after {elapsed:.2f} seconds: unexpected error")
        print(f"{type(exc).__name__}: {exc}")


def _run_standalone_test():
    """Small manual test so lyrics.py can be run directly from PyCharm."""
    print("=" * 56)
    print("The Visualizer - Lyrics Test")
    print("=" * 56)
    print()

    diagnostic = input("Run LRCLIB connection diagnostic first? [Y/n]: ").strip().lower()
    if diagnostic in ("", "y", "yes"):
        _run_connection_diagnostic()
        print()
        print("=" * 56)
        print()

    title = input("Song title: ").strip()
    artist = input("Artist: ").strip()
    album = input("Album (optional): ").strip()
    duration_text = input("Duration in seconds (optional): ").strip()

    duration = None
    if duration_text:
        try:
            duration = float(duration_text)
        except ValueError:
            print("Invalid duration. Continuing without duration.")

    if not title or not artist:
        print("\nTitle and artist are required.")
        return

    print("\nSearching LRCLIB...")
    result = get_lyrics(title, artist, album, duration)

    print()
    print(f"Status : {result.get('status', 'unknown')}")
    print(f"Source : {result.get('source') or 'none'}")
    print(f"Cached : {'yes' if result.get('cached') else 'no'}")

    synced = result.get("synced_lyrics") or ""
    plain = result.get("plain_lyrics") or ""

    if synced:
        lines = parse_synced_lyrics_compact(synced)
        prepared = prepare_lyrics(lines)

        print(f"Lines  : {len(lines)} synchronized lines")
        print()
        print("First 10 synced lines:")
        print("-" * 56)

        for timestamp, text_value in lines[:10]:
            print(f"[{_format_timestamp(timestamp)}] {text_value}")

        print("-" * 56)
        print()
        print("Current-line lookup test:")

        test_times = []
        if prepared["times"]:
            first = prepared["times"][0]
            test_times = [first, first + 5.0, first + 15.0]

        for test_time in test_times:
            current = get_current_line(prepared, test_time)
            print(f"  {_format_timestamp(test_time)} -> {current!r}")

        print()
        print("Lyrics engine test completed successfully.")

    elif plain:
        print("Plain lyrics were found, but they are not timestamp-synced.")
        print("They are cached, but the live lyric system will not use them for timing.")
        print()
        print("First few lines:")
        print("-" * 56)
        for line in plain.splitlines()[:10]:
            print(line)
        print("-" * 56)

    elif result.get("status") == "not_found":
        print("No lyrics were found for this song.")
        print("This result is cached so repeated playback will not repeatedly query LRCLIB.")

    elif result.get("status") == "network_error":
        print("LRCLIB could not be reached.")
        print(f"Error: {result.get('error', 'unknown network error')}")

    else:
        print("No usable lyrics were returned.")
        if result.get("error"):
            print(f"Error: {result['error']}")


# ---------------------------------------------------------------------------
# TEMPORARY STANDALONE AUDIO + LYRICS PLAYER
# ---------------------------------------------------------------------------


def _select_audio_file_for_test():
    """Open a temporary song picker for standalone lyrics testing."""
    try:
        import tkinter as tk
        from tkinter import filedialog

        root = tk.Tk()
        root.withdraw()
        root.update()
        path = filedialog.askopenfilename(
            title="Select a song to test lyrics",
            filetypes=[
                ("Audio files", "*.mp3 *.wav *.ogg *.flac *.m4a *.aac"),
                ("All files", "*.*"),
            ],
        )
        root.destroy()
        return path
    except Exception as exc:
        print(f"Could not open song selector: {exc}")
        return ""




def _find_ffmpeg_for_lyrics_test():
    """Find FFmpeg for the standalone lyrics player."""
    candidates = []

    project_dir = os.path.dirname(os.path.abspath(__file__))
    candidates.extend([
        os.path.join(project_dir, "ffmpeg.exe"),
        os.path.join(project_dir, "ffmpeg-9.0.1-essentials_build", "bin", "ffmpeg.exe"),
    ])

    try:
        import imageio_ffmpeg
        bundled = imageio_ffmpeg.get_ffmpeg_exe()
        if bundled:
            candidates.append(bundled)
    except Exception:
        pass

    path_ffmpeg = shutil.which("ffmpeg")
    if path_ffmpeg:
        candidates.append(path_ffmpeg)

    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            return candidate

    return None
def _find_unicode_font(text=""):
    """Find a broadly Unicode-capable font for the standalone lyric window."""
    project_dir = os.path.dirname(os.path.abspath(__file__))
    candidates = [
        # Windows fonts first. Nirmala UI has broad Indic/Sinhala coverage.
        os.path.join(os.environ.get("WINDIR", r"C:\\Windows"), "Fonts", "Nirmala.ttf"),
        os.path.join(os.environ.get("WINDIR", r"C:\\Windows"), "Fonts", "NirmalaUI.ttf"),
        os.path.join(os.environ.get("WINDIR", r"C:\\Windows"), "Fonts", "seguisym.ttf"),
        os.path.join(os.environ.get("WINDIR", r"C:\\Windows"), "Fonts", "segoeui.ttf"),
        # Common Linux/macOS paths as a fallback for development/testing.
        "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/opentype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        os.path.join(project_dir, "NotoSans-Regular.ttf"),
        os.path.join(project_dir, "NotoSans.ttf"),
    ]
    for path in candidates:
        if path and os.path.isfile(path):
            return path
    return None


def _wrap_lyric_text(font, text, max_width):
    """Wrap Unicode lyric text without breaking words when possible."""
    text = str(text or "").strip()
    if not text:
        return [""]

    words = text.split()
    if not words:
        return [text]

    lines = []
    current = ""
    for word in words:
        candidate = word if not current else current + " " + word
        if font.size(candidate)[0] <= max_width:
            current = candidate
            continue

        if current:
            lines.append(current)
            current = word
        else:
            # Very long unbroken text: split by characters.
            chunk = ""
            for char in word:
                candidate_char = chunk + char
                if chunk and font.size(candidate_char)[0] > max_width:
                    lines.append(chunk)
                    chunk = char
                else:
                    chunk = candidate_char
            current = chunk

    if current:
        lines.append(current)
    return lines or [text]


def _prepare_plain_display_lines(plain_text):
    """Turn plain lyrics into display lines for the standalone fallback."""
    lines = []
    for raw in str(plain_text or "").splitlines():
        line = raw.strip()
        if line:
            lines.append(line)
    return lines


def _run_standalone_player():
    """Temporary standalone player used only to test synced lyrics.

    Pygame's built-in decoder cannot reliably open every audio format/file.
    When that happens, convert the selected file to a temporary WAV with
    FFmpeg and let pygame play the WAV instead.
    """
    print("=" * 64)
    print("The Visualizer - Standalone Lyrics Player")
    print("=" * 64)
    print()
    print("Select a song. It will be identified, lyrics will be fetched, and")
    print("the song will play while the currently timed lyric is shown here.")
    print()

    audio_path = _select_audio_file_for_test()
    if not audio_path:
        print("No song selected.")
        return

    print(f"Selected: {audio_path}")
    print("\nIdentifying song and loading lyrics...")

    combined, prepared = get_synced_lines_for_audio(audio_path)

    if not combined.get("success"):
        print(f"Lyrics lookup failed: {combined.get('error', combined.get('status'))}")
        return

    song_info = combined.get("song_info") or {}
    lyrics_result = combined.get("lyrics") or {}

    print()
    print(f"Title   : {song_info.get('title', '')}")
    print(f"Artist  : {song_info.get('artist', '')}")
    print(f"Album   : {song_info.get('album', '') or '(unknown)'}")
    print(f"Duration: {song_info.get('duration', '')}")
    print(f"Lyrics  : {lyrics_result.get('status', 'unknown')}")
    print(f"Source  : {lyrics_result.get('source') or 'none'}")

    has_synced = bool(prepared.get("times"))
    has_word_sync = bool(prepared.get("has_word_sync"))
    print(f"Word sync: {'yes' if has_word_sync else 'no'}")
    plain_lines = _prepare_plain_display_lines(lyrics_result.get("plain_lyrics", ""))

    if not has_synced:
        print("\nNo timestamp-synchronized lyrics are available for this song.")
        print("Plain-only lyrics, when present, are intentionally not used for live timing.")
        return

    try:
        import pygame
    except Exception as exc:
        print(f"\npygame is required for the temporary player: {exc}")
        return

    temp_wav = None
    playback_path = audio_path

    try:
        pygame.init()
        pygame.font.init()
        pygame.mixer.init()

        # First try the original file. This keeps playback simple for formats
        # pygame can already handle. If its decoder fails, use FFmpeg.
        try:
            pygame.mixer.music.load(audio_path)
        except Exception as direct_exc:
            print(f"\nPygame could not decode the selected file: {direct_exc}")
            print("Converting it to a temporary WAV with FFmpeg...")

            temp_dir = tempfile.mkdtemp(prefix="the_visualizer_lyrics_")
            temp_wav = os.path.join(temp_dir, "playback.wav")

            ffmpeg_path = _find_ffmpeg_for_lyrics_test()
            if not ffmpeg_path:
                raise RuntimeError(
                    "FFmpeg was not found. Put ffmpeg.exe in the project "
                    "folder or install FFmpeg so it is available on PATH."
                ) from direct_exc

            command = [
                ffmpeg_path,
                "-y",
                "-i", audio_path,
                "-vn",
                "-ac", "2",
                "-ar", "44100",
                "-c:a", "pcm_s16le",
                temp_wav,
            ]

            result = subprocess.run(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )

            if result.returncode != 0 or not os.path.isfile(temp_wav):
                detail = result.stderr.strip().splitlines()
                detail = detail[-1] if detail else "Unknown FFmpeg error."
                raise RuntimeError(f"FFmpeg conversion failed: {detail}") from direct_exc

            playback_path = temp_wav
            pygame.mixer.music.load(playback_path)
            print("Temporary WAV created successfully.")

    except Exception as exc:
        print(f"\nCould not play this audio file: {exc}")
        try:
            pygame.mixer.music.stop()
            pygame.mixer.quit()
        except Exception:
            pass
        if temp_wav:
            try:
                shutil.rmtree(os.path.dirname(temp_wav), ignore_errors=True)
            except Exception:
                pass
        return

    print()
    print("Controls: SPACE = pause/resume | ESC = stop | Q = quit")
    print("Starting playback...\n")

    screen = pygame.display.set_mode((900, 260))
    pygame.display.set_caption("The Visualizer - Lyrics Test")
    clock = pygame.time.Clock()

    unicode_font_path = _find_unicode_font()
    try:
        font = pygame.font.Font(unicode_font_path, 34) if unicode_font_path else pygame.font.Font(None, 34)
        small_font = pygame.font.Font(unicode_font_path, 24) if unicode_font_path else pygame.font.Font(None, 24)
    except Exception:
        font = pygame.font.Font(None, 34)
        small_font = pygame.font.Font(None, 24)

    pygame.mixer.music.play()
    paused = False
    running = True
    last_index = -1
    last_text = ""
    plain_page = 0
    plain_page_started = time.monotonic()
    plain_page_lines = []

    try:
        while running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE or event.key == pygame.K_q:
                        running = False
                    elif event.key == pygame.K_SPACE:
                        if paused:
                            pygame.mixer.music.unpause()
                            paused = False
                        else:
                            pygame.mixer.music.pause()
                            paused = True

            if not paused:
                position = max(0.0, pygame.mixer.music.get_pos() / 1000.0)

                if has_synced:
                    index = get_current_line_index(prepared, position)
                    if index != last_index:
                        current = get_current_line(prepared, position)
                        last_index = index
                        last_text = current or ""
                        romanized_text = transliterate_lyrics_line(last_text)
                        print(f"[{_format_timestamp(position)}] {romanized_text}")
                else:
                    # Plain lyrics have no authoritative timestamps. Show a
                    # small page at a time instead of pretending they are synced.
                    if plain_lines and time.monotonic() - plain_page_started >= 4.0:
                        plain_page = (plain_page + 3) % len(plain_lines)
                        plain_page_started = time.monotonic()

                    if plain_lines:
                        page_items = plain_lines[plain_page:plain_page + 3]
                        plain_page_lines = []
                        for item in page_items:
                            plain_page_lines.extend(_wrap_lyric_text(font, item, 820))

            screen.fill((0, 0, 0))
            if has_synced:
                current_index = get_current_line_index(prepared, position)
                if has_word_sync and current_index >= 0:
                    words = prepared["words"][current_index]
                    word_index = get_current_word_index(prepared, position, current_index)
                    pieces = []
                    for i, (_, raw_word) in enumerate(words):
                        word = transliterate_lyrics_line(raw_word)
                        # Future words stay dim; the word currently being sung
                        # is bright; completed words are also bright but slightly
                        # softer. This is the karaoke behavior the line-only
                        # version could not provide.
                        if i == word_index:
                            text_color = (255, 255, 255)
                        elif i < word_index:
                            text_color = (210, 210, 210)
                        else:
                            text_color = (90, 90, 90)
                        pieces.append((word, text_color))

                    total_width = sum(font.size(text)[0] for text, _ in pieces)
                    x = (900 - total_width) / 2
                    y = 85
                    for text, text_color in pieces:
                        surface = font.render(text, True, text_color)
                        screen.blit(surface, (x, y))
                        x += surface.get_width()
                else:
                    display_text = transliterate_lyrics_line(last_text)
                    display_lines = _wrap_lyric_text(font, display_text or "...", 820)
                    start_y = 85 - ((len(display_lines) - 1) * 20)
                    for line_number, line in enumerate(display_lines):
                        lyric_surface = font.render(line, True, (255, 255, 255))
                        screen.blit(
                            lyric_surface,
                            lyric_surface.get_rect(center=(450, start_y + line_number * 40)),
                        )
            else:
                display_lines = plain_page_lines or ["..."]
                start_y = 85 - ((len(display_lines) - 1) * 20)
                for line_number, line in enumerate(display_lines):
                    lyric_surface = font.render(line, True, (255, 255, 255))
                    screen.blit(
                        lyric_surface,
                        lyric_surface.get_rect(center=(450, start_y + line_number * 40)),
                    )

            info = "PAUSED" if paused else (("Playing • word synced" if has_word_sync else "Playing • line synced") if has_synced else "Playing • plain lyrics")
            info_surface = small_font.render(info, True, (150, 150, 150))
            screen.blit(
                info_surface,
                info_surface.get_rect(center=(450, 225)),
            )
            pygame.display.flip()

            if not pygame.mixer.music.get_busy() and not paused:
                running = False

            clock.tick(30)
    finally:
        pygame.mixer.music.stop()
        pygame.mixer.quit()
        pygame.display.quit()

        if temp_wav:
            try:
                shutil.rmtree(os.path.dirname(temp_wav), ignore_errors=True)
            except Exception:
                pass

    print("\nPlayback test finished.")


if __name__ == "__main__":
    _run_standalone_player()

