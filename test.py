import os  # Work with file and folder paths
import math  # Draw the Undo curved-arrow icon
import ctypes  # Access the Windows API so a normal decorated window can be maximized
import json  # Save and load cache information
import hashlib  # Create unique cache names
import sqlite3  # Store song-specific visualizer images in the existing local database
import threading  # Run analysis in the background
import time  # Measure real playback elapsed time without rebuilding the timeline from mixer offsets
import tkinter as tk  # Create the song-selection window
from tkinter import filedialog, messagebox, colorchooser  # Show file dialogs, messages, and color pickers

import numpy as np  # Work with numerical arrays
import pygame  # Play music and draw the visualizer
import soundfile as sf  # Read the converted WAV file in small blocks
from scipy.fft import rfft, rfftfreq  # Use SciPy's fast FFT functions
from PIL import Image, ImageDraw  # Load images and build anti-aliased rounded-corner masks
import tempfile  # Materialize database-stored images temporarily for Pillow
import subprocess  # Use the project FFmpeg as a fallback for image formats Pillow cannot decode
import identify_song_and_vibe as vibe_detector  # Load the exact vibe detector module Python found
import lyrics as lyrics_engine  # Reuse the standalone lyrics engine for synchronized lyrics

if not hasattr(vibe_detector, "analyze_song_vibe"):
    raise ImportError(
        "The identify_song_and_vibe.py being loaded does not contain analyze_song_vibe. "
        f"Python loaded: {vibe_detector.__file__}"
    )  # Stop clearly instead of silently using the wrong detector file

analyze_song_vibe = vibe_detector.analyze_song_vibe  # Use the reusable function from the loaded detector
print(f"Vibe detector loaded from: {vibe_detector.__file__}")  # Show exactly which detector file Test 15 is using

if not hasattr(lyrics_engine, "get_synced_lines_for_audio"):
    raise ImportError(
        "The lyrics.py being loaded does not contain get_synced_lines_for_audio. "
        f"Python loaded: {getattr(lyrics_engine, '__file__', 'unknown')}"
    )  # Stop clearly instead of silently using an incompatible lyrics module

print(f"Lyrics engine loaded from: {lyrics_engine.__file__}")  # Show exactly which lyrics.py the visualizer is using


# ============================================================
# SETTINGS
# ============================================================

SAMPLE_RATE = 22050  # Use a lower sample rate to speed up analysis

ANALYSIS_CHUNK_SIZE = 1000  # Use shorter frames so fast piano notes are tracked more precisely

FFT_SIZE = 4096  # Use a larger FFT so piano frequencies are separated more clearly

LOOKAHEAD_SECONDS = 5.0  # Keep several seconds of analysis ahead

STARTUP_READY_SECONDS = 1.5  # Analyze this much audio before playback starts

MIN_ANALYSIS_AHEAD_SECONDS = 0.20  # Pause playback if analysis falls behind

WAVE_HEIGHT = 0.30  # Keep the same visual bar height as before

PIANO_KEYS = 88  # A standard piano has 88 keys

A4_FREQUENCY = 440.0  # A4 is the reference frequency for piano tuning

NOTE_THRESHOLD = 0.08  # Ignore weak detections so random FFT peaks do not become bars

VOLUME_REFERENCE = 0.10  # Use this RMS level as the full-height reference for volume

HARMONIC_WEIGHTS = np.array(
    [1.0, 0.25, 0.20, 0.05, 0.02],
    dtype=np.float32
)  # Make the fundamental dominate so harmonics are less likely to select the wrong key

FUNDAMENTAL_MINIMUM = 0.035  # Require useful energy at the actual piano-key frequency

CONTINUITY_STRENGTH = 0.12  # Prefer nearby notes slightly so the leading piano line does not jump randomly

MAX_CONTINUITY_DISTANCE = 12  # Do not strongly favor notes more than one octave away

BASS_ANALYSIS_CHUNK_SIZE = 1000  # Use the same 1000-sample bass-analysis chunks as The Waver
BASS_LOW_FREQUENCY = 20.0  # Start the bass analysis at 20 Hz, matching The Waver
BASS_HIGH_FREQUENCY = 250.0  # End the bass analysis at 250 Hz, matching The Waver
BASS_ATTACK = 0.18  # Smoothly increase the background bass level
BASS_RELEASE = 0.08  # Smoothly decrease the background bass level
BACKGROUND_IDLE = (0, 0, 0)  # Keep the idle background pitch black
BACKGROUND_BASS = (5, 4, 78)  # Keep the original bass color as the fallback if vibe detection fails

VIBE_COLORS = {
    "romantic": (255, 70, 150),  # Use rose pink for romantic music
    "sad": (55, 100, 220),  # Use deep blue for sad music
    "calm": (55, 200, 180),  # Use teal for calm music
    "happy": (255, 210, 55),  # Use golden yellow for happy music
    "energetic": (255, 120, 25),  # Use orange for energetic music
    "intense": (245, 45, 45),  # Use red for intense music
    "acoustic": (210, 150, 65),  # Use warm amber for acoustic music
    "electronic": (30, 220, 255),  # Use cyan for electronic music
}

ACOUSTIC_HAPPY_COMBO_COLORS = {
    "acoustic": (190, 70, 75),  # Use deep coral when acoustic and happy appear together
    "happy": (255, 215, 35),  # Use brighter golden yellow when acoustic and happy appear together
}

BRIGHT_BASS_OPACITY = 0.40  # Keep bright bass colors from becoming visually overpowering
DARK_BASS_OPACITY = 0.80  # Keep dark bass colors at the current 80% strength


def is_bright_color(color):
    # Calculate perceived brightness from the actual RGB color.
    r, g, b = color
    brightness = (
        0.299 * r
        + 0.587 * g
        + 0.114 * b
    )
    return brightness >= 150


def get_automatic_bass_opacity(color):
    # Use 40% for bright colors and 80% for dark colors.
    return (
        BRIGHT_BASS_OPACITY
        if is_bright_color(color)
        else DARK_BASS_OPACITY
    )
PRIMARY_VIBE_NAME = ""  # Store the current strongest vibe for automatic wave coloring
SECONDARY_VIBE_NAME = ""  # Store the current second-ranked vibe for bass color handling

PRIMARY_VIBE_COLOR = (255, 255, 255)  # Use white until the first song's vibe is detected
SECONDARY_VIBE_COLOR = BACKGROUND_BASS  # Use the fallback bass color until the first vibe result is ready
CUSTOM_WAVE_COLOR = None  # Store the user's custom wave color; None means use the automatic vibe color
CUSTOM_BASS_COLOR = None  # Store the user's custom bass color; None means use the automatic vibe color


# ============================================================
# PROJECT PATHS
# ============================================================

PROJECT_FOLDER = os.path.dirname(
    os.path.abspath(__file__)
)  # Find the project folder

FFMPEG_PATH = os.path.join(
    PROJECT_FOLDER,
    "ffmpeg-9.0.1-essentials_build",
    "bin",
    "ffmpeg.exe"
)  # Find FFmpeg inside the project

CONVERTED_AUDIO = os.path.join(
    PROJECT_FOLDER,
    "converted_audio.wav"
)  # Store the converted playback file here

CACHE_FOLDER = os.path.join(
    PROJECT_FOLDER,
    ".the_one_cache"
)  # Store The One's analysis cache here

BAR_SETTINGS_FILE = os.path.join(
    PROJECT_FOLDER,
    "bar_settings.json"
)  # Store the user's custom bar defaults separately from the analysis cache

os.makedirs(
    CACHE_FOLDER,
    exist_ok=True
)  # Create the cache folder if it does not exist


# ============================================================
# PRECOMPUTED FFT DATA
# ============================================================

FFT_WINDOW = np.hanning(
    ANALYSIS_CHUNK_SIZE
).astype(np.float32)  # Create a window that matches each short analysis chunk

FFT_FREQUENCIES = rfftfreq(
    FFT_SIZE,
    1.0 / SAMPLE_RATE
)  # Calculate the frequency represented by every FFT bin


# ============================================================
# PIANO FREQUENCIES
# ============================================================

PIANO_FREQUENCIES = (
    A4_FREQUENCY
    * (2.0 ** ((np.arange(PIANO_KEYS) - 48) / 12.0))
).astype(
    np.float32
)  # Calculate all 88 piano-key frequencies


# ============================================================
# BUILD FFT LOOKUP TABLE
# ============================================================

MAX_HARMONICS = len(
    HARMONIC_WEIGHTS
)  # Remember how many harmonics we inspect

BIN_LOOKUP = np.zeros(
    (PIANO_KEYS, MAX_HARMONICS, 5),
    dtype=np.int32
)  # Store several nearby FFT bins for every piano harmonic

VALID_LOOKUP = np.zeros(
    (PIANO_KEYS, MAX_HARMONICS, 5),
    dtype=bool
)  # Remember which lookup positions are valid


for key_index, fundamental in enumerate(PIANO_FREQUENCIES):

    for harmonic_index in range(MAX_HARMONICS):

        harmonic_frequency = (
            fundamental
            * (harmonic_index + 1)
        )  # Calculate this harmonic frequency

        if harmonic_frequency >= SAMPLE_RATE / 2:
            continue  # Ignore frequencies above the Nyquist limit

        nearest_bin = int(
            np.argmin(
                np.abs(
                    FFT_FREQUENCIES - harmonic_frequency
                )
            )
        )  # Find the closest FFT bin

        for offset_index, offset in enumerate((-2, -1, 0, 1, 2)):

            bin_index = nearest_bin + offset  # Check nearby FFT bins

            if 0 <= bin_index < len(FFT_FREQUENCIES):

                BIN_LOOKUP[
                    key_index,
                    harmonic_index,
                    offset_index
                ] = bin_index  # Save this FFT bin

                VALID_LOOKUP[
                    key_index,
                    harmonic_index,
                    offset_index
                ] = True  # Mark this lookup as valid


# ============================================================
# ANALYSIS STATE
# ============================================================

class HybridAnalysisState:

    def __init__(self):

        self.lock = threading.Lock()  # Protect shared analysis data

        self.fast_matrix = None  # Store fast analysis frames

        self.refined_matrix = None  # Store refined analysis frames

        self.analyzed_frames = 0  # Remember how many frames are ready

        self.song_duration = 0.0  # Store total song duration

        self.chunk_duration = (
            ANALYSIS_CHUNK_SIZE / SAMPLE_RATE
        )  # Calculate how long one frame represents

        self.finished = False  # Remember when analysis is complete

        self.cache_loaded = False  # Remember whether cache was loaded

        self.error = None  # Store an analysis error

        self.stop_event = threading.Event()  # Allow analysis to stop


# ============================================================
# ERROR MESSAGE
# ============================================================

def show_error_message(title, message):

    try:

        root = tk.Tk()  # Create a temporary Tkinter window

        root.withdraw()  # Hide the temporary Tkinter window

        messagebox.showerror(
            title,
            message
        )  # Show the error to the user

        root.destroy()  # Close the temporary Tkinter window

    except Exception:

        print(
            f"{title}: {message}"
        )  # Fall back to the terminal if Tkinter fails


# ============================================================
# CACHE
# ============================================================

def make_cache_key(source_path):

    absolute_path = os.path.abspath(
        source_path
    )  # Convert the source path to an absolute path

    file_size = os.path.getsize(
        absolute_path
    )  # Get the current file size

    modified_time = os.path.getmtime(
        absolute_path
    )  # Get the file modification time

    identity = {
        "path": absolute_path,
        "size": file_size,
        "mtime": modified_time,
        "sample_rate": SAMPLE_RATE,
        "chunk_size": ANALYSIS_CHUNK_SIZE,
        "fft_size": FFT_SIZE,
        "note_threshold": NOTE_THRESHOLD,
        "volume_reference": VOLUME_REFERENCE,
        "harmonic_weights": HARMONIC_WEIGHTS.tolist(),
        "fundamental_minimum": FUNDAMENTAL_MINIMUM,
        "continuity_strength": CONTINUITY_STRENGTH,
        "version": "test15_improved_piano_tracking_v3"
    }  # Identify this exact analysis configuration

    identity_text = json.dumps(
        identity,
        sort_keys=True
    )  # Convert the identity into stable text

    return hashlib.sha256(
        identity_text.encode("utf-8")
    ).hexdigest()  # Create a unique cache name


def get_cache_path(source_path):

    cache_key = make_cache_key(
        source_path
    )  # Create a unique cache key

    return os.path.join(
        CACHE_FOLDER,
        cache_key + ".npz"
    )  # Return the complete cache filename


def load_cache(source_path):

    cache_path = get_cache_path(
        source_path
    )  # Find the cache for this song

    if not os.path.exists(cache_path):
        return None  # No cache exists yet

    try:

        data = np.load(
            cache_path,
            allow_pickle=False
        )  # Load the cached analysis

        matrix = data["matrix"].astype(
            np.float32
        )  # Convert cached values to float32

        duration = float(
            data["duration"]
        )  # Load the cached duration

        return matrix, duration  # Return the cached data

    except Exception:

        return None  # Ignore broken caches and analyze again


def save_cache(source_path, matrix, duration):

    cache_path = get_cache_path(
        source_path
    )  # Find the correct cache filename

    temporary_path = cache_path + ".tmp"  # Write to a temporary cache first

    try:

        with open(
            temporary_path,
            "wb"
        ) as file:

            np.savez_compressed(
                file,
                matrix=matrix,
                duration=np.float32(duration)
            )  # Save the analysis

        os.replace(
            temporary_path,
            cache_path
        )  # Replace the old cache safely

    except Exception:

        try:

            if os.path.exists(temporary_path):

                os.remove(
                    temporary_path
                )  # Remove a failed temporary cache

        except Exception:

            pass  # Ignore cleanup errors


# ============================================================
# PIANO SCORING
# ============================================================

def score_all_piano_keys(spectrum):

    gathered_values = spectrum[
        BIN_LOOKUP
    ]  # Collect FFT values for every piano harmonic

    gathered_values = np.where(
        VALID_LOOKUP,
        gathered_values,
        0.0
    )  # Remove invalid lookup positions

    harmonic_strengths = np.max(
        gathered_values,
        axis=2
    )  # Take the strongest nearby FFT bin for every harmonic

    fundamental_strengths = harmonic_strengths[
        :,
        0
    ]  # Get the actual fundamental strength of every key

    weighted_harmonics = (
        harmonic_strengths
        * HARMONIC_WEIGHTS
    )  # Keep the fundamental dominant over the harmonics

    scores = np.sum(
        weighted_harmonics,
        axis=1
    )  # Combine fundamental and harmonic evidence

    valid_fundamentals = (
        fundamental_strengths >= FUNDAMENTAL_MINIMUM
    )  # Require real energy at the key's own fundamental

    scores = np.where(
        valid_fundamentals,
        scores,
        0.0
    )  # Remove keys that are supported only by harmonics

    return scores  # Return all 88 piano-key scores


# ============================================================
# CHOOSE THE NEXT KEY
# ============================================================

def choose_key(scores, previous_key):

    strongest_key = int(
        np.argmax(scores)
    )  # Start with the strongest raw piano-key score

    strongest_score = float(
        scores[strongest_key]
    )  # Get the strongest raw score

    if previous_key is None or strongest_score <= 0:
        return strongest_key  # Use the strongest key when no history exists

    key_indices = np.arange(
        PIANO_KEYS,
        dtype=np.float32
    )  # Create piano-key indices for distance calculations

    distances = np.abs(
        key_indices - float(previous_key)
    )  # Measure how far every key is from the previous note

    continuity = np.clip(
        1.0 - (distances / MAX_CONTINUITY_DISTANCE),
        0.0,
        1.0
    )  # Give nearby notes a small continuity advantage

    adjusted_scores = scores * (
        1.0 + CONTINUITY_STRENGTH * continuity
    )  # Gently prefer a nearby plausible continuation

    chosen_key = int(
        np.argmax(adjusted_scores)
    )  # Choose the best score after continuity is considered

    return chosen_key  # Return the selected piano key


# ============================================================
# ANALYZE ONE CHUNK
# ============================================================

def analyze_chunk(chunk, previous_key=None):

    if len(chunk) == 0:

        return np.zeros(
            PIANO_KEYS,
            dtype=np.float32
        ), previous_key  # Return silence for an empty chunk


    # --------------------------------------------------------
    # FIND THE PIANO KEY
    # --------------------------------------------------------

    copy_length = min(
        len(chunk),
        ANALYSIS_CHUNK_SIZE
    )  # Limit the analysis to one short time frame

    short_chunk = chunk[:copy_length].astype(
        np.float32
    )  # Copy the current audio frame for analysis

    if copy_length < ANALYSIS_CHUNK_SIZE:

        short_chunk = np.pad(
            short_chunk,
            (0, ANALYSIS_CHUNK_SIZE - copy_length)
        ).astype(
            np.float32
        )  # Pad the final short frame so it matches the normal frame length

    windowed_chunk = (
        short_chunk
        * FFT_WINDOW
    )  # Apply a window that matches the actual short time frame

    padded_chunk = np.zeros(
        FFT_SIZE,
        dtype=np.float32
    )  # Create the larger zero-padded FFT input buffer

    start_index = (
        FFT_SIZE - ANALYSIS_CHUNK_SIZE
    ) // 2  # Center the short frame inside the larger FFT window

    padded_chunk[
        start_index:start_index + ANALYSIS_CHUNK_SIZE
    ] = windowed_chunk  # Place the windowed audio in the center of the FFT buffer

    windowed = padded_chunk  # Use the centered zero-padded frame for the FFT

    spectrum = np.abs(
        rfft(windowed)
    )  # Calculate the FFT magnitude

    maximum = np.max(
        spectrum
    )  # Find the strongest frequency

    if maximum <= 0:

        return np.zeros(
            PIANO_KEYS,
            dtype=np.float32
        ), previous_key  # Return silence when the FFT has no energy

    spectrum = (
        spectrum / maximum
    )  # Normalize the spectrum so song loudness does not change pitch selection

    scores = score_all_piano_keys(
        spectrum
    )  # Calculate the strength of all 88 piano keys

    strongest_value = float(
        np.max(scores)
    )  # Get the strongest piano-key score

    if strongest_value < NOTE_THRESHOLD:

        return np.zeros(
            PIANO_KEYS,
            dtype=np.float32
        ), previous_key  # Ignore weak detections instead of showing false bars

    strongest_key = choose_key(
        scores,
        previous_key
    )  # Choose the best current note while preserving reasonable continuity

    # --------------------------------------------------------
    # MEASURE THE AUDIO VOLUME
    # --------------------------------------------------------

    rms_volume = float(
        np.sqrt(
            np.mean(
                chunk.astype(np.float32) ** 2
            )
        )
    )  # Measure the actual audio volume of this chunk

    volume_value = min(
        rms_volume / VOLUME_REFERENCE,
        1.0
    )  # Convert the RMS volume into a 0-to-1 bar height value

    # --------------------------------------------------------
    # PUT THE VOLUME ON THE DETECTED PIANO KEY
    # --------------------------------------------------------

    one_note = np.zeros(
        PIANO_KEYS,
        dtype=np.float32
    )  # Create a frame containing no notes yet

    one_note[
        strongest_key
    ] = volume_value  # Put the volume level on the detected piano key

    return one_note, strongest_key  # Return the note frame and remember it for the next frame


# ============================================================
# KEEP ONLY ONE NOTE
# ============================================================

def keep_one_note(note_matrix):

    if len(note_matrix) == 0:

        return note_matrix  # Return immediately if there are no frames

    result = np.zeros_like(
        note_matrix
    )  # Create an empty result matrix

    strongest_keys = np.argmax(
        note_matrix,
        axis=1
    )  # Find the strongest key in every frame

    strongest_values = np.max(
        note_matrix,
        axis=1
    )  # Get the strength of the strongest key

    frame_indices = np.arange(
        len(note_matrix)
    )  # Create frame indices

    valid_frames = (
        strongest_values >= NOTE_THRESHOLD
    )  # Only keep real note detections

    result[
        frame_indices[valid_frames],
        strongest_keys[valid_frames]
    ] = strongest_values[
        valid_frames
    ]  # Keep only the strongest note

    return result  # Return the one-note-per-frame result


# ============================================================
# SMOOTH THE NOTE DATA
# ============================================================

def refine_note_matrix(note_matrix):

    if len(note_matrix) == 0:

        return note_matrix  # Return immediately if there are no frames

    smoothed = note_matrix.copy()  # Copy the detected notes

    if len(note_matrix) >= 3:

        smoothed[1:-1] = (
            note_matrix[:-2]
            * 0.20
            + note_matrix[1:-1]
            * 0.60
            + note_matrix[2:]
            * 0.20
        )  # Smooth gently without blurring fast piano notes too much

    smoothed = keep_one_note(
        smoothed
    )  # Keep only one note after smoothing

    return smoothed  # Return the refined data


# ============================================================
# STREAMING BACKGROUND ANALYSIS
# ============================================================

def analyze_song(audio_path, cache_source_path, state):

    try:

        cached = load_cache(
            cache_source_path
        )  # Check whether this song already has cached analysis

        if cached is not None:

            matrix, duration = cached  # Unpack cached data

            with state.lock:

                state.fast_matrix = matrix  # Make cached data available immediately

                state.refined_matrix = matrix  # Cached data is already refined

                state.analyzed_frames = len(
                    matrix
                )  # Mark every frame as ready

                state.song_duration = duration  # Restore the duration

                state.finished = True  # Mark analysis as finished

                state.cache_loaded = True  # Remember that cache was used

            return  # No new analysis is necessary

        with sf.SoundFile(
            audio_path
        ) as audio_file:

            native_sample_rate = audio_file.samplerate  # Read the WAV sample rate

            total_samples = len(
                audio_file
            )  # Get the total number of samples

            duration = (
                total_samples / native_sample_rate
            )  # Calculate the song duration

            total_frames = int(
                np.ceil(
                    total_samples
                    / ANALYSIS_CHUNK_SIZE
                )
            )  # Calculate the number of analysis frames

            fast_matrix = np.zeros(
                (total_frames, PIANO_KEYS),
                dtype=np.float32
            )  # Allocate only the small note matrix

            with state.lock:

                state.fast_matrix = fast_matrix  # Publish the matrix immediately

                state.song_duration = duration  # Publish the duration

            previous_key = None  # Remember the last detected piano note

            for frame_index in range(total_frames):

                if state.stop_event.is_set():

                    return  # Stop immediately if the visualizer is closing

                chunk = audio_file.read(
                    ANALYSIS_CHUNK_SIZE,
                    dtype="float32",
                    always_2d=False
                )  # Read only one small piece of the song

                if chunk.ndim > 1:

                    chunk = np.mean(
                        chunk,
                        axis=1
                    ).astype(
                        np.float32
                    )  # Convert stereo audio to mono for note analysis

                if native_sample_rate != SAMPLE_RATE:

                    raise RuntimeError(
                        "The converted WAV has an unexpected sample rate."
                    )  # Prevent incorrect frequency analysis

                scores, previous_key = analyze_chunk(
                    chunk,
                    previous_key
                )  # Analyze this short audio block and continue the note line

                fast_matrix[
                    frame_index
                ] = scores  # Store this frame's note data

                with state.lock:

                    state.analyzed_frames = (
                        frame_index + 1
                    )  # Publish this frame immediately

        refined_matrix = refine_note_matrix(
            fast_matrix
        )  # Refine the completed note matrix

        with state.lock:

            state.refined_matrix = refined_matrix  # Publish refined data

        save_cache(
            cache_source_path,
            refined_matrix,
            duration
        )  # Save the analysis for future runs

        with state.lock:

            state.finished = True  # Mark analysis as complete

    except Exception as error:

        with state.lock:

            state.error = str(
                error
            )  # Store the analysis error

            state.finished = True  # Stop the startup wait


# ============================================================
# GET CURRENT NOTE
# ============================================================

def get_current_note(state, current_time):

    with state.lock:

        refined_matrix = state.refined_matrix  # Get refined analysis

        fast_matrix = state.fast_matrix  # Get fast analysis

        analyzed_frames = state.analyzed_frames  # Get ready frame count

    frame_index = int(
        current_time / state.chunk_duration
    )  # Convert playback time into a frame index

    if refined_matrix is not None:

        if frame_index < len(refined_matrix):

            return refined_matrix[
                frame_index
            ]  # Use refined data when available

    if fast_matrix is not None:

        if frame_index < analyzed_frames:

            return fast_matrix[
                frame_index
            ]  # Otherwise use the fast data

    return np.zeros(
        PIANO_KEYS,
        dtype=np.float32
    )  # Return silence when the frame is not ready


# ============================================================
# SONG SELECTION
# ============================================================

def bring_visualizer_to_front(screen):
    if os.name != "nt":
        return  # The Windows foreground APIs below are only needed on Windows

    try:
        wm_info = pygame.display.get_wm_info()  # Get the native Windows handle for the Pygame window
        hwnd = wm_info.get("window")  # Read the Pygame window handle

        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 3)  # Keep the normal decorated window maximized
            ctypes.windll.user32.BringWindowToTop(hwnd)  # Move the visualizer above PyCharm
            ctypes.windll.user32.SetForegroundWindow(hwnd)  # Give the visualizer keyboard and mouse focus
            ctypes.windll.user32.SetFocus(hwnd)  # Give the visualizer the active input focus
    except Exception:
        pass  # Do not stop the visualizer if Windows refuses a focus request


# Keep the song picker in its own Tkinter thread so Pygame keeps animating behind it.
_song_picker_thread = None  # Store the background file-picker thread
_song_picker_result = None  # Store the selected song when the dialog closes
_song_picker_open = False  # Track whether the song picker is currently open
_song_picker_lock = threading.Lock()  # Protect the picker state shared with the Pygame loop

# Remember the last folder used by each picker separately.  This prevents the image
# picker from changing the folder that the song picker opens in (and vice versa).
_picker_locations_file = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "file_picker_locations.json",
)
_picker_locations = {"song": "", "image": ""}

try:
    if os.path.exists(_picker_locations_file):
        with open(_picker_locations_file, "r", encoding="utf-8") as _picker_file:
            _saved_picker_locations = json.load(_picker_file)
        if isinstance(_saved_picker_locations, dict):
            for _picker_type in ("song", "image"):
                _saved_folder = _saved_picker_locations.get(_picker_type, "")
                if isinstance(_saved_folder, str) and os.path.isdir(_saved_folder):
                    _picker_locations[_picker_type] = _saved_folder
except Exception:
    pass  # Picker history is optional; never prevent the visualizer from starting.


def _get_picker_initial_dir(picker_type):
    folder = _picker_locations.get(picker_type, "")
    return folder if folder and os.path.isdir(folder) else None


def _remember_picker_folder(picker_type, selected_path):
    if not selected_path:
        return
    try:
        folder = os.path.dirname(os.path.abspath(selected_path))
        if not os.path.isdir(folder):
            return
        _picker_locations[picker_type] = folder
        with open(_picker_locations_file, "w", encoding="utf-8") as _picker_file:
            json.dump(_picker_locations, _picker_file, indent=2)
    except Exception:
        pass  # Remembering the folder is optional and must never break file selection.


def _run_song_picker():
    global _song_picker_result, _song_picker_open

    root = tk.Tk()  # Create a temporary Tkinter window
    root.withdraw()  # Hide the temporary Tkinter window
    filename = ""  # Start with no selected song in case the dialog is cancelled

    try:
        root.attributes("-topmost", True)  # Keep the file picker in front while choosing the song
        root.update()  # Apply the foreground setting before opening the dialog
        filename = filedialog.askopenfilename(
            parent=root,
            title="Select a song",
            initialdir=_get_picker_initial_dir("song"),
            filetypes=[
                ("Audio Files", "*.mp3 *.wav *.flac *.ogg *.m4a"),
                ("All Files", "*.*")
            ]
        )  # Show the song-selection dialog
    finally:
        root.destroy()  # Close the temporary Tkinter window even if the dialog fails
        if filename:
            _remember_picker_folder("song", filename)
        with _song_picker_lock:
            _song_picker_result = filename  # Publish the result to the Pygame loop
            _song_picker_open = False  # Tell the Pygame loop that the dialog is finished


def select_audio_file():
    # Create a temporary Tkinter window for the initial song selection.
    root = tk.Tk()
    root.withdraw()
    filename = ""
    try:
        root.attributes("-topmost", True)
        root.update()
        filename = filedialog.askopenfilename(
            parent=root,
            title="Select a song",
            initialdir=_get_picker_initial_dir("song"),
            filetypes=[
                ("Audio Files", "*.mp3 *.wav *.flac *.ogg *.m4a"),
                ("All Files", "*.*")
            ]
        )
    finally:
        root.destroy()
    if filename:
        _remember_picker_folder("song", filename)
    return filename


def select_audio_file_async():
    global _song_picker_thread, _song_picker_result, _song_picker_open
    with _song_picker_lock:
        if _song_picker_open:
            return False  # Do not open a second song picker while one is already open
        _song_picker_result = None  # Clear the previous picker result
        _song_picker_open = True  # Mark the picker as open before starting its thread
    _song_picker_thread = threading.Thread(
        target=_run_song_picker,
        daemon=True,
    )  # Run the blocking dialog away from the Pygame loop
    _song_picker_thread.start()
    return True  # Tell the caller that a picker was started


# Keep the image picker in its own Tkinter thread too, so opening the
# image-selection dialog never stops the Pygame visualizer loop.
_image_picker_thread = None
_image_picker_result = None
_image_picker_open = False
_image_picker_lock = threading.Lock()


def _run_image_picker():
    global _image_picker_result, _image_picker_open

    root = tk.Tk()
    root.withdraw()
    filename = ""

    try:
        root.attributes("-topmost", True)
        root.update()
        filename = filedialog.askopenfilename(
            parent=root,
            title="Choose Visualizer Image",
            initialdir=_get_picker_initial_dir("image"),
            filetypes=[
                ("All supported image files", "*.*"),
                ("Common images", "*.png *.jpg *.jpeg *.jfif *.jpe *.bmp *.webp *.gif *.tif *.tiff *.ico *.ppm *.pgm *.pbm *.pnm *.avif"),
                ("All files", "*.*"),
            ],
        )
    finally:
        root.destroy()
        if filename:
            _remember_picker_folder("image", filename)
        with _image_picker_lock:
            _image_picker_result = filename
            _image_picker_open = False


def select_image_file_async():
    global _image_picker_thread, _image_picker_result, _image_picker_open
    with _image_picker_lock:
        if _image_picker_open:
            return False
        _image_picker_result = None
        _image_picker_open = True
    _image_picker_thread = threading.Thread(
        target=_run_image_picker,
        daemon=True,
    )
    _image_picker_thread.start()
    return True


def get_image_picker_result():
    global _image_picker_result
    with _image_picker_lock:
        if _image_picker_open:
            return None
        result = _image_picker_result
        _image_picker_result = None
        return result


def get_song_picker_result():
    global _song_picker_result
    with _song_picker_lock:
        if _song_picker_open:
            return None  # The user is still choosing a song
        result = _song_picker_result  # Read the finished dialog result
        _song_picker_result = None  # Consume the result so it is handled only once
        return result  # Return the selected path or empty string for Cancel


# ============================================================
# CONVERT AUDIO
# ============================================================

def prepare_playback_audio(source_path):

    import subprocess  # Run FFmpeg from Python

    command = [
        FFMPEG_PATH,
        "-y",
        "-i",
        source_path,
        "-ar",
        str(SAMPLE_RATE),
        "-ac",
        "2",
        CONVERTED_AUDIO
    ]  # Build the FFmpeg conversion command

    subprocess.run(
        command,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True
    )  # Convert the selected song to a 22050 Hz stereo WAV

    return CONVERTED_AUDIO  # Return the converted WAV path


# ============================================================
# WAIT FOR STARTUP ANALYSIS
# ============================================================

def wait_for_startup_analysis(state):

    while True:

        with state.lock:

            error = state.error  # Read any analysis error

            analyzed_frames = state.analyzed_frames  # Read ready frames

            finished = state.finished  # Check whether analysis finished

        if error is not None:

            return False  # Stop if analysis failed

        ready_seconds = (
            analyzed_frames
            * state.chunk_duration
        )  # Convert ready frames into seconds

        if ready_seconds >= STARTUP_READY_SECONDS:

            return True  # Enough analysis is ready

        if finished:

            return True  # The whole song has finished analyzing

        pygame.time.wait(
            10
        )  # Wait briefly before checking again


# ============================================================
# BASS BACKGROUND STATE
# ============================================================

bass_analysis_values = None  # Store normalized bass values without touching the piano-analysis state
bass_analysis_duration = 0.0  # Store how long each bass-analysis chunk represents
bass_analysis_ready = False  # Remember whether the separate bass analysis has finished
bass_analysis_error = None  # Store a bass-analysis error without affecting piano analysis
bass_analysis_thread = None  # Store the separate bass-analysis thread
bass_analysis_lock = threading.Lock()  # Protect the independent bass-analysis results
bass_analysis_stop = threading.Event()  # Allow the independent bass analysis to stop cleanly
smooth_bass_background = 0.0  # Store the smoothly changing background bass amount
bass_gradient_surface = None  # Reuse the tiny bass gradient surface every frame
bass_gradient_size = 0  # Remember the size of the reusable bass gradient


# ============================================================
# ANALYZE BASS FOR BACKGROUND
# ============================================================

def analyze_bass_background(audio_path):
    global bass_analysis_values  # Allow this function to store the bass values
    global bass_analysis_duration  # Allow this function to store the chunk duration
    global bass_analysis_ready  # Allow this function to mark bass analysis as ready
    global bass_analysis_error  # Allow this function to store a bass-analysis error

    try:
        audio, sample_rate = sf.read(
            audio_path,
            dtype="float32",
            always_2d=False
        )  # Read the playback audio independently from the piano-analysis thread

        if audio.ndim > 1:  # Check whether the audio contains multiple channels
            audio = np.mean(
                audio,
                axis=1
            )  # Convert multi-channel audio to mono like The Waver

        usable_length = (
            len(audio) // BASS_ANALYSIS_CHUNK_SIZE
        ) * BASS_ANALYSIS_CHUNK_SIZE  # Keep only complete 1000-sample bass chunks

        if usable_length <= 0:  # Check whether the song contains any complete bass chunks
            with bass_analysis_lock:  # Protect the independent bass-analysis state
                bass_analysis_values = []  # Publish an empty result safely
                bass_analysis_duration = BASS_ANALYSIS_CHUNK_SIZE / sample_rate  # Store the chunk duration
                bass_analysis_ready = True  # Mark the bass analysis as ready
            return  # Leave without touching the piano analysis

        audio_chunks = audio[:usable_length].reshape(
            -1,
            BASS_ANALYSIS_CHUNK_SIZE
        )  # Turn the song into a matrix so many bass FFTs can run together

        frequencies = np.fft.rfftfreq(
            BASS_ANALYSIS_CHUNK_SIZE,
            1.0 / sample_rate
        )  # Calculate the FFT frequencies once for every bass chunk

        bass_mask = (
            (frequencies >= BASS_LOW_FREQUENCY)
            & (frequencies <= BASS_HIGH_FREQUENCY)
        )  # Select exactly the 20–250 Hz bass range used by The Waver

        bass_values = []  # Store the raw bass strength for every 1000-sample chunk
        batch_size = 1024  # Process many chunks at once without creating a huge temporary array

        for start in range(0, len(audio_chunks), batch_size):  # Process the song in fast FFT batches
            if bass_analysis_stop.is_set():  # Check whether the visualizer has stopped
                return  # Leave immediately without touching the piano analysis

            batch = audio_chunks[
                start:start + batch_size
            ]  # Get one batch of 1000-sample bass chunks

            spectrum = np.fft.rfft(
                batch,
                axis=1
            )  # Calculate all FFTs in this batch at once for much faster processing

            magnitude = np.abs(
                spectrum[:, bass_mask]
            )  # Keep only the bass-frequency magnitudes needed by the background visual

            batch_strength = np.mean(
                magnitude,
                axis=1
            )  # Calculate one bass strength value for every chunk in the batch

            bass_values.extend(
                batch_strength.astype(float).tolist()
            )  # Append the batch results to the complete bass-value list

        max_bass = max(
            bass_values
        ) if bass_values else 1.0  # Find the strongest bass value in the song

        normalized_values = (
            [
                bass / max_bass
                for bass in bass_values
            ]
            if max_bass > 0
            else []
        )  # Normalize the bass values from zero to one exactly like The Waver

        with bass_analysis_lock:  # Protect the independent bass-analysis state
            bass_analysis_values = normalized_values  # Publish the finished bass values
            bass_analysis_duration = (
                BASS_ANALYSIS_CHUNK_SIZE / sample_rate
            )  # Store the exact duration represented by one bass chunk
            bass_analysis_ready = True  # Mark the bass analysis as ready immediately after the fast batch pass

    except Exception as error:
        with bass_analysis_lock:  # Protect the independent error state
            bass_analysis_error = error  # Remember the error without touching piano analysis
            bass_analysis_ready = False  # Keep the bass background disabled if analysis failed


# ============================================================

# GET BASS BACKGROUND LEVEL
# ============================================================

def get_bass_background_level(current_time):
    global smooth_bass_background  # Allow this function to smoothly change the background bass

    with bass_analysis_lock:  # Read only the independent bass-analysis state
        values = bass_analysis_values  # Get the finished normalized bass values
        chunk_duration = bass_analysis_duration  # Get the bass chunk duration
        ready = bass_analysis_ready  # Check whether bass analysis is ready

    if not ready or not values or chunk_duration <= 0:  # Check whether bass data is unavailable
        target_bass = 0.0  # Keep the background at idle until bass analysis is ready

    else:
        current_index = int(
            current_time / chunk_duration
        )  # Find the bass chunk matching the current playback time

        current_index = min(
            current_index,
            len(values) - 1
        )  # Keep the bass index inside the available data

        target_bass = float(
            values[current_index]
        )  # Get the normalized bass value for this moment

    if target_bass > smooth_bass_background:  # Check whether the bass is increasing
        smooth_bass_background += (
            target_bass
            - smooth_bass_background
        ) * BASS_ATTACK  # Smoothly rise toward the new bass value
    else:
        smooth_bass_background += (
            target_bass
            - smooth_bass_background
        ) * BASS_RELEASE  # Smoothly fall toward the new bass value

    smooth_bass_background = float(
        np.clip(
            smooth_bass_background,
            0.0,
            1.0
        )
    )  # Keep the smooth bass level between zero and one

    return smooth_bass_background  # Return the smoothly changing bass level


# ============================================================
# DRAW BASS-REACTIVE BACKGROUND
# ============================================================

def draw_bass_background(screen, bass_level, peak_x=None, bass_opacity_setting=0.80, clear_screen=True):
    global bass_gradient_surface
    global bass_gradient_size

    if clear_screen:
        screen.fill(BACKGROUND_IDLE)  # Fill the whole screen only when no image is being used as a base layer

    height = screen.get_height()  # Read the current screen height
    width = screen.get_width()  # Read the current screen width
    glow_start_y = int(height * 0.25)  # Set the highest point the bass glow is allowed to reach
    glow_height = max(1, height - glow_start_y)  # Measure the vertical range available to the bass glow
    bass_level = float(np.clip(np.real(bass_level), 0.0, 1.0))  # Keep bass as a safe real value
    bass_opacity = float(
        np.clip(bass_opacity_setting, 0.0, 1.0)
    )  # Use the user's selected opacity directly; automatic color brightness sets the starting value

    growth = bass_level ** 0.65  # Make stronger bass use more upward travel
    active_glow_height = glow_height * growth  # Convert bass intensity into visible glow height

    if active_glow_height <= 0.5:  # Check whether the bass is too low to draw
        return  # Keep the idle background when the glow is effectively invisible

    # Use a tiny fixed gradient instead of calculating hundreds of screen rows every frame.
    gradient_height = 256  # Keep enough vertical samples for a visually seamless gradient

    if (
        bass_gradient_surface is None
        or bass_gradient_size != gradient_height
    ):
        bass_gradient_surface = pygame.Surface(
            (1, gradient_height),
            pygame.SRCALPHA
        )  # Create the reusable one-pixel gradient surface
        bass_gradient_size = gradient_height  # Remember the cached gradient size

    gradient_pixels = pygame.surfarray.pixels3d(bass_gradient_surface)  # Access RGB pixels as one NumPy array
    gradient_alpha = pygame.surfarray.pixels_alpha(bass_gradient_surface)  # Access alpha pixels as one NumPy array

    gradient_rows = np.arange(gradient_height, dtype=np.float32)  # Create all gradient positions at once
    screen_y = gradient_rows / (gradient_height - 1) * height  # Map the tiny gradient to the full screen height
    dynamic_start_y = height - active_glow_height  # Find where the bass glow starts
    position = (screen_y - dynamic_start_y) / max(1.0, active_glow_height)  # Find each row's normalized glow position
    glow_strength = np.clip(position, 0.0, 1.0) ** 1.25  # Fade smoothly from the top toward the stronger bottom
    effective_level = bass_level * glow_strength * bass_opacity  # Apply bass strength and automatic color-dependent opacity

    idle = np.asarray(BACKGROUND_IDLE, dtype=np.float32)  # Convert idle RGB to a vector for fast blending
    bass = np.asarray(SECONDARY_VIBE_COLOR, dtype=np.float32)  # Convert vibe RGB to a vector for fast blending
    colors = idle[:, None] + (bass[:, None] - idle[:, None]) * effective_level[None, :]  # Blend every row in one operation

    if clear_screen:
        gradient_pixels[0, :, :] = np.rint(colors).T.astype(np.uint8)  # Blend with the normal idle background when no image is underneath
        gradient_alpha[0, :] = 255  # Keep the normal background gradient fully opaque
    else:
        bass_color = np.asarray(SECONDARY_VIBE_COLOR, dtype=np.uint8)  # Use the current bass color as a transparent overlay
        gradient_pixels[0, :, :] = bass_color  # Put only the bass color into the overlay so the image remains visible underneath
        gradient_alpha[0, :] = np.clip(np.rint(effective_level * 255.0), 0, 255).astype(np.uint8)  # Fade the bass color over the image

    del gradient_pixels  # Release the RGB surface lock
    del gradient_alpha  # Release the alpha surface lock

    gradient = pygame.transform.scale(
        bass_gradient_surface,
        (width, height)
    )  # Stretch the tiny smooth gradient across the whole window
    screen.blit(gradient, (0, 0))  # Draw the completed bass background in one blit

# ============================================================
# MAIN VISUALIZER
# ============================================================

def _run_color_picker_window(screen):
    # Open the modern Colors window with true rounded outer corners.
    global CUSTOM_WAVE_COLOR
    global CUSTOM_BASS_COLOR
    global PRIMARY_VIBE_COLOR
    global SECONDARY_VIBE_COLOR

    import colorsys
    import ctypes
    import tkinter as tk
    from PIL import Image, ImageTk, ImageDraw, ImageFont

    # ============================================================
    # COLORS
    # ============================================================

    COLORS = {
        "background": "#101116",
        "titlebar": "#151720",
        "surface": "#181A21",
        "surface_hover": "#22252E",
        "text": "#F2F3F5",
        "muted": "#8F95A3",
        "border": "#2B2E38",
        "accent": "#FFFFFF",
    }

    # ============================================================
    # GET AUTOMATIC VIBE COLORS
    # ============================================================

    def get_vibe_colors():
        # Get the automatic colors for the current song.
        if (
            PRIMARY_VIBE_NAME == "acoustic"
            and SECONDARY_VIBE_NAME == "happy"
        ):
            return (
                ACOUSTIC_HAPPY_COMBO_COLORS.get(
                    PRIMARY_VIBE_NAME, (255, 255, 255)
                ),
                ACOUSTIC_HAPPY_COMBO_COLORS.get(
                    SECONDARY_VIBE_NAME, BACKGROUND_BASS
                ),
            )

        wave_color = VIBE_COLORS.get(
            PRIMARY_VIBE_NAME,
            (255, 255, 255)
        )

        bass_color = VIBE_COLORS.get(
            SECONDARY_VIBE_NAME,
            BACKGROUND_BASS
        )

        return wave_color, bass_color

    # ============================================================
    # INITIAL COLORS
    # ============================================================

    original_wave, original_bass = get_vibe_colors()

    classic_wave = (255, 255, 255)
    classic_bass = BACKGROUND_BASS

    pending_wave = (
        tuple(CUSTOM_WAVE_COLOR)
        if CUSTOM_WAVE_COLOR is not None
        else tuple(original_wave)
    )

    pending_bass = (
        tuple(CUSTOM_BASS_COLOR)
        if CUSTOM_BASS_COLOR is not None
        else tuple(original_bass)
    )

    # Remember the colors from before opening the picker so Cancel/Close can restore them.
    preview_original_wave = tuple(PRIMARY_VIBE_COLOR)
    preview_original_bass = tuple(SECONDARY_VIBE_COLOR)
    preview_original_custom_wave = (
        tuple(CUSTOM_WAVE_COLOR)
        if CUSTOM_WAVE_COLOR is not None
        else None
    )
    preview_original_custom_bass = (
        tuple(CUSTOM_BASS_COLOR)
        if CUSTOM_BASS_COLOR is not None
        else None
    )

    # ============================================================
    # WINDOW SETTINGS
    # ============================================================

    WINDOW_WIDTH = 430
    WINDOW_HEIGHT = 510

    # This controls the actual outer corner roundness.
    WINDOW_RADIUS = 18

    # ============================================================
    # CREATE THE SINGLE TK ROOT
    # ============================================================

    # Use Tk() so another unwanted white "tk" window is not created.
    root = tk.Tk()

    root.title("Colors")

    root.geometry(
        f"{WINDOW_WIDTH}x{WINDOW_HEIGHT}"
    )

    root.resizable(
        False,
        False
    )

    # Remove the normal Windows title bar.
    root.overrideredirect(True)

    # Use the actual window background.
    root.configure(
        bg=COLORS["background"]
    )

    # Keep the picker above the visualizer.
    root.attributes(
        "-topmost",
        True
    )

    # ============================================================
    # CENTER WINDOW
    # ============================================================

    root.update_idletasks()

    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()

    window_x = (
        screen_width - WINDOW_WIDTH
    ) // 2

    window_y = (
        screen_height - WINDOW_HEIGHT
    ) // 2

    root.geometry(
        f"{WINDOW_WIDTH}x{WINDOW_HEIGHT}"
        f"+{window_x}+{window_y}"
    )

    # ============================================================
    # TRUE WINDOWS ROUNDED CORNERS
    # ============================================================

    def apply_rounded_window():
        # Get the native Windows handle of the Tk window.
        hwnd = root.winfo_id()

        # Windows CreateRoundRectRgn uses the diameter
        # for the corner curvature.
        diameter = WINDOW_RADIUS * 2

        # Create an actual Windows rounded rectangle region.
        rounded_region = ctypes.windll.gdi32.CreateRoundRectRgn(
            0,
            0,
            WINDOW_WIDTH + 1,
            WINDOW_HEIGHT + 1,
            diameter,
            diameter
        )

        # Apply that region to the entire window.
        # Everything outside the rounded shape is clipped away.
        ctypes.windll.user32.SetWindowRgn(
            hwnd,
            rounded_region,
            True
        )

    # Apply the rounded region after the window exists.
    root.update_idletasks()

    apply_rounded_window()

    # ============================================================
    # MAIN WINDOW FRAME
    # ============================================================

    main_frame = tk.Frame(
        root,
        bg=COLORS["background"],
        bd=0,
        highlightthickness=0,
    )

    main_frame.place(
        x=0,
        y=0,
        width=WINDOW_WIDTH,
        height=WINDOW_HEIGHT
    )

    # ============================================================
    # TITLE BAR
    # ============================================================

    TITLEBAR_HEIGHT = 42

    titlebar = tk.Frame(
        main_frame,
        bg=COLORS["titlebar"],
        bd=0,
        highlightthickness=0,
    )

    titlebar.place(
        x=0,
        y=0,
        width=WINDOW_WIDTH,
        height=TITLEBAR_HEIGHT
    )

    # ============================================================
    # WINDOW DRAGGING
    # ============================================================

    drag_data = {
        "x": 0,
        "y": 0
    }

    def start_drag(event):
        # Remember where the mouse was pressed.
        drag_data["x"] = event.x_root
        drag_data["y"] = event.y_root

    def drag_window(event):
        # Calculate how far the mouse moved.
        delta_x = (
            event.x_root
            - drag_data["x"]
        )

        delta_y = (
            event.y_root
            - drag_data["y"]
        )

        # Get the current window position.
        current_x = root.winfo_x()
        current_y = root.winfo_y()

        # Move the window.
        root.geometry(
            f"+{current_x + delta_x}"
            f"+{current_y + delta_y}"
        )

        # Remember the new mouse position.
        drag_data["x"] = event.x_root
        drag_data["y"] = event.y_root

    titlebar.bind(
        "<Button-1>",
        start_drag
    )

    titlebar.bind(
        "<B1-Motion>",
        drag_window
    )

    # ============================================================
    # TITLE ICON
    # ============================================================

    title_icon = tk.Label(
        titlebar,
        text="◢",
        bg=COLORS["titlebar"],
        fg="#A7B0FF",
        font=("Segoe UI", 12),
        bd=0,
    )

    title_icon.place(
        x=18,
        y=21,
        anchor="center"
    )

    # Allow dragging from the icon too.
    title_icon.bind(
        "<Button-1>",
        start_drag
    )

    title_icon.bind(
        "<B1-Motion>",
        drag_window
    )

    # ============================================================
    # TITLE
    # ============================================================

    title_label = tk.Label(
        titlebar,
        text="Colors",
        bg=COLORS["titlebar"],
        fg=COLORS["text"],
        font=("Segoe UI", 10),
        bd=0,
    )

    title_label.place(
        x=45,
        y=21,
        anchor="w"
    )

    title_label.bind(
        "<Button-1>",
        start_drag
    )

    title_label.bind(
        "<B1-Motion>",
        drag_window
    )

    # ============================================================
    # TITLE BAR BUTTON
    # ============================================================

    def make_title_button(
        text,
        x_position,
        command
    ):
        # Create a custom title-bar button.
        button = tk.Label(
            titlebar,
            text=text,
            bg=COLORS["titlebar"],
            fg=COLORS["muted"],
            font=("Segoe UI", 10),
            width=3,
            height=1,
            bd=0,
            cursor="hand2",
        )

        button.place(
            x=x_position,
            y=21,
            anchor="center"
        )

        def on_enter(_event):
            # Highlight the button.
            button.configure(
                bg=COLORS["surface_hover"],
                fg=COLORS["text"]
            )

        def on_leave(_event):
            # Restore the normal appearance.
            button.configure(
                bg=COLORS["titlebar"],
                fg=COLORS["muted"]
            )

        button.bind(
            "<Enter>",
            on_enter
        )

        button.bind(
            "<Leave>",
            on_leave
        )

        button.bind(
            "<Button-1>",
            lambda _event: command()
        )

        return button

    # ============================================================
    # CLOSE / MINIMIZE
    # ============================================================

    def close_window():
        # Close without applying changes.
        cancel_image_color_pick()
        restore_preview()
        root.destroy()

    def minimize_window():
        # Temporarily hide the window.
        root.withdraw()

    make_title_button(
        "×",
        WINDOW_WIDTH - 20,
        close_window
    )

    make_title_button(
        "—",
        WINDOW_WIDTH - 55,
        minimize_window
    )

    # ============================================================
    # CONTENT
    # ============================================================

    content = tk.Frame(
        main_frame,
        bg=COLORS["background"],
        bd=0,
        highlightthickness=0,
    )

    content.place(
        x=0,
        y=TITLEBAR_HEIGHT,
        width=WINDOW_WIDTH,
        height=WINDOW_HEIGHT - TITLEBAR_HEIGHT
    )

    # ============================================================
    # HEADER
    # ============================================================

    header = tk.Frame(
        content,
        bg=COLORS["background"],
        bd=0,
    )

    header.pack(
        fill="x",
        padx=20,
        pady=(10, 5)
    )

    heading = tk.Label(
        header,
        text="Colors",
        bg=COLORS["background"],
        fg=COLORS["text"],
        font=("Segoe UI", 17, "bold"),
        anchor="w",
    )

    heading.pack(
        anchor="w"
    )

    subtitle = tk.Label(
        header,
        text="Choose the colors used by the visualizer",
        bg=COLORS["background"],
        fg=COLORS["muted"],
        font=("Segoe UI", 8),
        anchor="w",
    )

    subtitle.pack(
        anchor="w",
        pady=(2, 0)
    )

    # ============================================================
    # TAB BAR
    # ============================================================

    # Create the tab bar as one Canvas so all three rectangles can have rounded corners.
    TAB_BAR_WIDTH = 170
    TAB_BAR_HEIGHT = 42
    TAB_RENDER_SCALE = 4  # Render the tabs at higher resolution so curved edges look smooth.

    tab_bar = tk.Canvas(
        content, width=TAB_BAR_WIDTH, height=TAB_BAR_HEIGHT,
        bg=COLORS["background"], highlightthickness=0, bd=0, cursor="hand2"
    )
    tab_bar.pack(anchor="w", padx=20, pady=(3, 8))

    tab_bar_image = None  # Keep the rendered tab image alive while the color picker is open.

    def redraw_tab_bar(active_tab, indicator_x=None):
        # Render the complete tab control at 4x resolution for smoother curved edges.
        nonlocal tab_bar_image

        scale = TAB_RENDER_SCALE
        image = Image.new("RGB", (TAB_BAR_WIDTH * scale, TAB_BAR_HEIGHT * scale), COLORS["background"])
        draw = ImageDraw.Draw(image)

        def rounded_box(x1, y1, x2, y2, radius, fill, outline=None, outline_width=1):
            # Draw a true rounded rectangle with PIL's anti-aliased high-resolution rendering.
            box = tuple(int(value * scale) for value in (x1, y1, x2, y2))
            draw.rounded_rectangle(
                box,
                radius=int(radius * scale),
                fill=fill,
                outline=outline,
                width=max(1, int(outline_width * scale)) if outline else 1,
            )

        # Make the outer container a true pill so it matches the pill-shaped tabs inside it.
        rounded_box(
            0.5, 0.5, TAB_BAR_WIDTH - 0.5, TAB_BAR_HEIGHT - 0.5,
            TAB_BAR_HEIGHT / 2, COLORS["surface"], COLORS["border"], 1
        )

        # Keep both tab backgrounds visible, then draw the active white pill separately.
        # This lets the active pill slide smoothly between Wave and Bass.
        wave_text = "#15161B" if active_tab == "wave" else COLORS["muted"]
        bass_text = "#15161B" if active_tab == "bass" else COLORS["muted"]

        # Give both tab areas a half-height radius so their ends are true semicircular pills.
        pill_radius = (TAB_BAR_HEIGHT - 4) / 2
        rounded_box(2, 2, 84, TAB_BAR_HEIGHT - 2, pill_radius, COLORS["surface"])
        rounded_box(86, 2, TAB_BAR_WIDTH - 2, TAB_BAR_HEIGHT - 2, pill_radius, COLORS["surface"])

        # Draw the active white pill at the requested horizontal position.
        if indicator_x is None:
            indicator_x = 2 if active_tab == "wave" else 86
        rounded_box(
            indicator_x, 2, indicator_x + 82, TAB_BAR_HEIGHT - 2,
            pill_radius, COLORS["accent"]
        )

        # Use a clean 15 px font and render text at final resolution to keep it sharp.
        font = ImageFont.truetype("segoeuib.ttf", 15) if active_tab == "wave" else ImageFont.truetype("segoeui.ttf", 15)
        bass_font = ImageFont.truetype("segoeuib.ttf", 15) if active_tab == "bass" else ImageFont.truetype("segoeui.ttf", 15)

        # Labels are drawn after downsampling so they remain crisp and centered.

        # Downsample the rounded shapes with Lanczos for smooth edges.
        image = image.resize((TAB_BAR_WIDTH, TAB_BAR_HEIGHT), Image.Resampling.LANCZOS)

        # Redraw the tab labels at final resolution so the font stays crisp instead of blurry.
        text_draw = ImageDraw.Draw(image)
        final_wave_font = ImageFont.truetype("segoeuib.ttf", 15) if active_tab == "wave" else ImageFont.truetype("segoeui.ttf", 15)
        final_bass_font = ImageFont.truetype("segoeuib.ttf", 15) if active_tab == "bass" else ImageFont.truetype("segoeui.ttf", 15)
        text_draw.text((43, 21), "Wave", fill=wave_text, font=final_wave_font, anchor="mm")
        text_draw.text((127, 21), "Bass", fill=bass_text, font=final_bass_font, anchor="mm")

        tab_bar_image = ImageTk.PhotoImage(image)
        tab_bar.delete("all")
        tab_bar.create_image(0, 0, image=tab_bar_image, anchor="nw")

    # ============================================================
    # TAB CONTENT
    # ============================================================

    tab_content = tk.Frame(
        content,
        bg=COLORS["background"],
        bd=0,
    )

    tab_content.pack(
        fill="both",
        expand=True,
        padx=20
    )

    wave_tab = tk.Frame(
        tab_content,
        bg=COLORS["background"],
        bd=0,
    )

    bass_tab = tk.Frame(
        tab_content,
        bg=COLORS["background"],
        bd=0,
    )

    picker_images = []

    # ============================================================
    # TAB SWITCHING
    # ============================================================

    tab_animation_id = None  # Store the scheduled tab animation so repeated clicks can be handled cleanly.

    def show_tab(tab_name, animate=True):
        # Hide both content panels before showing the selected one.
        nonlocal tab_animation_id
        wave_tab.pack_forget()
        bass_tab.pack_forget()
        if tab_name == "wave":
            wave_tab.pack(fill="both", expand=True)
        else:
            bass_tab.pack(fill="both", expand=True)

        # Move the white pill smoothly instead of instantly jumping to the new tab.
        if not animate:
            redraw_tab_bar(tab_name)
            return

        start_x = 2 if active_tab_state["name"] == "wave" else 86
        end_x = 2 if tab_name == "wave" else 86

        if tab_animation_id is not None:
            try:
                root.after_cancel(tab_animation_id)
            except Exception:
                pass
            tab_animation_id = None

        active_tab_state["name"] = tab_name
        active_tab_state["start_x"] = start_x
        active_tab_state["end_x"] = end_x
        active_tab_state["frame"] = 0

        def animate_indicator():
            # Advance the pill a small amount each frame for a smooth 180 ms slide.
            nonlocal tab_animation_id
            active_tab_state["frame"] += 1
            progress = min(active_tab_state["frame"] / 5.0, 1.0)

            # Ease in and out so the pill starts and stops naturally.
            eased = progress * progress * (3.0 - 2.0 * progress)
            current_x = active_tab_state["start_x"] + (active_tab_state["end_x"] - active_tab_state["start_x"]) * eased
            redraw_tab_bar(tab_name, current_x)

            if progress < 1.0:
                tab_animation_id = root.after(16, animate_indicator)
            else:
                tab_animation_id = None
                redraw_tab_bar(tab_name, active_tab_state["end_x"])

        animate_indicator()

    active_tab_state = {"name": "wave", "start_x": 2, "end_x": 2, "frame": 0}

    def on_tab_click(event):
        # Select Wave or Bass from the clicked half of the tab bar.
        show_tab("wave" if event.x < TAB_BAR_WIDTH / 2 else "bass", animate=True)

    tab_bar.bind("<Button-1>", on_tab_click)

    # ============================================================
    # SCREEN IMAGE COLOR PICKER
    # ============================================================

    def start_image_color_pick(target, callback):
        # Hide the Tk picker temporarily so the Pygame image is unobstructed.
        global _color_pick_request, _color_pick_target, _color_pick_result, _color_pick_callback
        with _color_pick_lock:
            _color_pick_request = True
            _color_pick_target = target
            _color_pick_result = None
            _color_pick_callback = callback
        root.withdraw()
        bring_visualizer_to_front(screen)
        root.after(30, poll_image_color_pick)

    def poll_image_color_pick():
        # Wait for the Pygame loop to report a picked pixel, then restore the picker.
        global _color_pick_result, _color_pick_request, _color_pick_target, _color_pick_callback
        with _color_pick_lock:
            result = _color_pick_result
            active = _color_pick_request
            callback = _color_pick_callback
            if result is not None:
                _color_pick_result = None
                _color_pick_request = False
                _color_pick_target = None
                _color_pick_callback = None
        if result is not None:
            root.deiconify()
            root.lift()
            root.attributes("-topmost", True)
            root.focus_force()
            if callback is not None:
                callback(tuple(result))
            return
        if active:
            root.after(30, poll_image_color_pick)

    def cancel_image_color_pick():
        # Cancel eyedropper mode if the color window is closed while it is active.
        global _color_pick_request, _color_pick_target, _color_pick_result, _color_pick_callback
        with _color_pick_lock:
            _color_pick_request = False
            _color_pick_target = None
            _color_pick_result = None
            _color_pick_callback = None

    # ============================================================
    # COLOR PICKER
    # ============================================================

    def build_picker(
        parent,
        title,
        initial_color,
        on_change
    ):
        # Store the color picker state.
        state = {
            "rgb": tuple(initial_color),
            "hue": 0.0,
            "sat": 1.0,
            "value": 1.0,
        }

        # Convert RGB to HSV.
        r, g, b = state["rgb"]

        h, s, v = colorsys.rgb_to_hsv(
            r / 255.0,
            g / 255.0,
            b / 255.0
        )

        state["hue"] = h
        state["sat"] = s
        state["value"] = v

        # --------------------------------------------------------
        # PICKER SIZE
        # --------------------------------------------------------

        PICKER_WIDTH = 372
        PICKER_HEIGHT = 178

        # --------------------------------------------------------
        # PICKER CARD
        # --------------------------------------------------------

        # Use a Canvas as the card itself so no rectangular Frame can cover the rounded corners.
        card = tk.Canvas(
            parent,
            bg=COLORS["background"],
            highlightthickness=0,
            bd=0,
            width=PICKER_WIDTH + 16,
            height=276,
        )

        card.pack(
            fill="x"
        )

        # Draw one clean anti-aliased rounded card instead of overlapping arcs and rectangles.
        card_width = PICKER_WIDTH + 16
        card_height = 276
        card_radius = 10
        card_scale = 4

        card_image = Image.new(
            "RGBA",
            (card_width * card_scale, card_height * card_scale),
            (0, 0, 0, 0),
        )
        card_draw = ImageDraw.Draw(card_image)
        card_draw.rounded_rectangle(
            (card_scale, card_scale,
             card_width * card_scale - card_scale,
             card_height * card_scale - card_scale),
            radius=card_radius * card_scale,
            fill=COLORS["surface"],
            outline=COLORS["border"],
            width=card_scale,
        )
        card_image = card_image.resize(
            (card_width, card_height),
            Image.Resampling.LANCZOS,
        )
        card_background_image = ImageTk.PhotoImage(card_image)
        card._background_image = card_background_image
        card.create_image(
            0, 0,
            anchor="nw",
            image=card_background_image,
            tags="card_background",
        )

        title_label = tk.Label(
            card,
            text=title,
            bg=COLORS["surface"],
            fg=COLORS["text"],
            font=("Segoe UI", 8, "bold"),
            anchor="w",
        )

        card.create_window(
            8, 7,
            anchor="nw",
            window=title_label,
            width=PICKER_WIDTH,
            height=16,
        )

        # --------------------------------------------------------
        # SATURATION / VALUE CANVAS
        # --------------------------------------------------------

        picker_canvas = tk.Canvas(
            card,
            width=PICKER_WIDTH,
            height=PICKER_HEIGHT,
            bg=COLORS["surface"],
            highlightthickness=0,
            bd=0,
        )

        card.create_window(
            8, 28,
            anchor="nw",
            window=picker_canvas,
            width=PICKER_WIDTH,
            height=PICKER_HEIGHT,
        )

        # --------------------------------------------------------
        # HUE CANVAS
        # --------------------------------------------------------

        hue_canvas = tk.Canvas(
            card,
            width=PICKER_WIDTH,
            height=18,
            bg=COLORS["surface"],
            highlightthickness=0,
            bd=0,
        )

        card.create_window(
            8, 213,
            anchor="nw",
            window=hue_canvas,
            width=PICKER_WIDTH,
            height=18,
        )

        # --------------------------------------------------------
        # INFO ROW
        # --------------------------------------------------------

        info_row = tk.Frame(
            card,
            bg=COLORS["surface"],
            bd=0,
        )

        card.create_window(
            8, 238,
            anchor="nw",
            window=info_row,
            width=PICKER_WIDTH,
            height=31,
        )

        swatch = tk.Canvas(
            info_row,
            width=60,
            height=24,
            bg=COLORS["surface"],
            highlightthickness=0,
            bd=0,
        )

        swatch.pack(
            side="left"
        )

        def make_swatch_image(rgb):
            # Render the current-color indicator at high resolution for smooth rounded corners.
            swatch_scale = 4
            swatch_width = 60
            swatch_height = 24
            swatch_radius = 6

            image = Image.new(
                "RGB",
                (
                    swatch_width * swatch_scale,
                    swatch_height * swatch_scale
                ),
                COLORS["surface"]
            )

            draw = ImageDraw.Draw(image)
            draw.rounded_rectangle(
                (
                    0,
                    0,
                    swatch_width * swatch_scale - 1,
                    swatch_height * swatch_scale - 1
                ),
                radius=swatch_radius * swatch_scale,
                fill=(
                    int(rgb[0]),
                    int(rgb[1]),
                    int(rgb[2])
                )
            )

            image = image.resize(
                (swatch_width, swatch_height),
                Image.Resampling.LANCZOS
            )

            return ImageTk.PhotoImage(image)

        swatch_image = make_swatch_image((255, 255, 255))
        picker_images.append(swatch_image)
        swatch.create_image(
            0,
            0,
            anchor="nw",
            image=swatch_image,
            tags="swatch_image"
        )

        rgb_label = tk.Label(
            info_row,
            text="RGB: 255, 255, 255",
            bg=COLORS["surface"],
            fg=COLORS["muted"],
            font=("Consolas", 8),
        )

        rgb_label.pack(
            side="left",
            padx=(26, 0)
        )

        hex_label = tk.Label(
            info_row,
            text="HEX: #FFFFFF",
            bg=COLORS["surface"],
            fg=COLORS["muted"],
            font=("Consolas", 8),
        )

        hex_label.pack(
            side="left",
            padx=(20, 0)
        )

        # --------------------------------------------------------
        # IMAGE EYEDROPPER
        # --------------------------------------------------------

        def apply_image_color(rgb):
            # Convert the sampled RGB color to HSV and commit it through the normal picker path.
            hue, saturation, value = colorsys.rgb_to_hsv(
                rgb[0] / 255.0,
                rgb[1] / 255.0,
                rgb[2] / 255.0,
            )
            update_picker(
                hue,
                saturation,
                value,
                commit=True,
                preview_color=True,
            )

        pick_color_button = tk.Button(
            info_row,
            text="Pick Color",
            command=lambda: start_image_color_pick(
                "wave" if title.lower().startswith("wave") else "bass",
                apply_image_color,
            ),
            bg=COLORS["surface_hover"],
            fg=COLORS["text"],
            activebackground="#303440",
            activeforeground=COLORS["text"],
            relief="flat",
            bd=0,
            highlightthickness=1,
            highlightbackground=COLORS["border"],
            highlightcolor=COLORS["border"],
            font=("Segoe UI", 8),
            cursor="hand2",
            padx=5,
        )
        pick_color_button.pack(
            side="right",
            padx=(6, 0),
            pady=1,
        )

        # --------------------------------------------------------
        # SATURATION / VALUE IMAGE
        # --------------------------------------------------------

        def make_picker_image():
            # Create the saturation/value gradient.
            image = Image.new(
                "RGB",
                (
                    PICKER_WIDTH,
                    PICKER_HEIGHT
                )
            )

            pixels = image.load()

            hue_rgb = colorsys.hsv_to_rgb(
                state["hue"],
                1.0,
                1.0
            )

            hue_r = int(
                hue_rgb[0] * 255
            )

            hue_g = int(
                hue_rgb[1] * 255
            )

            hue_b = int(
                hue_rgb[2] * 255
            )

            for y in range(PICKER_HEIGHT):
                value = (
                    1.0
                    - y / (PICKER_HEIGHT - 1)
                )

                for x in range(PICKER_WIDTH):
                    saturation = (
                        x / (PICKER_WIDTH - 1)
                    )

                    r = int(
                        255
                        * (
                            (1 - saturation)
                            + (
                                hue_r / 255.0
                                * saturation
                            )
                        )
                        * value
                    )

                    g = int(
                        255
                        * (
                            (1 - saturation)
                            + (
                                hue_g / 255.0
                                * saturation
                            )
                        )
                        * value
                    )

                    b = int(
                        255
                        * (
                            (1 - saturation)
                            + (
                                hue_b / 255.0
                                * saturation
                            )
                        )
                        * value
                    )

                    pixels[x, y] = (
                        r,
                        g,
                        b
                    )

            # Create a high-resolution mask so the picker corners stay smooth.
            mask_scale = 4
            mask = Image.new(
                "L",
                (PICKER_WIDTH * mask_scale, PICKER_HEIGHT * mask_scale),
                0
            )

            mask_draw = ImageDraw.Draw(
                mask
            )

            mask_draw.rounded_rectangle(
                (
                    0,
                    0,
                    PICKER_WIDTH * mask_scale - 1,
                    PICKER_HEIGHT * mask_scale - 1
                ),
                radius=9 * mask_scale,
                fill=255
            )

            # Downsample the mask to create anti-aliased edges.
            mask = mask.resize(
                image.size,
                Image.Resampling.LANCZOS
            )

            rounded = Image.new(
                "RGB",
                image.size,
                COLORS["surface"]
            )

            rounded.paste(
                image,
                (0, 0),
                mask
            )

            return ImageTk.PhotoImage(
                rounded
            )

        # --------------------------------------------------------
        # HUE IMAGE
        # --------------------------------------------------------

        def make_hue_image():
            # Create the rainbow hue strip.
            image = Image.new(
                "RGB",
                (
                    PICKER_WIDTH,
                    18
                )
            )

            pixels = image.load()

            for x in range(PICKER_WIDTH):
                hue = (
                    x / (PICKER_WIDTH - 1)
                )

                rgb = colorsys.hsv_to_rgb(
                    hue,
                    1.0,
                    1.0
                )

                color = (
                    int(rgb[0] * 255),
                    int(rgb[1] * 255),
                    int(rgb[2] * 255)
                )

                for y in range(18):
                    pixels[x, y] = color

            # Round the hue bar ends with a high-resolution anti-aliased mask.
            mask_scale = 4
            mask = Image.new(
                "L",
                (PICKER_WIDTH * mask_scale, 18 * mask_scale),
                0
            )

            mask_draw = ImageDraw.Draw(
                mask
            )

            mask_draw.rounded_rectangle(
                (
                    0,
                    0,
                    PICKER_WIDTH * mask_scale - 1,
                    18 * mask_scale - 1
                ),
                radius=8 * mask_scale,
                fill=255
            )

            # Downsample the mask to remove jagged corner pixels.
            mask = mask.resize(
                image.size,
                Image.Resampling.LANCZOS
            )

            rounded = Image.new(
                "RGB",
                image.size,
                COLORS["surface"]
            )

            rounded.paste(
                image,
                (0, 0),
                mask
            )

            return ImageTk.PhotoImage(
                rounded
            )

        # --------------------------------------------------------
        # MARKER
        # --------------------------------------------------------

        def refresh_marker(marker_hue=None, marker_sat=None, marker_value=None):
            # Keep the marker anchored to the last clicked color unless a click commits a new position.
            picker_canvas.delete(
                "picker_marker"
            )

            if marker_sat is None:
                marker_sat = state["sat"]
            if marker_value is None:
                marker_value = state["value"]

            marker_x = (
                marker_sat
                * (PICKER_WIDTH - 1)
            )

            marker_y = (
                (1.0 - marker_value)
                * (PICKER_HEIGHT - 1)
            )

            # Draw the outer white marker.
            picker_canvas.create_oval(
                marker_x - 7,
                marker_y - 7,
                marker_x + 7,
                marker_y + 7,
                outline="white",
                width=2,
                tags="picker_marker"
            )

            # Draw the inner dark marker.
            picker_canvas.create_oval(
                marker_x - 4,
                marker_y - 4,
                marker_x + 4,
                marker_y + 4,
                outline="#202127",
                width=1,
                tags="picker_marker"
            )

        # --------------------------------------------------------
        # UPDATE PICKER
        # --------------------------------------------------------

        def update_picker(
            hue=None,
            sat=None,
            value=None,
            commit=False,
            preview_color=True
        ):
            # Use temporary HSV values for hover previews without moving the anchored marker.
            render_hue = state["hue"] if hue is None else hue
            render_sat = state["sat"] if sat is None else sat
            render_value = state["value"] if value is None else value

            # Convert the requested HSV color to RGB.
            rgb_float = colorsys.hsv_to_rgb(
                render_hue,
                render_sat,
                render_value
            )

            rgb = (
                int(rgb_float[0] * 255),
                int(rgb_float[1] * 255),
                int(rgb_float[2] * 255)
            )

            # Commit the HSV position only after a click.
            if commit:
                state["hue"] = render_hue
                state["sat"] = render_sat
                state["value"] = render_value
                state["rgb"] = rgb

            # Update the color swatch with the hovered or committed color.
            swatch_image = make_swatch_image(rgb)
            picker_images.append(swatch_image)
            swatch.delete("swatch_image")
            swatch.create_image(
                0,
                0,
                anchor="nw",
                image=swatch_image,
                tags="swatch_image"
            )

            # Update RGB text.
            rgb_label.configure(
                text=(
                    f"RGB: {rgb[0]}, "
                    f"{rgb[1]}, "
                    f"{rgb[2]}"
                )
            )

            # Update HEX text.
            hex_label.configure(
                text=(
                    "HEX: #"
                    + "%02X%02X%02X" % rgb
                )
            )

            # Send the hover preview or committed color to the parent.
            if preview_color:
                on_change(rgb, commit)

            # Temporarily use the requested hue to rebuild the saturation/value gradient.
            old_hue = state["hue"]
            state["hue"] = render_hue
            picker_image = make_picker_image()
            state["hue"] = old_hue

            picker_images.append(
                picker_image
            )

            picker_canvas.delete(
                "picker_image"
            )

            picker_canvas.create_image(
                0,
                0,
                anchor="nw",
                image=picker_image,
                tags="picker_image"
            )

            # Rebuild the hue image so the hue bar stays current after a hue hover/click.
            hue_image = make_hue_image()

            picker_images.append(
                hue_image
            )

            hue_canvas.delete(
                "hue_image"
            )

            hue_canvas.create_image(
                0,
                0,
                anchor="nw",
                image=hue_image,
                tags="hue_image"
            )

            # Keep the marker anchored to the last committed click.
            refresh_marker()

        # --------------------------------------------------------
        # RESTORE HOVER PREVIEW
        # --------------------------------------------------------

        def restore_hover_preview():
            # Return the picker display to the last clicked/committed color.
            update_picker(
                state["hue"],
                state["sat"],
                state["value"],
                commit=False,
                preview_color=True
            )

        # --------------------------------------------------------
        # SATURATION / VALUE CONTROL
        # --------------------------------------------------------

        def get_sv_from_event(event):
            # Keep the mouse inside the picker.
            x = max(
                0,
                min(
                    PICKER_WIDTH - 1,
                    event.x
                )
            )

            y = max(
                0,
                min(
                    PICKER_HEIGHT - 1,
                    event.y
                )
            )

            return (
                x / (PICKER_WIDTH - 1),
                1.0 - y / (PICKER_HEIGHT - 1)
            )

        def preview_sv(event):
            # Preview the color under the cursor without moving the anchored marker.
            sat, value = get_sv_from_event(event)
            update_picker(
                state["hue"],
                sat,
                value,
                commit=False,
                preview_color=True
            )

        def commit_sv(event):
            # Anchor the picker point only when the user clicks.
            sat, value = get_sv_from_event(event)
            update_picker(
                state["hue"],
                sat,
                value,
                commit=True,
                preview_color=True
            )

        picker_canvas.bind(
            "<Button-1>",
            commit_sv
        )

        picker_canvas.bind(
            "<B1-Motion>",
            commit_sv
        )

        picker_canvas.bind(
            "<Motion>",
            preview_sv
        )

        picker_canvas.bind(
            "<Leave>",
            lambda _event: restore_hover_preview()
        )

        # --------------------------------------------------------
        # HUE CONTROL
        # --------------------------------------------------------

        def get_hue_from_event(event):
            # Keep the mouse inside the hue bar.
            x = max(
                0,
                min(
                    PICKER_WIDTH - 1,
                    event.x
                )
            )

            return x / (PICKER_WIDTH - 1)

        def preview_hue(event):
            # Preview the hue under the cursor without moving the anchored point.
            hue = get_hue_from_event(event)
            update_picker(
                hue,
                state["sat"],
                state["value"],
                commit=False,
                preview_color=True
            )

        def commit_hue(event):
            # Anchor the hue only when the user clicks.
            hue = get_hue_from_event(event)
            update_picker(
                hue,
                state["sat"],
                state["value"],
                commit=True,
                preview_color=True
            )

        hue_canvas.bind(
            "<Button-1>",
            commit_hue
        )

        hue_canvas.bind(
            "<B1-Motion>",
            commit_hue
        )

        hue_canvas.bind(
            "<Motion>",
            preview_hue
        )

        hue_canvas.bind(
            "<Leave>",
            lambda _event: restore_hover_preview()
        )

        # Create the initial picker.
        update_picker(
            state["hue"],
            state["sat"],
            state["value"],
            commit=False,
            preview_color=False
        )

        return card


    # ============================================================
    # COLOR CALLBACKS
    # ============================================================

    def wave_changed(color, commit=False):
        # Preview Wave color live, but only save it as pending after a click.
        nonlocal pending_wave
        global PRIMARY_VIBE_COLOR

        PRIMARY_VIBE_COLOR = tuple(color)
        if commit:
            pending_wave = tuple(color)

    def bass_changed(color, commit=False):
        # Preview Bass color live, but only save it as pending after a click.
        nonlocal pending_bass
        global SECONDARY_VIBE_COLOR

        SECONDARY_VIBE_COLOR = tuple(color)
        if commit:
            pending_bass = tuple(color)

    # ============================================================
    # REBUILD PICKERS
    # ============================================================

    def rebuild_pickers():
        # Rebuild both color picker tabs without changing the currently selected tab.
        nonlocal picker_images
        current_tab = "bass" if bass_tab.winfo_ismapped() else "wave"

        # Remove old Wave widgets.
        for child in wave_tab.winfo_children():
            child.destroy()

        # Remove old Bass widgets.
        for child in bass_tab.winfo_children():
            child.destroy()

        # Remove old image references.
        picker_images = []

        # Build Wave picker.
        build_picker(
            wave_tab,
            "Wave color",
            pending_wave,
            wave_changed
        )

        # Build Bass picker.
        build_picker(
            bass_tab,
            "Bass color",
            pending_bass,
            bass_changed
        )

        # Return to the tab that was active before rebuilding.
        show_tab(current_tab)

    # Build the initial pickers.
    rebuild_pickers()

    # ============================================================
    # DEFAULT
    # ============================================================

    def use_default():
        # Restore the automatic vibe colors immediately in the live preview.
        nonlocal pending_wave
        nonlocal pending_bass
        global PRIMARY_VIBE_COLOR
        global SECONDARY_VIBE_COLOR

        pending_wave = tuple(
            original_wave
        )

        pending_bass = tuple(
            original_bass
        )

        PRIMARY_VIBE_COLOR = tuple(
            pending_wave
        )
        SECONDARY_VIBE_COLOR = tuple(
            pending_bass
        )

        rebuild_pickers()

    # ============================================================
    # CLASSIC
    # ============================================================

    def use_classic():
        # Restore the original Test 15 colors.
        nonlocal pending_wave
        nonlocal pending_bass

        pending_wave = tuple(
            classic_wave
        )

        pending_bass = tuple(
            classic_bass
        )

        rebuild_pickers()

    # ============================================================
    # ACCEPT
    # ============================================================

    def restore_preview():
        # Restore the colors that were active before the picker opened.
        global CUSTOM_WAVE_COLOR
        global CUSTOM_BASS_COLOR
        global PRIMARY_VIBE_COLOR
        global SECONDARY_VIBE_COLOR

        CUSTOM_WAVE_COLOR = preview_original_custom_wave
        CUSTOM_BASS_COLOR = preview_original_custom_bass
        PRIMARY_VIBE_COLOR = preview_original_wave
        SECONDARY_VIBE_COLOR = preview_original_bass

    def accept():
        # Save the selected colors globally.
        global CUSTOM_WAVE_COLOR
        global CUSTOM_BASS_COLOR
        global PRIMARY_VIBE_COLOR
        global SECONDARY_VIBE_COLOR
        global _bass_color_changed

        bass_color_was_changed = tuple(pending_bass) != tuple(preview_original_bass)

        # Remove the custom Wave override if it matches automatic.
        if tuple(pending_wave) == tuple(
            original_wave
        ):
            CUSTOM_WAVE_COLOR = None
        else:
            CUSTOM_WAVE_COLOR = tuple(
                pending_wave
            )

        # Remove the custom Bass override if it matches automatic.
        if tuple(pending_bass) == tuple(
            original_bass
        ):
            CUSTOM_BASS_COLOR = None
        else:
            CUSTOM_BASS_COLOR = tuple(
                pending_bass
            )

        # Apply the selected Wave color.
        PRIMARY_VIBE_COLOR = tuple(
            pending_wave
        )

        # Apply the selected Bass color.
        SECONDARY_VIBE_COLOR = tuple(
            pending_bass
        )

        if bass_color_was_changed:
            _bass_color_changed = True

        # Close the picker.
        root.destroy()

    # ============================================================
    # CANCEL
    # ============================================================

    def cancel():
        # Close without applying changes.
        cancel_image_color_pick()
        restore_preview()
        root.destroy()

    # ============================================================
    # BUTTON HELPER
    # ============================================================

    def modern_button(
            parent,
            text,
            command,
            primary=False
    ):
        # Select the normal button colors.
        if primary:
            normal_bg = COLORS["accent"]
            normal_fg = "#15161B"
        else:
            normal_bg = COLORS["surface"]
            normal_fg = COLORS["text"]

        # Create the button as a Canvas.
        button_width = 78
        button_height = 30

        button = tk.Canvas(
            parent,
            width=button_width,
            height=button_height,
            bg=COLORS["background"],
            highlightthickness=0,
            bd=0,
            cursor="hand2"
        )

        button.pack(
            side="left",
            padx=(0, 5)
        )

        # Draw the pill at a higher resolution for smoother anti-aliased edges.
        scale = 4

        from PIL import Image, ImageDraw, ImageTk

        normal_image = Image.new(
            "RGBA",
            (
                button_width * scale,
                button_height * scale
            ),
            (0, 0, 0, 0)
        )

        draw = ImageDraw.Draw(normal_image)

        draw.rounded_rectangle(
            (
                0,
                0,
                button_width * scale - 1,
                button_height * scale - 1
            ),
            radius=button_height * scale // 2,
            fill=normal_bg
        )

        # Resize down with high-quality filtering for smooth corners.
        normal_image = normal_image.resize(
            (button_width, button_height),
            Image.Resampling.LANCZOS
        )

        normal_photo = ImageTk.PhotoImage(normal_image)

        # Create the hover version the same way.
        hover_image = Image.new(
            "RGBA",
            (
                button_width * scale,
                button_height * scale
            ),
            (0, 0, 0, 0)
        )

        hover_draw = ImageDraw.Draw(hover_image)

        if primary:
            hover_bg = "#E5E6E8"
        else:
            hover_bg = COLORS["surface_hover"]

        hover_draw.rounded_rectangle(
            (
                0,
                0,
                button_width * scale - 1,
                button_height * scale - 1
            ),
            radius=button_height * scale // 2,
            fill=hover_bg
        )

        hover_image = hover_image.resize(
            (button_width, button_height),
            Image.Resampling.LANCZOS
        )

        hover_photo = ImageTk.PhotoImage(hover_image)

        # Put the rounded image and text together.
        button.create_image(
            0,
            0,
            anchor="nw",
            image=normal_photo,
            tags="button_image"
        )

        button.create_text(
            button_width // 2,
            button_height // 2,
            text=text,
            fill=normal_fg,
            font=("Segoe UI", 12),
            tags="button_text"
        )

        # Keep references so the images do not disappear.
        button.normal_photo = normal_photo
        button.hover_photo = hover_photo

        def on_enter(_event):
            # Show the smoother hover button.
            button.itemconfigure(
                "button_image",
                image=button.hover_photo
            )

        def on_leave(_event):
            # Restore the normal button.
            button.itemconfigure(
                "button_image",
                image=button.normal_photo
            )

        button.bind(
            "<Enter>",
            on_enter
        )

        button.bind(
            "<Leave>",
            on_leave
        )

        button.bind(
            "<Button-1>",
            lambda _event: command()
        )

        return button

    # ============================================================
    # BOTTOM BUTTON BAR
    # ============================================================

    bottom_bar = tk.Frame(
        content,
        bg=COLORS["background"],
        bd=0,
    )

    bottom_bar.pack(
        fill="x",
        padx=20,
        pady=(7, 18)
    )

    # Left buttons.
    modern_button(
        bottom_bar,
        "Default",
        use_default
    )

    modern_button(
        bottom_bar,
        "Classic",
        use_classic
    )

    # Empty space between button groups.
    spacer = tk.Frame(
        bottom_bar,
        bg=COLORS["background"]
    )

    spacer.pack(
        side="left",
        fill="x",
        expand=True
    )

    # Right buttons.
    modern_button(
        bottom_bar,
        "OK",
        accept,
        primary=True
    )

    modern_button(
        bottom_bar,
        "Cancel",
        cancel
    )

    # ============================================================
    # INITIAL TAB
    # ============================================================

    show_tab("wave")

    # ============================================================
    # WINDOW CLOSE
    # ============================================================

    root.protocol(
        "WM_DELETE_WINDOW",
        cancel
    )

    # ============================================================
    # FINAL SETUP
    # ============================================================

    root.update_idletasks()

    # Reapply the Windows region after all widgets are created.
    apply_rounded_window()

    root.lift()

    root.focus_force()

    root.attributes(
        "-topmost",
        True
    )

    # Start the color picker event loop in this worker thread.
    root.mainloop()


# Keep a reference to the color-picker thread so only one picker window opens at a time.
_color_picker_thread = None
_bass_color_changed = False

# Cross-thread state used by the color-picker eyedropper. The Tk color picker
# lives in its own thread while the Pygame visualizer continues running.
_color_pick_request = False
_color_pick_target = None
_color_pick_result = None
_color_pick_callback = None
_color_pick_lock = threading.Lock()


def choose_custom_colors(screen):
    # Open the color picker without blocking the Pygame playback loop.
    global _color_picker_thread

    if _color_picker_thread is not None and _color_picker_thread.is_alive():
        return

    def open_picker():
        # Run all Tkinter work together in the dedicated picker thread.
        _run_color_picker_window(screen)

    _color_picker_thread = threading.Thread(
        target=open_picker,
        daemon=True,
    )
    _color_picker_thread.start()


def run_the_one(converted_path=None, source_path=None, embedded=False):

    global _color_pick_result

    state = None  # Prepare the analysis state variable
    new_song_requested = None  # Keep this initialized even if an early error happens

    pygame.init()  # Start Pygame

    try:

        # ----------------------------------------------------
        # SELECT SONG
        # ----------------------------------------------------

        if converted_path is None:

            if source_path is None:
                source_path = select_audio_file()  # Ask the user to select a song

                if not source_path:
                    return  # Stop if the user cancelled

            try:

                converted_path = prepare_playback_audio(
                    source_path
                )  # Convert the selected song

            except Exception as error:

                show_error_message(
                    "The One - Audio Conversion Error",
                    f"Could not convert this song:\n\n{error}"
                )  # Show conversion errors instead of closing silently

                return

        else:

            if source_path is None:

                source_path = converted_path  # Use the converted path if no original path exists

        global PRIMARY_VIBE_COLOR  # Allow the selected song to control the wave color
        global SECONDARY_VIBE_COLOR  # Allow the selected song to control the bass color
        global PRIMARY_VIBE_NAME  # Allow the selected song's strongest vibe to be available to the color picker
        global SECONDARY_VIBE_NAME  # Allow the selected song to control automatic bass opacity and the color picker
        global CUSTOM_WAVE_COLOR  # Allow this song to load its own saved wave color
        global CUSTOM_BASS_COLOR  # Allow this song to load its own saved bass color
        global _bass_color_changed  # Allow the main loop to consume color-picker changes

        PRIMARY_VIBE_COLOR = (255, 255, 255)  # Reset the automatic wave color before detecting the new song
        SECONDARY_VIBE_COLOR = BACKGROUND_BASS  # Reset the automatic bass color before detecting the new song
        CUSTOM_WAVE_COLOR = None  # Prevent the previous song's custom wave color from carrying into this song
        CUSTOM_BASS_COLOR = None  # Prevent the previous song's custom bass color from carrying into this song

        # ----------------------------------------------------
        # DETECT TOP TWO VIBES
        # ----------------------------------------------------

        automatic_wave_color = (255, 255, 255)  # Remember the automatic Wave color for status reporting
        automatic_bass_color = BACKGROUND_BASS  # Remember the automatic Bass color for status reporting

        try:
            print("\nChecking the two main vibes for the selected song...")  # Start the imported vibe detector once for this song

            primary_vibe, secondary_vibe = analyze_song_vibe(
                source_path
            )  # Ask the imported detector for the strongest and second-strongest vibes

            PRIMARY_VIBE_NAME = primary_vibe or ""  # Store the strongest vibe for automatic wave coloring
            SECONDARY_VIBE_NAME = secondary_vibe or ""  # Store the second-ranked vibe for automatic bass opacity

            # Use a dedicated palette when acoustic and happy are the top two vibes,
            # regardless of which one ranks first.
            if {primary_vibe, secondary_vibe} == {"acoustic", "happy"}:
                automatic_wave_color = ACOUSTIC_HAPPY_COMBO_COLORS.get(primary_vibe, (255, 255, 255))
                automatic_bass_color = ACOUSTIC_HAPPY_COMBO_COLORS.get(secondary_vibe, BACKGROUND_BASS)
            else:
                automatic_wave_color = VIBE_COLORS.get(primary_vibe, (255, 255, 255))
                automatic_bass_color = VIBE_COLORS.get(secondary_vibe, BACKGROUND_BASS)

            PRIMARY_VIBE_COLOR = automatic_wave_color
            SECONDARY_VIBE_COLOR = automatic_bass_color

            if CUSTOM_WAVE_COLOR is not None:
                PRIMARY_VIBE_COLOR = CUSTOM_WAVE_COLOR  # Keep the user-selected wave color over automatic vibe coloring
            if CUSTOM_BASS_COLOR is not None:
                SECONDARY_VIBE_COLOR = CUSTOM_BASS_COLOR  # Keep the user-selected bass color over automatic vibe coloring

            print(f"VIBE 1: {primary_vibe.upper()}")  # Show the strongest detected vibe
            print(f"VIBE 2: {secondary_vibe.upper()}")  # Show the second strongest detected vibe
            print(f"Wave color: {PRIMARY_VIBE_COLOR}")  # Show the color selected for the wave
            print(f"Bass color: {SECONDARY_VIBE_COLOR}")  # Show the color selected for the bass background

        except Exception as error:
            PRIMARY_VIBE_NAME = ""  # Clear the strongest vibe when detection fails
            SECONDARY_VIBE_NAME = ""  # Clear the second vibe when detection fails
            automatic_wave_color = (255, 255, 255)  # Fall back to the original Test 15 wave color
            automatic_bass_color = BACKGROUND_BASS  # Fall back to the original Test 15 bass color
            PRIMARY_VIBE_COLOR = automatic_wave_color
            SECONDARY_VIBE_COLOR = automatic_bass_color
            if CUSTOM_WAVE_COLOR is not None:
                PRIMARY_VIBE_COLOR = CUSTOM_WAVE_COLOR  # Keep the user-selected wave color after a detection failure
            if CUSTOM_BASS_COLOR is not None:
                SECONDARY_VIBE_COLOR = CUSTOM_BASS_COLOR  # Keep the user-selected bass color after a detection failure
            print(f"Vibe checker failed: {error}")  # Keep the visualizer running if vibe detection fails
            print("Using the classic Test 15 colors.")  # Explain the fallback colors

        # ----------------------------------------------------
        # LOAD SONG-SPECIFIC CUSTOM COLORS
        # ----------------------------------------------------

        saved_bass_opacity = None
        saved_song_curvature = None
        saved_song_wave_height = None
        saved_song_calmness = None
        saved_song_gap = None
        saved_song_overall_opacity = None
        saved_song_center_width = None
        saved_song_center_opacity = None

        try:
            saved_wave_color, saved_bass_color = vibe_detector.get_saved_song_colors(
                source_path
            )  # Look for colors saved specifically for this song
            saved_bass_opacity = vibe_detector.get_saved_song_bass_opacity(
                source_path
            )  # Look for a song-specific Bass opacity saved in the same database
            saved_song_curvature = vibe_detector.get_saved_song_curvature(
                source_path
            )
            saved_song_wave_height = vibe_detector.get_saved_song_wave_height(
                source_path
            )  # Look for a song-specific wave curvature saved in the same database
            saved_song_calmness = vibe_detector.get_saved_song_calmness(
                source_path
            )  # Look for a song-specific Calmness level saved in the same database

            saved_song_bar_settings = vibe_detector.get_saved_song_bar_settings(
                source_path
            )  # Load the remaining song-specific bar settings
            if saved_song_bar_settings:
                saved_song_gap = saved_song_bar_settings.get("gap")
                saved_song_overall_opacity = saved_song_bar_settings.get("overall_opacity")
                saved_song_center_width = saved_song_bar_settings.get("center_width")
                saved_song_center_opacity = saved_song_bar_settings.get("center_opacity")

            if saved_wave_color is not None:
                CUSTOM_WAVE_COLOR = tuple(saved_wave_color)  # Restore the song's saved wave color
                PRIMARY_VIBE_COLOR = CUSTOM_WAVE_COLOR  # Use the saved wave color instead of the vibe color

            if saved_bass_color is not None:
                CUSTOM_BASS_COLOR = tuple(saved_bass_color)  # Restore the song's saved bass color
                SECONDARY_VIBE_COLOR = CUSTOM_BASS_COLOR  # Use the saved bass color instead of the vibe color

            if saved_bass_opacity is not None:
                bass_opacity_setting = float(
                    np.clip(saved_bass_opacity, 0.0, 1.0)
                )  # Restore this song's saved Bass opacity control value

            if saved_song_curvature is not None:
                saved_song_curvature = float(np.clip(saved_song_curvature, 0.0, 1.0))

            if saved_song_wave_height is not None:
                saved_song_wave_height = int(np.clip(round(float(saved_song_wave_height)), 1, 10))

            if saved_song_calmness is not None:
                saved_song_calmness = int(np.clip(round(float(saved_song_calmness)), 0, 10))

            if saved_song_gap is not None:
                saved_song_gap = float(np.clip(saved_song_gap, 0.0, 10.0))
            if saved_song_overall_opacity is not None:
                saved_song_overall_opacity = float(np.clip(saved_song_overall_opacity, 0.0, 1.0))
            if saved_song_center_width is not None:
                saved_song_center_width = float(np.clip(saved_song_center_width, 0.0, 1.0))
            if saved_song_center_opacity is not None:
                saved_song_center_opacity = float(np.clip(saved_song_center_opacity, 0.0, 1.0))

            if any(value is not None for value in (saved_wave_color, saved_bass_color, saved_bass_opacity, saved_song_curvature, saved_song_wave_height, saved_song_calmness, saved_song_gap, saved_song_overall_opacity, saved_song_center_width, saved_song_center_opacity)):
                print("Song-specific custom colors/opacity found and loaded.")  # Tell the user that saved song settings are active

        except Exception as error:
            print(f"Saved song colors could not be loaded: {error}")  # Keep normal vibe colors if the color cache cannot be read

        # If this song has no saved manual Bass opacity, start from the automatic
        # color-based value: 40% for bright colors and 80% for dark colors.
        if saved_bass_opacity is None:
            bass_opacity_setting = get_automatic_bass_opacity(
                SECONDARY_VIBE_COLOR
            )

        # ----------------------------------------------------
        # SONG DETAILS FOR THE STATUS PANEL
        # ----------------------------------------------------
        try:
            song_info = vibe_detector.get_last_visualizer_song_info() or {}
        except Exception:
            song_info = {}

        try:
            embedded_metadata = vibe_detector.read_embedded_song_metadata(source_path)
        except Exception:
            embedded_metadata = None

        song_info = dict(song_info)
        song_info["title"] = song_info.get("title") or (embedded_metadata.get("title") if embedded_metadata else os.path.splitext(os.path.basename(source_path))[0])
        song_info["artist"] = song_info.get("artist") or (embedded_metadata.get("artist") if embedded_metadata else "Unknown artist")
        song_info["identifier"] = song_info.get("identifier") or "Local file"
        song_info["primary_vibe"] = song_info.get("primary_vibe") or PRIMARY_VIBE_NAME or ""
        song_info["secondary_vibe"] = song_info.get("secondary_vibe") or SECONDARY_VIBE_NAME or ""
        try:
            song_info["duration"] = float(sf.info(source_path).duration)
        except Exception:
            song_info["duration"] = float(song_info.get("duration") or 0.0)

        saved_song_wave_color = tuple(saved_wave_color) if saved_wave_color is not None else None
        saved_song_bass_color = tuple(saved_bass_color) if saved_bass_color is not None else None
        saved_song_bass_opacity = float(np.clip(saved_bass_opacity, 0.0, 1.0)) if saved_bass_opacity is not None else None

        # ----------------------------------------------------
        # ----------------------------------------------------
        # LYRICS LOAD STATE
        # ----------------------------------------------------
        # Use lyrics.py's exact standalone audio lookup path. The lookup is
        # started once per song in a background thread, so playback is never
        # blocked by network/provider latency. lyrics.py handles its own cache.
        lyrics_state_lock = threading.Lock()
        lyrics_state = {
            "loading": True,
            "ready": False,
            "prepared": None,
            "combined": None,
            "error": None,
        }
        lyrics_visible = False

        def load_lyrics_background():
            try:
                combined, prepared = lyrics_engine.get_synced_lines_for_audio(source_path)
                with lyrics_state_lock:
                    lyrics_state["loading"] = False
                    lyrics_state["ready"] = bool(prepared and prepared.get("times"))
                    lyrics_state["prepared"] = prepared
                    lyrics_state["combined"] = combined
                    lyrics_state["error"] = None
            except Exception as error:
                with lyrics_state_lock:
                    lyrics_state["loading"] = False
                    lyrics_state["ready"] = False
                    lyrics_state["prepared"] = None
                    lyrics_state["combined"] = None
                    lyrics_state["error"] = str(error)
                print(f"Lyrics background load failed: {error}")

        lyrics_thread = threading.Thread(
            target=load_lyrics_background,
            daemon=True
        )
        lyrics_thread.start()

        # INITIALIZE AUDIO
        # ----------------------------------------------------

        try:

            pygame.mixer.init(
                frequency=SAMPLE_RATE
            )  # Initialize the audio mixer

        except Exception as error:

            show_error_message(
                "The One - Audio Error",
                f"Could not initialize the audio system:\n\n{error}"
            )  # Show mixer errors

            return

        # ----------------------------------------------------
        # CREATE OR REUSE WINDOW
        # ----------------------------------------------------

        screen = pygame.display.get_surface()  # Reuse the existing window when changing songs

        if screen is None:
            screen = pygame.display.set_mode(
                (1000, 600),
                pygame.RESIZABLE
            )  # Create the normal decorated Windows window only once

            # Maximize the normal Windows window instead of using Pygame's nonexistent MAXIMIZED flag.
            if os.name == "nt":
                wm_info = pygame.display.get_wm_info()  # Get the Windows handle for the Pygame window
                hwnd = wm_info.get("window")  # Read the native Windows window handle
                if hwnd:
                    ctypes.windll.user32.ShowWindow(hwnd, 3)  # Maximize the window after creating it

        bring_visualizer_to_front(screen)  # Put the visualizer in front of PyCharm and give it focus
        # If a window already exists, leave its size and maximized state completely unchanged.

        pygame.display.set_caption(
            "The One - Wave Surface Test"
        )  # Set the window title

        clock = pygame.time.Clock()  # Create the FPS clock

        displayed_wave_heights = None  # Remember the previous wave so it can fade smoothly
        displayed_wave_width = 0  # Remember the width used by the stored wave
        bar_surface_cache = {}  # Reuse rendered bar shapes instead of rebuilding alpha matrices every frame
        global smooth_bass_background  # Allow this visualizer instance to reset the bass background
        smooth_bass_background = 0.0  # Start the bass-reactive background from idle

        font = pygame.font.SysFont(
            "Arial",
            20
        )  # Create the status font
        small_font = pygame.font.SysFont(
            "Arial",
            16
        )  # Create the smaller controls-menu font

        try:
            unicode_font_path = lyrics_engine._find_unicode_font()
            lyrics_font = (
                pygame.font.Font(unicode_font_path, 34)
                if unicode_font_path
                else pygame.font.Font(None, 34)
            )
        except Exception:
            lyrics_font = pygame.font.SysFont("Arial", 34)

        # Temporary Calm Mode notification shown directly below the Calm button.
        calm_mode_notice_message = ""
        calm_mode_notice_until = 0.0
        calm_mode_notice_started = 0.0

        # ----------------------------------------------------
        # START BACKGROUND ANALYSIS
        # ----------------------------------------------------

        state = HybridAnalysisState()  # Create shared analysis state

        analysis_thread = threading.Thread(
            target=analyze_song,
            args=(
                converted_path,
                source_path,
                state
            ),
            daemon=True
        )  # Create the streaming analysis thread

        analysis_thread.start()  # Start the streaming analysis thread

        bass_analysis_stop.clear()  # Allow the independent bass-analysis thread to run

        bass_thread = threading.Thread(
            target=analyze_bass_background,
            args=(converted_path,),
            daemon=True
        )  # Create a separate thread so bass analysis cannot alter the piano-analysis process

        bass_thread.start()  # Start the independent background-bass analysis

        # ----------------------------------------------------
        # WAIT FOR THE FIRST PART
        # ----------------------------------------------------

        if not wait_for_startup_analysis(
            state
        ):

            with state.lock:

                startup_error = state.error  # Get the actual analysis error

            if startup_error:

                show_error_message(
                    "The One - Analysis Error",
                    f"Could not analyze this song:\n\n{startup_error}"
                )  # Tell the user why the song failed

            else:

                show_error_message(
                    "The One - Analysis Error",
                    "The song could not be analyzed."
                )  # Show a generic error if no details exist

            state.stop_event.set()  # Stop the analysis thread

            return

        # ----------------------------------------------------
        # LOAD SONG INTO PYGAME
        # ----------------------------------------------------

        try:

            pygame.mixer.music.load(
                converted_path
            )  # Load the converted WAV into Pygame

        except Exception as error:

            show_error_message(
                "The One - Playback Error",
                f"Could not play this song:\n\n{error}"
            )  # Show playback errors instead of silently closing

            state.stop_event.set()  # Stop background analysis

            return

        # ----------------------------------------------------
        # START PLAYBACK
        # ----------------------------------------------------

        pygame.mixer.music.play()  # Start playing the song

        playing = True  # Remember that playback is currently active

        user_paused = False  # Remember whether the user intentionally paused playback

        # Home-button auto-hide state.  The button starts visible, then smoothly
        # fades away after playback begins.  Any mouse movement reveals it again.
        home_visibility = 1.0
        home_reveal_until = time.perf_counter() + 0.8

        seek_offset = 0.0  # Keep the compatibility seek position used when restarting Pygame music

        song_position = 0.0  # Keep the visualizer's logical song position synchronized with playback
        position_clock = time.perf_counter()  # Keep a compatibility timestamp; audio timing now comes from Pygame

        running = True  # Keep the window open

        # ====================================================
        # BAR APPEARANCE CONTROLS
        # ====================================================
        default_bar_gap = 2.0  # Factory-default gap
        default_curvature = 0.50  # Factory-default wave curvature; 50% preserves the current wave shape
        default_wave_height = 10  # Factory-default overall wave height on the 1-10 scale
        default_overall_opacity = 0.80  # Factory-default maximum opacity
        default_center_width = 0.20  # Factory-default center width
        default_center_opacity = 0.80  # Factory-default center opacity
        default_bass_opacity = 0.80  # Factory-default bass opacity control
        default_calmness = 0  # Factory-default Calmness level; 0 keeps the raw responsive wave

        def load_bar_defaults():
            try:
                with open(BAR_SETTINGS_FILE, "r", encoding="utf-8") as file:
                    saved = json.load(file)  # Load the user's saved bar defaults
                return (
                    float(saved.get("gap", default_bar_gap)),
                    float(saved.get("curvature", default_curvature)),
                    int(np.clip(round(float(saved.get("wave_height", default_wave_height))), 1, 10)),
                    float(saved.get("overall_opacity", default_overall_opacity)),
                    float(saved.get("center_width", default_center_width)),
                    float(saved.get("center_opacity", default_center_opacity)),
                    default_bass_opacity,
                    int(np.clip(round(float(saved.get("calmness", default_calmness))), 0, 10)),
                )  # Load the saved bar settings; Bass opacity stays independent
            except Exception:
                return (default_bar_gap, default_curvature, default_wave_height, default_overall_opacity, default_center_width, default_center_opacity, default_bass_opacity, default_calmness)  # Use factory defaults if loading fails

        bar_gap_setting, curvature_setting, wave_height_setting, overall_opacity_setting, center_width_setting, center_opacity_setting, factory_bass_opacity_setting, calmness_setting = load_bar_defaults()  # Load the saved global bar defaults at startup

        if saved_song_gap is not None:
            bar_gap_setting = saved_song_gap
        if saved_song_overall_opacity is not None:
            overall_opacity_setting = saved_song_overall_opacity
        if saved_song_center_width is not None:
            center_width_setting = saved_song_center_width
        if saved_song_center_opacity is not None:
            center_opacity_setting = saved_song_center_opacity

        if saved_song_curvature is not None:
            curvature_setting = saved_song_curvature  # Song-specific curvature overrides the global factory/default value

        if saved_song_wave_height is not None:
            wave_height_setting = saved_song_wave_height  # Song-specific wave height overrides the global factory/default value

        # Keep the song-specific Bass opacity loaded earlier.
        # Only use the factory value when this song has no saved Bass opacity.
        if saved_bass_opacity is None:
            bass_opacity_setting = get_automatic_bass_opacity(SECONDARY_VIBE_COLOR)

        def save_bar_defaults():
            settings = {
                "gap": bar_gap_setting,
                "curvature": curvature_setting,
                "wave_height": wave_height_setting,
                "overall_opacity": overall_opacity_setting,
                "center_width": center_width_setting,
                "center_opacity": center_opacity_setting,
                "calmness": calmness_setting,
            }  # Save the bar controls; Bass opacity remains independent
            try:
                with open(BAR_SETTINGS_FILE, "w", encoding="utf-8") as file:
                    json.dump(settings, file, indent=4)  # Save them for the next launch
                return True  # Report a successful save
            except Exception:
                return False  # Keep the visualizer running if saving fails

        def save_current_song_colors():
            """Save the currently displayed Wave/Bass colors and Bass opacity to this song's vibe-cache entry."""
            try:
                vibe_detector.save_song_colors(
                    source_path,
                    PRIMARY_VIBE_COLOR,
                    SECONDARY_VIBE_COLOR,
                    bass_opacity_setting,
                    curvature_setting,
                    wave_height_setting,
                    bar_gap_setting,
                    overall_opacity_setting,
                    center_width_setting,
                    center_opacity_setting,
                    calmness_setting,
                )  # Save every menu-controlled bar setting using the song's exact fingerprint
                nonlocal saved_song_wave_color, saved_song_bass_color, saved_song_bass_opacity, saved_song_curvature, saved_song_wave_height
                nonlocal saved_song_gap, saved_song_overall_opacity, saved_song_center_width, saved_song_center_opacity, saved_song_calmness
                saved_song_wave_color = tuple(PRIMARY_VIBE_COLOR)
                saved_song_bass_color = tuple(SECONDARY_VIBE_COLOR)
                saved_song_bass_opacity = float(bass_opacity_setting)
                saved_song_curvature = float(curvature_setting)
                saved_song_wave_height = int(wave_height_setting)
                saved_song_gap = float(bar_gap_setting)
                saved_song_overall_opacity = float(overall_opacity_setting)
                saved_song_center_width = float(center_width_setting)
                saved_song_center_opacity = float(center_opacity_setting)
                saved_song_calmness = int(calmness_setting)

                # The newly saved settings are now the song's current saved state.
                # Update Undo's baseline too, so pressing Undo after Save As Default
                # does not jump back to the older settings from before the save.
                nonlocal undo_song_settings
                undo_song_settings = (
                    bar_gap_setting,
                    curvature_setting,
                    wave_height_setting,
                    overall_opacity_setting,
                    center_width_setting,
                    center_opacity_setting,
                    bass_opacity_setting,
                    calmness_setting,
                )

                print(f"Saved all song bar settings for: {source_path}")  # Confirm the song-specific color save
                return True  # Report a successful song-color save
            except Exception as error:
                print(f"Could not save song colors: {error}")  # Keep the visualizer running if saving fails
                show_error_message(
                    "The One - Color Save Error",
                    f"Could not save colors for this song:\n\n{error}"
                )  # Tell the user why the colors could not be saved
                return False  # Report a failed song-color save
        controls_open = False  # Keep the settings menu hidden until its button is clicked
        status_open = False  # Keep the song details/status panel hidden until its button is clicked
        status_details_open = False  # Keep the detailed settings-change list collapsed by default
        calm_mode = False  # Keep the existing quick Calm toggle as a hard 10/10 override
        calm_mode_saved_settings = None  # Temporarily store the normal settings while Calm mode is active
        visualizer_image_frames = []  # Store the selected image or all frames of the selected GIF
        visualizer_image_delays = []  # Store per-frame GIF delays in milliseconds
        visualizer_image_is_gif = False  # Remember whether the selected visualizer image is animated
        visualizer_image_path = None  # Remember the currently selected image path
        visualizer_image_started_at = 0.0  # Track when the current GIF animation began
        visualizer_image_size = 0.20  # User-adjustable image height as a fraction of the screen height
        visualizer_image_corner_roundness = 0.0  # Rounded-corner amount as a fraction of the image
        visualizer_image_bottom_fade = 0.0  # Bottom-to-black fade strength for improving wave/bass contrast
        screen_width, screen_height = screen.get_size()
        visualizer_image_center = [screen_width / 2.0, screen_height / 2.0]  # Current draggable image center
        visualizer_image_editing = False  # Show image-position/size controls after selecting an image
        visualizer_image_dragging = False  # Track whether the image itself is being dragged
        visualizer_image_drag_offset = (0.0, 0.0)  # Preserve the grab point while dragging
        # Center alignment snapping: gently lock the image to the exact screen center
        # when its center is close enough, just like photo editors.
        visualizer_image_center_snap_x = False
        visualizer_image_center_snap_y = False
        visualizer_image_edit_backup = None  # Restore the previous image/settings when Cancel is pressed
        visualizer_image_database_data = None  # Keep the selected image bytes so the exact image can be saved in the song database
        visualizer_image_database_name = None  # Remember the original image filename/extension for database restores
        image_size_slider_active = False  # Track image-size slider dragging
        # Remember the song's original customization so Undo can restore it without reloading the song.
        undo_song_settings = None
        calmness_setting = default_calmness  # Store the new 0-to-10 gradual Calmness control
        if saved_song_calmness is not None:
            calmness_setting = saved_song_calmness  # Song-specific Calmness overrides the global default

        # Capture the exact settings this song started with. Undo restores these
        # values even after the user presses Default or makes further unsaved changes.
        undo_song_settings = (
            bar_gap_setting,
            curvature_setting,
            wave_height_setting,
            overall_opacity_setting,
            center_width_setting,
            center_opacity_setting,
            bass_opacity_setting,
            calmness_setting,
        )
        active_slider = None  # Remember which slider is being dragged

        def format_song_length(seconds):
            total_seconds = max(0, int(round(float(seconds or 0.0))))
            minutes, remaining_seconds = divmod(total_seconds, 60)
            return f"{minutes}:{remaining_seconds:02d}"

        def get_status_name_line_count():
            title = str(song_info.get("title", "Unknown title"))
            max_width = 235
            lines = []
            current_line = ""

            # Wrap by pixels, including very long single words. This prevents
            # a long song title from escaping through the right side of the panel.
            for word in title.split():
                candidate = word if not current_line else current_line + " " + word
                if small_font.size(candidate)[0] <= max_width:
                    current_line = candidate
                    continue

                if current_line:
                    lines.append(current_line)
                    current_line = ""

                # Break a single word into pieces when the word itself is too long.
                piece = ""
                for char in word:
                    test_piece = piece + char
                    if piece and small_font.size(test_piece)[0] > max_width:
                        lines.append(piece)
                        piece = char
                    else:
                        piece = test_piece
                current_line = piece

            if current_line or not lines:
                lines.append(current_line)
            return max(1, len(lines))

        def get_status_singer_line_count():
            singer = str(song_info.get("artist", "Unknown artist"))
            max_width = 235
            lines = []
            current_line = ""

            # Use the same pixel-based wrapping as the visible Singer row so
            # the dropdown position stays synchronized with the displayed text.
            for word in singer.split():
                candidate = word if not current_line else current_line + " " + word
                if small_font.size(candidate)[0] <= max_width:
                    current_line = candidate
                    continue

                if current_line:
                    lines.append(current_line)
                    current_line = ""

                # Break a single long word into pieces when necessary.
                piece = ""
                for char in word:
                    test_piece = piece + char
                    if piece and small_font.size(test_piece)[0] > max_width:
                        lines.append(piece)
                        piece = char
                    else:
                        piece = test_piece
                current_line = piece

            if current_line or not lines:
                lines.append(current_line)
            return max(1, len(lines))

        def get_status_settings_y():
            name_height = max(26, get_status_name_line_count() * 22)
            singer_height = max(26, get_status_singer_line_count() * 22)
            return 103 + name_height + singer_height + 26 + 26

        def current_settings_status():
            wave_changed = tuple(PRIMARY_VIBE_COLOR) != tuple(automatic_wave_color)
            bass_changed = tuple(SECONDARY_VIBE_COLOR) != tuple(automatic_bass_color)
            bass_factory_opacity = get_automatic_bass_opacity(SECONDARY_VIBE_COLOR)
            bass_opacity_changed = abs(float(bass_opacity_setting) - bass_factory_opacity) > 0.0005
            gap_changed = abs(float(bar_gap_setting) - default_bar_gap) > 0.001
            curvature_changed = abs(float(curvature_setting) - default_curvature) > 0.0005
            wave_height_changed = int(wave_height_setting) != int(default_wave_height)
            overall_changed = abs(float(overall_opacity_setting) - default_overall_opacity) > 0.0005
            center_width_changed = abs(float(center_width_setting) - default_center_width) > 0.0005
            center_opacity_changed = abs(float(center_opacity_setting) - default_center_opacity) > 0.0005
            calmness_changed = int(calmness_setting) != int(default_calmness)
            any_changed = any((wave_changed, bass_changed, bass_opacity_changed, gap_changed, curvature_changed, wave_height_changed, overall_changed, center_width_changed, center_opacity_changed, calmness_changed))
            saved_exists = any((saved_song_wave_color is not None, saved_song_bass_color is not None, saved_song_bass_opacity is not None, saved_song_curvature is not None, saved_song_wave_height is not None, saved_song_gap is not None, saved_song_overall_opacity is not None, saved_song_center_width is not None, saved_song_center_opacity is not None))
            saved_current = True
            if saved_song_wave_color is not None: saved_current &= tuple(PRIMARY_VIBE_COLOR) == tuple(saved_song_wave_color)
            if saved_song_bass_color is not None: saved_current &= tuple(SECONDARY_VIBE_COLOR) == tuple(saved_song_bass_color)
            if saved_song_bass_opacity is not None: saved_current &= abs(float(bass_opacity_setting) - saved_song_bass_opacity) <= 0.0005
            if saved_song_curvature is not None: saved_current &= abs(float(curvature_setting) - saved_song_curvature) <= 0.0005
            if saved_song_wave_height is not None: saved_current &= int(wave_height_setting) == int(saved_song_wave_height)
            if saved_song_calmness is not None: saved_current &= int(calmness_setting) == int(saved_song_calmness)
            if saved_song_gap is not None: saved_current &= abs(float(bar_gap_setting) - saved_song_gap) <= 0.001
            if saved_song_overall_opacity is not None: saved_current &= abs(float(overall_opacity_setting) - saved_song_overall_opacity) <= 0.0005
            if saved_song_center_width is not None: saved_current &= abs(float(center_width_setting) - saved_song_center_width) <= 0.0005
            if saved_song_center_opacity is not None: saved_current &= abs(float(center_opacity_setting) - saved_song_center_opacity) <= 0.0005
            if not saved_exists: saved_current = not (wave_changed or bass_changed or bass_opacity_changed or gap_changed or curvature_changed or wave_height_changed or overall_changed or center_width_changed or center_opacity_changed or calmness_changed)
            return {"overall": any_changed, "wave": wave_changed, "bass": bass_changed, "bass_opacity": bass_opacity_changed, "gap": gap_changed, "curvature": curvature_changed, "overall_opacity": overall_changed, "center_width": center_width_changed, "center_opacity": center_opacity_changed, "wave_height": wave_height_changed, "calmness": calmness_changed, "saved_current": bool(saved_current)}

        def get_song_image_database_key():
            # Use the same exact acoustic fingerprint key as the existing song settings database.
            fingerprint = vibe_detector._get_visualizer_fingerprint(source_path)
            if not fingerprint:
                raise RuntimeError("Could not create an acoustic fingerprint for saving this song's image.")
            return vibe_detector.get_fingerprint_cache_key(fingerprint)

        def ensure_song_image_table(connection):
            # Keep image data in a separate table so the existing vibe-cache schema and saved colors remain untouched.
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS visualizer_song_images (
                    fingerprint_key TEXT PRIMARY KEY,
                    image_data BLOB NOT NULL,
                    image_name TEXT,
                    image_size REAL NOT NULL DEFAULT 0.20,
                    center_x REAL NOT NULL DEFAULT 0.0,
                    center_y REAL NOT NULL DEFAULT 0.0,
                    corner_roundness REAL NOT NULL DEFAULT 0.0,
                    bottom_fade REAL NOT NULL DEFAULT 0.0,
                    updated_at REAL NOT NULL
                )
                """
            )
            # Migrate databases created before corner-rounding was added.
            columns = {row[1] for row in connection.execute("PRAGMA table_info(visualizer_song_images)").fetchall()}
            if "corner_roundness" not in columns:
                connection.execute(
                    "ALTER TABLE visualizer_song_images ADD COLUMN corner_roundness REAL NOT NULL DEFAULT 0.0"
                )
            if "bottom_fade" not in columns:
                connection.execute(
                    "ALTER TABLE visualizer_song_images ADD COLUMN bottom_fade REAL NOT NULL DEFAULT 0.0"
                )

        def save_song_visualizer_image():
            # Save the actual image/GIF bytes plus its current size and position for this exact song.
            if not visualizer_image_database_data:
                return False

            database_path = vibe_detector.initialize_vibe_database()
            fingerprint_key = get_song_image_database_key()
            image_name = visualizer_image_database_name or "visualizer_image"

            with sqlite3.connect(database_path) as connection:
                ensure_song_image_table(connection)
                connection.execute(
                    """
                    INSERT INTO visualizer_song_images (
                        fingerprint_key, image_data, image_name, image_size, center_x, center_y, corner_roundness, bottom_fade, updated_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(fingerprint_key) DO UPDATE SET
                        image_data = excluded.image_data,
                        image_name = excluded.image_name,
                        image_size = excluded.image_size,
                        center_x = excluded.center_x,
                        center_y = excluded.center_y,
                        corner_roundness = excluded.corner_roundness,
                        bottom_fade = excluded.bottom_fade,
                        updated_at = excluded.updated_at
                    """,
                    (
                        fingerprint_key,
                        sqlite3.Binary(visualizer_image_database_data),
                        image_name,
                        float(visualizer_image_size),
                        float(visualizer_image_center[0]),
                        float(visualizer_image_center[1]),
                        float(visualizer_image_corner_roundness),
                        float(visualizer_image_bottom_fade),
                        time.time(),
                    ),
                )

            print(f"Visualizer image saved to local database for: {source_path}")
            return True

        def load_saved_song_visualizer_image():
            # Restore the song's saved image, including the user's last size and exact position.
            nonlocal visualizer_image_frames, visualizer_image_delays
            nonlocal visualizer_image_is_gif, visualizer_image_path, visualizer_image_started_at
            nonlocal visualizer_image_size, visualizer_image_center, visualizer_image_corner_roundness, visualizer_image_bottom_fade
            nonlocal visualizer_image_database_data, visualizer_image_database_name

            try:
                database_path = vibe_detector.initialize_vibe_database()
                fingerprint_key = get_song_image_database_key()

                with sqlite3.connect(database_path) as connection:
                    ensure_song_image_table(connection)
                    row = connection.execute(
                        """
                        SELECT image_data, image_name, image_size, center_x, center_y, corner_roundness, bottom_fade
                        FROM visualizer_song_images
                        WHERE fingerprint_key = ?
                        """,
                        (fingerprint_key,),
                    ).fetchone()

                if not row or not row[0]:
                    return False

                image_data = bytes(row[0])
                image_name = row[1] or "visualizer_image"
                suffix = os.path.splitext(image_name)[1] or ".png"
                temp_path = None

                try:
                    with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as temp_file:
                        temp_file.write(image_data)
                        temp_path = temp_file.name

                    if not load_visualizer_image(
                        temp_path,
                        reset_position=False,
                        database_data=image_data,
                        database_name=image_name,
                    ):
                        return False
                finally:
                    if temp_path:
                        try:
                            os.unlink(temp_path)
                        except OSError:
                            pass

                visualizer_image_size = max(0.10, float(row[2]))
                visualizer_image_center = [float(row[3]), float(row[4])]
                visualizer_image_corner_roundness = float(np.clip(float(row[5]), 0.0, 0.45))
                visualizer_image_bottom_fade = float(np.clip(float(row[6]), 0.0, 1.0))
                visualizer_image_path = None
                return True

            except Exception as error:
                print(f"Could not load saved visualizer image: {error}")
                return False

        def load_visualizer_image(path, reset_position=True, database_data=None, database_name=None):
            # Load the selected image. WebP is decoded with FFmpeg first because
            # Pillow builds can sometimes reject otherwise valid WebP files.
            nonlocal visualizer_image_frames, visualizer_image_delays
            nonlocal visualizer_image_is_gif, visualizer_image_path, visualizer_image_started_at
            nonlocal visualizer_image_size, visualizer_image_center, visualizer_image_corner_roundness, visualizer_image_bottom_fade
            nonlocal visualizer_image_database_data, visualizer_image_database_name

            def _ffmpeg_executables():
                candidates = [FFMPEG_PATH]
                try:
                    import shutil as _shutil
                    system_ffmpeg = _shutil.which("ffmpeg")
                    if system_ffmpeg:
                        candidates.append(system_ffmpeg)
                except Exception:
                    pass
                try:
                    import imageio_ffmpeg
                    candidates.append(imageio_ffmpeg.get_ffmpeg_exe())
                except Exception:
                    pass

                result = []
                for candidate in candidates:
                    if candidate and candidate not in result and os.path.isfile(candidate):
                        result.append(candidate)
                return result

            def _convert_webp_with_ffmpeg(webp_path):
                executables = _ffmpeg_executables()
                if not executables:
                    raise RuntimeError(
                        "No FFmpeg executable was found for WebP decoding."
                    )

                errors = []
                for executable in executables:
                    temp_dir = tempfile.mkdtemp(prefix="visualizer_webp_")
                    try:
                        output_pattern = os.path.join(temp_dir, "frame_%06d.png")
                        command = [
                            executable,
                            "-hide_banner",
                            "-loglevel", "error",
                            "-y",
                            "-i", webp_path,
                            "-map", "0:v:0",
                            "-c:v", "png",
                            output_pattern,
                        ]

                        creationflags = 0
                        if os.name == "nt":
                            creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)

                        result = subprocess.run(
                            command,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            timeout=60,
                            creationflags=creationflags,
                        )

                        frame_paths = sorted(
                            os.path.join(temp_dir, filename)
                            for filename in os.listdir(temp_dir)
                            if filename.lower().endswith(".png")
                        )

                        if result.returncode == 0 and frame_paths:
                            frames = []
                            for frame_path in frame_paths:
                                frame = Image.open(frame_path).convert("RGBA")
                                frame_surface = pygame.image.fromstring(
                                    frame.tobytes(), frame.size, "RGBA"
                                ).convert_alpha()
                                frames.append(frame_surface)

                            # FFmpeg extraction gives reliable decoded frames but
                            # not the original WebP per-frame timing through this
                            # simple image-sequence path. Keep a safe animation rate.
                            delays = [100] * len(frames) if len(frames) > 1 else [0]
                            return frames, delays, len(frames) > 1

                        details = result.stderr.strip() or "unknown FFmpeg error"
                        errors.append(f"{os.path.basename(executable)}: {details}")
                    except Exception as error:
                        errors.append(f"{os.path.basename(executable)}: {error}")
                    finally:
                        shutil.rmtree(temp_dir, ignore_errors=True)

                raise RuntimeError(
                    "FFmpeg could not decode this WebP.\n\n" + "\n".join(errors)
                )

            try:
                is_webp = os.path.splitext(path)[1].lower() == ".webp"

                if is_webp:
                    # Use FFmpeg first. This is the important fix for the exact
                    # Pillow error: "cannot identify image file ...webp".
                    frames, delays, is_animated = _convert_webp_with_ffmpeg(path)
                else:
                    image = Image.open(path)
                    frame_count = max(1, int(getattr(image, "n_frames", 1)))
                    is_animated = frame_count > 1
                    frames = []
                    delays = []

                    for frame_index in range(frame_count):
                        if is_animated:
                            image.seek(frame_index)
                        frame = image.convert("RGBA")
                        frame_surface = pygame.image.fromstring(
                            frame.tobytes(), frame.size, "RGBA"
                        ).convert_alpha()
                        frames.append(frame_surface)

                        if is_animated:
                            delay = int(image.info.get("duration", 100) or 100)
                            delays.append(max(20, delay))
                        else:
                            delays.append(0)

                visualizer_image_frames = frames
                visualizer_image_delays = delays
                visualizer_image_is_gif = is_animated
                visualizer_image_path = path
                visualizer_image_started_at = time.perf_counter()
                visualizer_image_database_data = database_data
                visualizer_image_database_name = database_name or os.path.basename(path)
                if reset_position:
                    visualizer_image_size = 0.20
                    visualizer_image_center = [width / 2.0, height / 2.0]
                    visualizer_image_corner_roundness = 0.0
                    visualizer_image_bottom_fade = 0.0
                return True
            except Exception as error:
                print(f"Could not load visualizer image: {error}")
                show_error_message(
                    "The One - Image Error",
                    f"Could not load this image:\n\n{error}"
                )
                return False

        # Restore the image saved for this song before entering the main visualizer loop.
        # This must happen after load_visualizer_image() is defined because the saved-image
        # loader uses that function to decode the stored image/GIF bytes.
        if load_saved_song_visualizer_image():
            print(f"Restored saved visualizer image for: {source_path}")

        def get_visualizer_image_max_size():
            # Return the largest slider value needed for the current image to reach
            # the full screen width while preserving its original aspect ratio.
            if not visualizer_image_frames:
                return 1.0
            source_width, source_height = visualizer_image_frames[0].get_size()
            if source_width <= 0 or source_height <= 0 or height <= 0:
                return 1.0
            width_based_height_fraction = (float(width) * float(source_height)) / (float(source_width) * float(height))
            return max(1.0, width_based_height_fraction)

        def get_visualizer_image_rect():
            # Return the current image rectangle using the user-selected size and position.
            if not visualizer_image_frames:
                return None
            image_surface = visualizer_image_frames[0]
            source_width, source_height = image_surface.get_size()
            if source_height <= 0:
                return None
            image_height = max(80, int(round(height * visualizer_image_size)))
            image_width = max(1, int(round(source_width * image_height / source_height)))
            return pygame.Rect(0, 0, image_width, image_height).copy().move(
                int(round(visualizer_image_center[0] - image_width / 2)),
                int(round(visualizer_image_center[1] - image_height / 2)),
            )

        def get_current_image_pixel(mouse_x, mouse_y):
            # Sample the actual image frame at the clicked Pygame position.
            if not visualizer_image_frames:
                return None

            if visualizer_image_is_gif and len(visualizer_image_frames) > 1:
                elapsed_ms = int((time.perf_counter() - visualizer_image_started_at) * 1000.0)
                total_ms = max(1, sum(visualizer_image_delays))
                frame_time = elapsed_ms % total_ms
                accumulated_ms = 0
                frame_index = 0
                for index, delay in enumerate(visualizer_image_delays):
                    accumulated_ms += delay
                    if frame_time < accumulated_ms:
                        frame_index = index
                        break
                image_surface = visualizer_image_frames[frame_index]
            else:
                image_surface = visualizer_image_frames[0]

            source_width, source_height = image_surface.get_size()
            if source_width <= 0 or source_height <= 0:
                return None

            image_height = max(80, int(round(height * visualizer_image_size)))
            image_width = max(1, int(round(source_width * image_height / source_height)))
            image_rect = pygame.Rect(0, 0, image_width, image_height).move(
                int(round(visualizer_image_center[0] - image_width / 2)),
                int(round(visualizer_image_center[1] - image_height / 2)),
            )

            if not image_rect.collidepoint(mouse_x, mouse_y):
                return None

            local_x = max(0, min(image_width - 1, mouse_x - image_rect.left))
            local_y = max(0, min(image_height - 1, mouse_y - image_rect.top))
            source_x = min(source_width - 1, int(local_x * source_width / max(1, image_width)))
            source_y = min(source_height - 1, int(local_y * source_height / max(1, image_height)))

            try:
                return tuple(image_surface.get_at((source_x, source_y))[:3])
            except Exception:
                return None

        # Cache anti-aliased corner masks so rounded GIF frames do not need to rebuild
        # the mask from scratch when only the animation frame changes.
        rounded_image_mask_cache = {}

        def apply_rounded_image_corners(image_surface, roundness):
            # Apply smooth rounded corners after the image has been scaled to its final
            # display size. The mask itself is rendered at 4x resolution and downsampled
            # with Lanczos, keeping the curved edge clean instead of pixelated.
            if image_surface is None or roundness <= 0.0001:
                return image_surface

            image_width, image_height = image_surface.get_size()
            if image_width <= 1 or image_height <= 1:
                return image_surface

            radius = int(round(min(image_width, image_height) * float(np.clip(roundness, 0.0, 0.45))))
            if radius <= 0:
                return image_surface
            radius = min(radius, min(image_width, image_height) // 2)

            cache_key = (image_width, image_height, radius)
            mask = rounded_image_mask_cache.get(cache_key)

            if mask is None:
                aa_scale = 4
                hi_width = image_width * aa_scale
                hi_height = image_height * aa_scale
                hi_radius = radius * aa_scale

                high_mask = pygame.Surface((hi_width, hi_height), pygame.SRCALPHA)
                pygame.draw.rect(
                    high_mask,
                    (255, 255, 255, 255),
                    pygame.Rect(0, 0, hi_width, hi_height),
                    border_radius=hi_radius,
                )
                mask = pygame.transform.smoothscale(
                    high_mask,
                    (image_width, image_height),
                )
                rounded_image_mask_cache[cache_key] = mask

            rounded_image = image_surface.copy()
            rounded_image.blit(mask, (0, 0), special_flags=pygame.BLEND_RGBA_MULT)
            return rounded_image

        def apply_bottom_image_fade(image_surface, fade_strength):
            # Apply the selected fade level as a real black opacity gradient.
            # Level 0 leaves the image completely unchanged; higher levels
            # progressively darken the lower part of the image, with the
            # strongest level becoming almost black at the bottom.
            if image_surface is None:
                return image_surface

            fade_strength = float(np.clip(fade_strength, 0.0, 1.0))
            if fade_strength <= 0.0001:
                return image_surface

            image_width, image_height = image_surface.get_size()
            if image_width <= 1 or image_height <= 1:
                return image_surface

            # The fade starts around the lower 55% and becomes strongest at
            # the bottom.  Using the actual selected strength here makes each
            # level visibly different rather than merely changing the icon.
            gradient = pygame.Surface((1, image_height), pygame.SRCALPHA)
            for y in range(image_height):
                ratio = y / max(1.0, image_height - 1)
                fade_position = max(0.0, (ratio - 0.45) / 0.55)
                fade_position = fade_position * fade_position * (3.0 - 2.0 * fade_position)
                alpha = int(round(255.0 * fade_strength * fade_position))
                gradient.set_at((0, y), (0, 0, 0, alpha))

            gradient = pygame.transform.smoothscale(
                gradient,
                (image_width, image_height),
            )

            faded = image_surface.copy()
            faded.blit(gradient, (0, 0))
            return faded

        # ====================================================
        # MAIN LOOP
        # ====================================================

        while running:

            # Keep the top button rectangles defined for both mouse handling and drawing.
            width, height = screen.get_size()
            home_button_rect = pygame.Rect(5, 12, 40, 30)
            top_button_y = 12
            top_button_gap = 8
            lyrics_button_rect = pygame.Rect(width - 33, 18, 18, 18)
            calm_button_rect = pygame.Rect(lyrics_button_rect.left - top_button_gap - 18, 18, 18, 18)
            status_button_rect = pygame.Rect(calm_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            image_button_rect = pygame.Rect(status_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            song_button_rect = pygame.Rect(image_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            color_button_rect = pygame.Rect(song_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            menu_button_rect = pygame.Rect(color_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)

            # Temporary image editor controls shown only after an image is selected.
            # Keep the slider the same length as before; only the image's maximum
            # size is dynamic so the image itself can reach full screen width.
            image_size_slider_width = 280
            image_size_slider_left = (width - image_size_slider_width) // 2
            image_size_slider_right = image_size_slider_left + image_size_slider_width
            image_size_slider_y = 58
            image_size_slider_rect = pygame.Rect(
                image_size_slider_left - 12,
                image_size_slider_y - 14,
                image_size_slider_width + 24,
                28,
            )
            image_save_button_rect = pygame.Rect(
                image_size_slider_right + 12,
                image_size_slider_y - 15,
                30,
                30,
            )
            image_cancel_button_rect = pygame.Rect(
                image_save_button_rect.right + 8,
                image_size_slider_y - 15,
                30,
                30,
            )
            image_corner_button_rect = pygame.Rect(image_cancel_button_rect.right + 8, image_size_slider_y - 15, 30, 30)
            image_fade_button_rect = pygame.Rect(image_corner_button_rect.right + 8, image_size_slider_y - 15, 30, 30)

            # The color picker runs in another thread. Reset Bass opacity only
            # after the user has actually accepted the new Bass color.
            if _bass_color_changed:
                bass_opacity_setting = get_automatic_bass_opacity(
                    SECONDARY_VIBE_COLOR
                )
                _bass_color_changed = False

            picker_result = get_song_picker_result()  # Check whether the background song picker has finished
            if picker_result is not None:
                new_song_requested = picker_result  # Save the selected song path or empty cancel result
                bring_visualizer_to_front(screen)  # Re-activate the visualizer after the file picker closes
                if new_song_requested:
                    controls_open = False  # Keep the controls menu closed before switching songs
                    status_open = False  # Keep the song status panel closed before switching songs
                    active_slider = None  # Stop any slider interaction before switching songs
                    running = False  # End the current playback loop so the new song can be loaded

            # The image picker is also asynchronous. While its native Windows dialog
            # is open, this Pygame loop continues drawing, animating and playing audio.
            image_picker_result = get_image_picker_result()
            if image_picker_result is not None:
                image_path = image_picker_result
                bring_visualizer_to_front(screen)
                if image_path:
                    # Keep the current image/settings so Cancel can restore them.
                    visualizer_image_edit_backup = (
                        list(visualizer_image_frames),
                        list(visualizer_image_delays),
                        visualizer_image_is_gif,
                        visualizer_image_path,
                        visualizer_image_started_at,
                        visualizer_image_size,
                        list(visualizer_image_center),
                        visualizer_image_corner_roundness,
                        visualizer_image_bottom_fade,
                        visualizer_image_database_data,
                        visualizer_image_database_name,
                    )
                    try:
                        with open(image_path, "rb") as image_file:
                            selected_image_database_data = image_file.read()
                    except Exception as error:
                        selected_image_database_data = None
                        print(f"Could not read selected image for database saving: {error}")
                    if load_visualizer_image(
                        image_path,
                        reset_position=True,
                        database_data=selected_image_database_data,
                        database_name=os.path.basename(image_path),
                    ):
                        visualizer_image_editing = True
                        visualizer_image_dragging = False
                    controls_open = False
                    status_open = False
                    active_slider = None

            for event in pygame.event.get():

                # Mouse movement only reveals Home; it must NOT consume the
                # MOUSEMOTION event because sliders and image dragging also use it.
                if event.type == pygame.MOUSEMOTION:
                    home_reveal_until = time.perf_counter() + 1.2

                if event.type == pygame.QUIT:

                    running = False  # Close the window normally

                elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                    mouse_x, mouse_y = event.pos  # Read the mouse position when the user clicks

                    # The color-picker eyedropper temporarily hides its Tk window and
                    # lets the Pygame loop receive the next click. Consume that click
                    # so it cannot activate normal visualizer controls.
                    with _color_pick_lock:
                        color_pick_active = _color_pick_request

                    if color_pick_active:
                        picked_rgb = get_current_image_pixel(mouse_x, mouse_y)
                        if picked_rgb is not None:
                            with _color_pick_lock:
                                _color_pick_result = picked_rgb
                        continue

                    if home_button_rect.collidepoint(mouse_x, mouse_y):
                        running = False  # Return to the launcher Home screen
                        new_song_requested = None  # Do not treat Home as a song change
                    elif song_button_rect.collidepoint(mouse_x, mouse_y):
                        select_audio_file_async()  # Open the song picker without blocking the visualizer
                        controls_open = False  # Close the controls menu while choosing a new song
                        status_open = False  # Close the status panel while choosing a new song
                        active_slider = None  # Stop any slider interaction while the picker is open
                    elif image_button_rect.collidepoint(mouse_x, mouse_y):
                        # Open the native image-selection dialog without blocking the
                        # Pygame loop, exactly like Select Song.
                        select_image_file_async()
                        controls_open = False
                        status_open = False
                        active_slider = None
                    elif visualizer_image_editing and image_save_button_rect.collidepoint(mouse_x, mouse_y):
                        # Persist the selected image/GIF and its exact size/position for this song.
                        if save_song_visualizer_image():
                            visualizer_image_editing = False
                            visualizer_image_dragging = False
                            visualizer_image_edit_backup = None
                        else:
                            show_error_message(
                                "The One - Image Save Error",
                                "Could not save the selected image for this song."
                            )
                    elif visualizer_image_editing and image_cancel_button_rect.collidepoint(mouse_x, mouse_y):
                        # Restore exactly what was present before the latest image selection.
                        if visualizer_image_edit_backup is not None:
                            (
                                visualizer_image_frames,
                                visualizer_image_delays,
                                visualizer_image_is_gif,
                                visualizer_image_path,
                                visualizer_image_started_at,
                                visualizer_image_size,
                                visualizer_image_center,
                                visualizer_image_corner_roundness,
                                visualizer_image_bottom_fade,
                                visualizer_image_database_data,
                                visualizer_image_database_name,
                            ) = visualizer_image_edit_backup
                        else:
                            visualizer_image_frames = []
                            visualizer_image_delays = []
                            visualizer_image_is_gif = False
                            visualizer_image_path = None
                            visualizer_image_database_data = None
                            visualizer_image_database_name = None
                            visualizer_image_corner_roundness = 0.0
                            visualizer_image_bottom_fade = 0.0
                        visualizer_image_editing = False
                        visualizer_image_dragging = False
                        visualizer_image_edit_backup = None
                    elif visualizer_image_editing and image_corner_button_rect.collidepoint(mouse_x, mouse_y):
                        # Cycle through clean, anti-aliased corner amounts without changing image pixels.
                        corner_levels = (0.0, 0.10, 0.20, 0.30)
                        current_level = min(range(len(corner_levels)), key=lambda index: abs(corner_levels[index] - visualizer_image_corner_roundness))
                        visualizer_image_corner_roundness = corner_levels[(current_level + 1) % len(corner_levels)]
                    elif visualizer_image_editing and image_fade_button_rect.collidepoint(mouse_x, mouse_y):
                        # Cycle through progressively stronger black gradients from the bottom.
                        fade_levels = (0.0, 0.25, 0.45, 0.65, 0.90, 0.98)
                        current_level = min(range(len(fade_levels)), key=lambda index: abs(fade_levels[index] - visualizer_image_bottom_fade))
                        visualizer_image_bottom_fade = fade_levels[(current_level + 1) % len(fade_levels)]
                    elif visualizer_image_editing and image_size_slider_rect.collidepoint(mouse_x, mouse_y):
                        # Start resizing immediately from the clicked point on the image-size slider.
                        normalized = max(0.0, min(1.0, (mouse_x - image_size_slider_left) / max(1.0, image_size_slider_right - image_size_slider_left)))
                        visualizer_image_size = 0.10 + normalized * (get_visualizer_image_max_size() - 0.10)
                        image_size_slider_active = True
                    elif visualizer_image_editing and get_visualizer_image_rect() is not None and get_visualizer_image_rect().collidepoint(mouse_x, mouse_y):
                        # Grab the image at its current point so it can be dragged anywhere.
                        visualizer_image_dragging = True
                        image_rect_for_drag = get_visualizer_image_rect()
                        visualizer_image_drag_offset = (
                            mouse_x - image_rect_for_drag.centerx,
                            mouse_y - image_rect_for_drag.centery,
                        )
                    elif status_button_rect.collidepoint(mouse_x, mouse_y):
                        status_open = not status_open  # Open or close the song details/status panel
                        controls_open = False  # Keep only one panel open at a time
                        active_slider = None
                    elif lyrics_button_rect.collidepoint(mouse_x, mouse_y):
                        # Toggle the lyrics display. The data is loaded/cached in the
                        # background using lyrics.py's standalone audio lookup path.
                        lyrics_visible = not lyrics_visible
                        active_slider = None
                    elif calm_button_rect.collidepoint(mouse_x, mouse_y):
                        if not calm_mode:
                            # Show a short notification directly beneath the Calm button.
                            calm_mode_notice_started = time.perf_counter()
                            calm_mode_notice_until = calm_mode_notice_started + 1.2
                            calm_mode_notice_message = "Calm mode enabled"

                            # Save the user's exact normal settings so Calm mode can change them temporarily.
                            calm_mode_saved_settings = (
                                bar_gap_setting,
                                curvature_setting,
                                wave_height_setting,
                                overall_opacity_setting,
                                center_width_setting,
                                center_opacity_setting,
                                bass_opacity_setting,
                                calmness_setting,
                            )

                            # Apply the dedicated Calm-mode appearance settings.
                            # These values are temporary and are never written to the song's saved settings.
                            bar_gap_setting = 0.0
                            curvature_setting = 0.75
                            wave_height_setting = 4
                            overall_opacity_setting = 0.80
                            center_width_setting = 0.25
                            center_opacity_setting = 0.80
                            # Calm mode uses 35% from the system 40% default, or 75% from the system 80% default.
                            calm_bass_default = get_automatic_bass_opacity(SECONDARY_VIBE_COLOR)
                            bass_opacity_setting = float(np.clip(calm_bass_default - 0.05, 0.0, 1.0))

                            # Start at 10/10, but this remains user-adjustable while Calm mode is on.
                            calmness_setting = 10
                            calm_mode = True
                        else:
                            # Show a short notification directly beneath the Calm button.
                            calm_mode_notice_started = time.perf_counter()
                            calm_mode_notice_until = calm_mode_notice_started + 1.2
                            calm_mode_notice_message = "Calm mode disabled"

                            # Restore every setting exactly to what it was before Calm mode was enabled.
                            if calm_mode_saved_settings is not None:
                                (
                                    bar_gap_setting,
                                    curvature_setting,
                                    wave_height_setting,
                                    overall_opacity_setting,
                                    center_width_setting,
                                    center_opacity_setting,
                                    bass_opacity_setting,
                                    calmness_setting,
                                ) = calm_mode_saved_settings
                            calm_mode_saved_settings = None
                            calm_mode = False

                        active_slider = None
                    elif menu_button_rect.collidepoint(mouse_x, mouse_y):
                        controls_open = not controls_open  # Open or close the controls menu
                        status_open = False  # Close the status panel when opening controls
                        active_slider = None  # Stop dragging when the menu state changes
                    elif color_button_rect.collidepoint(mouse_x, mouse_y):
                        controls_open = False  # Close the bar controls while choosing custom colors
                        status_open = False  # Close the status panel while choosing custom colors
                        active_slider = None  # Stop any slider interaction before opening the picker
                        choose_custom_colors(screen)  # Open the wave and bass color pickers
                    elif status_open:
                        status_panel_width = 450
                        status_panel_x = max(20, calm_button_rect.right - status_panel_width)
                        status_settings_y = get_status_settings_y()
                        status_panel_height = status_settings_y + 38 + (365 if status_details_open else 43)
                        status_panel_rect = pygame.Rect(status_panel_x, 50, status_panel_width, status_panel_height + 38)
                        status_drop_rect = pygame.Rect(status_panel_x + 290, status_settings_y + 33, 30, 30)
                        if status_drop_rect.collidepoint(mouse_x, mouse_y):
                            status_details_open = not status_details_open  # Expand or collapse the settings-change details
                        elif not status_panel_rect.collidepoint(mouse_x, mouse_y):
                            status_open = False
                            active_slider = None
                            continue
                    elif controls_open:
                        panel_width = 600  # Give the controllers and vertical button stack their own space
                        panel_x = max(20, calm_button_rect.right - panel_width)  # Align the right edge directly under Calm
                        panel_rect = pygame.Rect(panel_x, 50, panel_width, 550)  # Fit all eight controllers and the right-side button stack
                        if not panel_rect.collidepoint(mouse_x, mouse_y):
                            controls_open = False  # Close the controls box when clicking outside it
                            active_slider = None  # Stop any slider interaction when the box closes
                            continue  # Ignore the outside click so it does not change anything else
                        slider_left = panel_x + 205  # Set the left end of each slider
                        slider_right = panel_x + 425  # Set the right end of each slider
                        slider_y_positions = {
                            "gap": 118,
                            "curvature": 168,
                            "wave_height": 218,
                            "overall": 268,
                            "center_width": 318,
                            "center_opacity": 368,
                            "bass_opacity": 418,
                            "calmness": 468,
                        }  # Keep all eight sliders compact enough to fit the menu
                        button_x = panel_x + 450
                        button_width = 132
                        button_gap = 12
                        button_y = 207  # Center the four-button stack on the midpoint of the eight controllers
                        default_width = 92
                        undo_gap = 8
                        undo_size = 34
                        default_rect = pygame.Rect(button_x, button_y, default_width, 34)
                        undo_rect = pygame.Rect(button_x + default_width + undo_gap, button_y, undo_size, undo_size)
                        save_default_rect = pygame.Rect(button_x, button_y + (34 + button_gap), button_width, 34)
                        save_colors_rect = pygame.Rect(button_x, button_y + 2 * (34 + button_gap), button_width, 34)
                        bass_default_rect = pygame.Rect(button_x, button_y + 3 * (34 + button_gap), button_width, 34)
                        remove_image_rect = pygame.Rect(button_x, button_y + 4 * (34 + button_gap), button_width, 34)

                        if default_rect.collidepoint(mouse_x, mouse_y):
                            # Factory Default must always restore the factory values.
                            # Do not read any song-specific saved settings here.
                            bar_gap_setting = default_bar_gap
                            curvature_setting = default_curvature
                            wave_height_setting = default_wave_height
                            overall_opacity_setting = default_overall_opacity
                            center_width_setting = default_center_width
                            center_opacity_setting = default_center_opacity
                            bass_opacity_setting = default_bass_opacity
                            calmness_setting = default_calmness
                            active_slider = None  # Stop any slider interaction after applying the default settings
                        elif undo_rect.collidepoint(mouse_x, mouse_y):
                            if calm_mode:
                                # While Calm mode is active, Undo should restore the original
                                # dedicated Calm-mode settings, not the song's normal settings.
                                bar_gap_setting = 0.0
                                curvature_setting = 0.75
                                wave_height_setting = 4
                                overall_opacity_setting = 0.80
                                center_width_setting = 0.25
                                center_opacity_setting = 0.80
                                calm_bass_default = get_automatic_bass_opacity(SECONDARY_VIBE_COLOR)
                                bass_opacity_setting = float(np.clip(calm_bass_default - 0.05, 0.0, 1.0))
                                calmness_setting = 10
                            elif undo_song_settings is not None:
                                # Outside Calm mode, restore the song's normal Undo baseline.
                                (
                                    bar_gap_setting,
                                    curvature_setting,
                                    wave_height_setting,
                                    overall_opacity_setting,
                                    center_width_setting,
                                    center_opacity_setting,
                                    bass_opacity_setting,
                                    calmness_setting,
                                ) = undo_song_settings
                            active_slider = None  # Stop any slider interaction after Undo
                        elif save_default_rect.collidepoint(mouse_x, mouse_y):
                            save_current_song_colors()  # Save the current colors and the selected Bass opacity together for this song
                            active_slider = None  # Stop any slider interaction after saving the default settings
                        elif save_colors_rect.collidepoint(mouse_x, mouse_y):
                            save_current_song_colors()  # Save the current Wave/Bass colors specifically for this song
                            active_slider = None  # Stop any slider interaction after saving the song colors
                        elif remove_image_rect.collidepoint(mouse_x, mouse_y):
                            # Permanently remove this song's saved image from the same SQLite database.
                            try:
                                database_path = vibe_detector.initialize_vibe_database()
                                fingerprint_key = get_song_image_database_key()
                                with sqlite3.connect(database_path) as connection:
                                    ensure_song_image_table(connection)
                                    connection.execute(
                                        "DELETE FROM visualizer_song_images WHERE fingerprint_key = ?",
                                        (fingerprint_key,),
                                    )
                                visualizer_image_frames = []
                                visualizer_image_delays = []
                                visualizer_image_is_gif = False
                                visualizer_image_path = None
                                visualizer_image_started_at = 0.0
                                visualizer_image_size = 0.20
                                visualizer_image_center = [width / 2.0, height / 2.0]
                                visualizer_image_corner_roundness = 0.0
                                visualizer_image_bottom_fade = 0.0
                                visualizer_image_database_data = None
                                visualizer_image_database_name = None
                                visualizer_image_editing = False
                                visualizer_image_dragging = False
                                visualizer_image_edit_backup = None
                                visualizer_image_center_snap_x = False
                                visualizer_image_center_snap_y = False
                                image_size_slider_active = False
                                print(f"Visualizer image permanently removed for: {source_path}")
                            except Exception as error:
                                print(f"Could not remove visualizer image: {error}")
                                show_error_message(
                                    "The One - Image Remove Error",
                                    f"Could not remove the saved image:\n\n{error}"
                                )
                            active_slider = None
                        elif bass_default_rect.collidepoint(mouse_x, mouse_y):
                            bass_opacity_setting = get_automatic_bass_opacity(
                                SECONDARY_VIBE_COLOR
                            )  # Reset only Bass opacity to the factory automatic 40%/80% color-based value
                            try:
                                vibe_detector.save_song_bass_opacity(
                                    source_path,
                                    bass_opacity_setting,
                                )  # Also save the factory Bass opacity for this exact song
                                saved_song_bass_opacity = float(bass_opacity_setting)
                            except Exception as error:
                                print(f"Could not save factory Bass opacity: {error}")  # Keep the reset working even if saving fails
                            active_slider = None  # Stop any slider interaction after resetting Bass opacity
                        else:
                            for slider_name, slider_y in slider_y_positions.items():
                                # Use a generous hit area around the visible track so a click anywhere
                                # on the slider immediately moves the knob to that exact position.
                                slider_rect = pygame.Rect(
                                    slider_left - 16,
                                    slider_y - 20,
                                    slider_right - slider_left + 32,
                                    40,
                                )
                                if slider_rect.collidepoint(mouse_x, mouse_y):
                                    # Calm mode settings are temporary, but all sliders remain user-adjustable.
                                    # Any changes made here are discarded when Calm mode is turned off.
                                    active_slider = slider_name  # Start dragging this slider
                                    normalized = max(
                                        0.0,
                                        min(
                                            1.0,
                                            (mouse_x - slider_left)
                                            / max(1.0, slider_right - slider_left),
                                        ),
                                    )  # Convert the clicked horizontal position to 0-100%
                                    if slider_name == "gap":
                                        bar_gap_setting = round(normalized * 10.0)  # Allow a 0-to-10 pixel gap
                                    elif slider_name == "curvature":
                                        curvature_setting = normalized  # Move Curvature exactly to the clicked point
                                    elif slider_name == "wave_height":
                                        wave_height_setting = max(1, min(10, int(round(1.0 + normalized * 9.0))))  # Move Overall height from 1 to 10
                                    elif slider_name == "overall":
                                        overall_opacity_setting = normalized  # Allow 0%-100% overall opacity
                                    elif slider_name == "center_width":
                                        center_width_setting = normalized  # Allow 0%-100% center width
                                    elif slider_name == "center_opacity":
                                        center_opacity_setting = normalized  # Allow 0%-100% center opacity
                                    elif slider_name == "bass_opacity":
                                        bass_opacity_setting = normalized  # Allow Bass opacity changes in both modes
                                    elif slider_name == "calmness":
                                        calmness_setting = int(round(normalized * 10.0))  # Allow Calmness from 0 to 10
                                    break

                elif event.type == pygame.MOUSEBUTTONUP and event.button == 1:
                    active_slider = None  # Stop moving a settings slider when the mouse button is released
                    image_size_slider_active = False
                    visualizer_image_dragging = False
                    # Keep the final snapped position, but hide alignment guides until dragging resumes.
                    visualizer_image_center_snap_x = False
                    visualizer_image_center_snap_y = False

                elif event.type == pygame.MOUSEMOTION and visualizer_image_editing and image_size_slider_active:
                    mouse_x, mouse_y = event.pos
                    normalized = max(0.0, min(1.0, (mouse_x - image_size_slider_left) / max(1.0, image_size_slider_right - image_size_slider_left)))
                    visualizer_image_size = 0.10 + normalized * (get_visualizer_image_max_size() - 0.10)

                elif event.type == pygame.MOUSEMOTION and visualizer_image_editing and visualizer_image_dragging:
                    mouse_x, mouse_y = event.pos

                    # Move normally first, then apply a small magnetic snap when the
                    # image center gets close to the exact center of the screen.
                    candidate_x = mouse_x - visualizer_image_drag_offset[0]
                    candidate_y = mouse_y - visualizer_image_drag_offset[1]
                    screen_center_x = width / 2.0
                    screen_center_y = height / 2.0
                    center_snap_distance = 12.0  # Pixels of magnetic range around center

                    if abs(candidate_x - screen_center_x) <= center_snap_distance:
                        visualizer_image_center[0] = screen_center_x
                        visualizer_image_center_snap_x = True
                    else:
                        visualizer_image_center[0] = candidate_x
                        visualizer_image_center_snap_x = False

                    if abs(candidate_y - screen_center_y) <= center_snap_distance:
                        visualizer_image_center[1] = screen_center_y
                        visualizer_image_center_snap_y = True
                    else:
                        visualizer_image_center[1] = candidate_y
                        visualizer_image_center_snap_y = False

                elif event.type == pygame.MOUSEMOTION and controls_open and active_slider is not None:
                    mouse_x, mouse_y = event.pos  # Read the current mouse position while dragging
                    width, height = screen.get_size()  # Read the current window size
                    panel_width = 600
                    panel_x = max(20, calm_button_rect.right - panel_width)  # Keep the controls panel aligned under Calm
                    slider_left = panel_x + 205  # Set the left end of each slider
                    slider_right = panel_x + 425  # Set the right end of each slider
                    normalized = max(0.0, min(1.0, (mouse_x - slider_left) / max(1.0, slider_right - slider_left)))  # Convert horizontal movement into a percentage
                    if active_slider == "gap":
                        bar_gap_setting = round(normalized * 10.0)  # Move the gap between 0 and 10 pixels
                    elif active_slider == "curvature":
                        curvature_setting = normalized  # Move wave curvature between 0% and 100%
                    elif active_slider == "wave_height":
                        wave_height_setting = max(1, min(10, int(round(1.0 + normalized * 9.0))))  # Move Overall height between 1 and 10
                    elif active_slider == "overall":
                        overall_opacity_setting = normalized  # Move overall opacity between 0% and 100%
                    elif active_slider == "center_width":
                        center_width_setting = normalized  # Move the center section between 0% and 100%
                    elif active_slider == "center_opacity":
                        center_opacity_setting = normalized  # Move center opacity between 0% and 100%
                    elif active_slider == "bass_opacity":
                        bass_opacity_setting = normalized  # Move Bass opacity in both modes
                    elif active_slider == "calmness":
                        calmness_setting = int(round(normalized * 10.0))  # Move Calmness between 0 and 10

                elif event.type == pygame.KEYDOWN:

                    if event.key == pygame.K_ESCAPE:

                        running = False  # Close the visualizer with Escape

                    elif event.key == pygame.K_SPACE:

                        if playing:

                            pygame.mixer.music.pause()  # Pause playback manually

                            playing = False  # Remember that playback is paused

                            user_paused = True  # Remember that the user caused the pause

                        else:

                            pygame.mixer.music.unpause()  # Resume playback manually

                            playing = True  # Remember that playback is active

                            user_paused = False  # Allow automatic analysis control again

                    elif event.key == pygame.K_LEFT:

                        current_position = song_position  # Use the synchronized logical song position instead of the mixer-relative timer

                        new_position = max(
                            0.0,
                            current_position - 10.0
                        )  # Move 10 seconds backward without going below zero

                        was_playing = playing  # Remember whether the user was playing before seeking

                        seek_offset = new_position  # Make the new mixer-relative position represent the real song position

                        pygame.mixer.music.play(
                            start=seek_offset
                        )  # Restart playback exactly at the requested song position

                        if not was_playing:

                            pygame.mixer.music.pause()  # Keep the song paused if it was paused before seeking

                        song_position = new_position  # Immediately move the visualizer to the same song position
                        position_clock = time.perf_counter()  # Reset the compatibility timestamp after seeking

                        displayed_wave_heights = None  # Drop the old wave so a seek cannot visually blend from the wrong moment

                        smooth_bass_background = 0.0  # Clear the old bass glow so the new position starts cleanly

                    elif event.key == pygame.K_RIGHT:

                        current_position = song_position  # Use the synchronized logical song position instead of the mixer-relative timer

                        new_position = min(
                            current_position + 10.0,
                            state.song_duration
                        )  # Move 10 seconds forward without passing the end of the song

                        was_playing = playing  # Remember whether the user was playing before seeking

                        seek_offset = new_position  # Make the new mixer-relative position represent the real song position

                        pygame.mixer.music.play(
                            start=seek_offset
                        )  # Restart playback exactly at the requested song position

                        if not was_playing:

                            pygame.mixer.music.pause()  # Keep the song paused if it was paused before seeking

                        song_position = new_position  # Immediately move the visualizer to the same song position
                        position_clock = time.perf_counter()  # Reset the compatibility timestamp after seeking

                        displayed_wave_heights = None  # Drop the old wave so a seek cannot visually blend from the wrong moment

                        smooth_bass_background = 0.0  # Clear the old bass glow so the new position starts cleanly

            if not running:

                break  # Leave the loop after a close request

            # ------------------------------------------------
            # CURRENT PLAYBACK POSITION
            # ------------------------------------------------

            if playing:
                mixer_position = pygame.mixer.music.get_pos() / 1000.0  # Read Pygame's actual audio playback clock in seconds
                if mixer_position >= 0.0:
                    song_position = seek_offset + mixer_position  # Use the audio clock as the master timing source

            current_time = max(
                0.0,
                min(song_position, state.song_duration)
            )  # Keep analysis and visuals locked to the real audio position

            # ------------------------------------------------
            # CHECK ANALYSIS PROGRESS
            # ------------------------------------------------

            with state.lock:

                analyzed_frames = state.analyzed_frames  # Get ready frames

                finished = state.finished  # Check whether analysis finished

            analyzed_seconds = (
                analyzed_frames
                * state.chunk_duration
            )  # Convert ready frames to seconds

            # ------------------------------------------------
            # PREVENT PLAYBACK FROM OVERTAKING ANALYSIS
            # ------------------------------------------------

            if (
                playing
                and not finished
                and not user_paused
            ):

                if analyzed_seconds < (
                    current_time
                    + MIN_ANALYSIS_AHEAD_SECONDS
                ):

                    pygame.mixer.music.pause()  # Pause temporarily if analysis falls behind

                    playing = False  # Remember that playback is temporarily paused
                    position_clock = time.perf_counter()  # Record the pause moment for compatibility

            elif (
                not playing
                and not finished
                and not user_paused
            ):

                if analyzed_seconds >= (
                    current_time
                    + MIN_ANALYSIS_AHEAD_SECONDS
                ):

                    pygame.mixer.music.unpause()  # Resume when analysis catches up

                    position_clock = time.perf_counter()  # Record the automatic resume moment for compatibility
                    playing = True  # Remember that playback is active again

            # ------------------------------------------------
            # GET CURRENT NOTE DATA
            # ------------------------------------------------

            song_position = current_time  # Keep the stored position synchronized with the mixer-derived time

            note_values = get_current_note(
                state,
                current_time
            )  # Get the piano notes for this moment

            # ------------------------------------------------
            # CLEAR SCREEN
            # ------------------------------------------------

            bass_level = get_bass_background_level(
                current_time
            )  # Get the independent smooth bass level for the background

            width, height = screen.get_size()  # Get the current window size

            # Start from the normal black/idle background, then place the selected image on it.
            # The bass effect is drawn afterward as a transparent overlay, so the image stays behind it.
            screen.fill(BACKGROUND_IDLE)

            if visualizer_image_frames:
                if visualizer_image_is_gif and len(visualizer_image_frames) > 1:
                    elapsed_ms = int((time.perf_counter() - visualizer_image_started_at) * 1000.0)
                    total_ms = max(1, sum(visualizer_image_delays))
                    frame_time = elapsed_ms % total_ms
                    accumulated_ms = 0
                    frame_index = 0
                    for index, delay in enumerate(visualizer_image_delays):
                        accumulated_ms += delay
                        if frame_time < accumulated_ms:
                            frame_index = index
                            break
                    image_surface = visualizer_image_frames[frame_index]
                else:
                    image_surface = visualizer_image_frames[0]

                image_height = max(80, int(round(height * visualizer_image_size)))
                source_width, source_height = image_surface.get_size()
                if source_height > 0:
                    image_width = max(1, int(round(source_width * image_height / source_height)))
                    scaled_image = pygame.transform.smoothscale(image_surface, (image_width, image_height))
                    scaled_image = apply_rounded_image_corners(
                        scaled_image,
                        visualizer_image_corner_roundness,
                    )
                    scaled_image = apply_bottom_image_fade(
                        scaled_image,
                        visualizer_image_bottom_fade,
                    )
                    image_rect = scaled_image.get_rect(
                        center=(int(round(visualizer_image_center[0])), int(round(visualizer_image_center[1])))
                    )
                    screen.blit(scaled_image, image_rect)

            draw_bass_background(
                screen,
                bass_level,
                bass_opacity_setting=bass_opacity_setting,
                clear_screen=False,
            )  # Overlay the bass color without erasing the image underneath

            # ------------------------------------------------
            # WAVE BASELINE
            # ------------------------------------------------

            baseline = height  # Let the blanket reach the very bottom so no black strip is left below it

            key_width = (
                width / PIANO_KEYS
            )  # Calculate each piano section's width

            # ------------------------------------------------
            # DRAW THE ACTIVE PIANO NOTE AS ONE FULL-WIDTH WAVE
            # ------------------------------------------------
            #
            # The important idea here is that ZERO-height piano keys are
            # not treated as little mountains that force the blanket back
            # to the floor. Only the currently active note creates the peak.
            #
            # The peak stays exactly where the original bar was, while its
            # smooth bell-shaped surface stretches all the way from the
            # left edge of the screen to the right edge.
            # ------------------------------------------------

            active_keys = np.flatnonzero(
                note_values > 0.0
            )  # Find the piano notes that are actually active right now

            wave_samples = max(
                160,
                width // 3
            )  # Use enough samples so the curve stays smooth across the whole screen

            # Build the wave that THIS frame wants to show.
            target_wave_heights = np.zeros(
                wave_samples + 1,
                dtype=np.float32
            )  # Store the new target shape separately from the visible shape

            if len(active_keys) > 0:
                active_heights = np.asarray(
                    [
                        float(note_values[key_index]) * height * WAVE_HEIGHT
                        for key_index in active_keys
                    ],
                    dtype=np.float32
                )  # Convert active note values into the original bar heights before the overall-height control

                active_x = (active_keys.astype(np.float32) + 0.5) * key_width  # Put every wave peak at its original bar center

                peak_volume = float(np.max(active_heights))  # Measure the loudest active note's current volume
                volume_ratio = np.clip(peak_volume, 0.0, 1.0)  # Convert the volume into a safe 0-to-1 range
                # The curvature slider must directly control the horizontal spread of each peak.
                # The previous formula only multiplied the volume-dependent widening, so at high
                # volume (volume_ratio near 1) the slider effectively did nothing.
                volume_widening = 1.0 + (1.0 - volume_ratio) * 1.5  # Keep the existing quiet-note widening
                user_curvature = 0.20 + (1.60 * curvature_setting)  # 0%=very pointy, 50%=factory shape, 100%=very broad
                curvature_factor = volume_widening * user_curvature  # Combine both effects
                base_crest_width = max(width * 0.055, key_width * 2.6)  # Keep the same minimum crest width
                crest_width = base_crest_width * curvature_factor  # Apply the user-selected wave curvature

                x_positions = (
                    np.arange(wave_samples + 1, dtype=np.float32)
                    / float(wave_samples)
                ) * width  # Build every horizontal sample position in one NumPy operation

                distances = np.abs(
                    x_positions[None, :] - active_x[:, None]
                )  # Calculate all peak distances at once
                normalized_distance = distances / crest_width  # Normalize every distance by the crest width
                squared_distance = normalized_distance * normalized_distance  # Reuse the squared distance for both profiles

                main_peak = np.exp(-squared_distance)  # Build all rounded main crests at once
                side_profile = (
                    1.0 - main_peak
                ) * np.exp(
                    -((distances / (crest_width * 3.2)) ** 2)
                )  # Build all smooth shoulders at once
                broad_elevation = 0.16 * np.exp(
                    -((distances / (crest_width * 7.0)) ** 2)
                )  # Build the broad wave body at once

                combined_profile = (
                    main_peak
                    + 0.28 * side_profile
                    + broad_elevation
                ) / 1.16  # Keep the original peak height normalization

                candidate_heights = (
                    active_heights[:, None] * combined_profile
                )  # Convert every peak profile into its actual wave height
                candidate_heights *= (0.50 + 0.50 * ((wave_height_setting - 1.0) / 9.0))  # Scale the complete wave from 50% at 1/10 to 100% at 10/10 without changing curvature
                target_wave_heights[:] = np.max(
                    candidate_heights,
                    axis=0
                )  # Keep the tallest active note at every horizontal position
            # ------------------------------------------------
            # SMOOTH WAVE TRANSITIONS
            # ------------------------------------------------
            #
            # Do NOT replace the old wave instantly when the detected note changes.
            # Instead, move the visible wave toward the new target a little at a time.
            # This makes the old peak travel downward smoothly while the new peak
            # rises smoothly, avoiding the harsh frame-to-frame disappearance.
            # ------------------------------------------------

            if (
                displayed_wave_heights is None
                or displayed_wave_width != width
                or len(displayed_wave_heights) != len(target_wave_heights)
            ):
                displayed_wave_heights = target_wave_heights.copy()  # Start cleanly when the window size changes
                displayed_wave_width = width  # Remember the sample width of the stored wave
            else:
                calmness_level = float(np.clip(calmness_setting, 0.0, 10.0)) / 10.0  # Convert Calmness 0-10 to a 0-1 smoothing amount

                rise_amount = 0.24 - (0.14 * calmness_level)  # Gradually slow rising peaks from raw to full Calm mode
                fall_amount = 0.22 - (0.14 * calmness_level)  # Gradually slow falling peaks from raw to full Calm mode

                rising = target_wave_heights > displayed_wave_heights  # Find parts that need to rise

                displayed_wave_heights[rising] += (
                    target_wave_heights[rising] - displayed_wave_heights[rising]
                ) * rise_amount  # Ease new wave sections upward instead of popping in

                falling = ~rising  # The remaining sections need to stay still or fall

                displayed_wave_heights[falling] += (
                    target_wave_heights[falling] - displayed_wave_heights[falling]
                ) * fall_amount  # Ease old wave sections downward for a soft fade-out

            displayed_wave_heights[0] = 0.0  # Keep the left corner anchored to the bottom edge
            displayed_wave_heights[-1] = 0.0  # Keep the right corner anchored to the bottom edge

            # DRAW THE SAME WAVE AS 88 SEPARATE POINTED BARS
            # ------------------------------------------------
            # Reuse cached alpha surfaces so the visualizer does not rebuild large NumPy masks 88 times per frame.

            bar_gap = bar_gap_setting  # Use the gap selected in the controls menu
            key_width = width / PIANO_KEYS  # Keep the original piano-key spacing across the screen
            bar_width = max(1.0, key_width - bar_gap)  # Make each bar narrower only to create the selected gaps

            cache_settings = (
                int(round(bar_width)),
                round(overall_opacity_setting, 3),
                round(center_width_setting, 3),
                round(center_opacity_setting, 3),
                PRIMARY_VIBE_COLOR,
            )  # Group all settings that affect a cached bar shape

            for key_index in range(PIANO_KEYS):
                center_x = (float(key_index) + 0.5) * key_width  # Keep the original bar center

                sample_position = (center_x / float(width)) * wave_samples  # Convert the bar center into the wave sample position
                left_sample = int(sample_position)  # Find the wave sample on the left
                left_sample = max(0, min(wave_samples, left_sample))  # Keep the sample inside the wave array
                right_sample = min(left_sample + 1, wave_samples)  # Find the wave sample on the right
                interpolation = sample_position - left_sample  # Find the position between the two samples

                sampled_height = (
                    displayed_wave_heights[left_sample] * (1.0 - interpolation)
                    + displayed_wave_heights[right_sample] * interpolation
                )  # Sample the exact same smoothed wave

                bar_height = max(0.0, float(sampled_height))  # Keep the height valid

                if bar_height <= 0.0:
                    continue  # Do not draw silent bars

                left_x = int(round(center_x - bar_width / 2.0))  # Calculate the left edge while keeping the gap
                right_x = int(round(center_x + bar_width / 2.0)) - 1  # Calculate the right edge without filling the gap
                right_x = max(left_x, min(width - 1, right_x))  # Keep the bar inside the screen
                actual_width = right_x - left_x + 1  # Get the exact number of pixels occupied by this bar

                # Keep the cached bar height to the nearest pixel so bars follow the smooth wave without visible stepping.
                render_height = max(1, int(round(bar_height)))  # Preserve one-pixel height changes for natural motion
                render_height = min(render_height, baseline)  # Never render below the floor

                cache_key = cache_settings + (actual_width, render_height)  # Identify an exact reusable bar surface
                bar_surface = bar_surface_cache.get(cache_key)  # Reuse the surface when this height/settings combination already exists

                if bar_surface is None:
                    top_y = max(0, baseline - render_height)  # Find the top of the cached bar
                    local_baseline = render_height  # Store the local bar height
                    local_center = (actual_width - 1) / 2.0  # Find the horizontal center
                    point_depth = max(1, int(min(render_height * 0.12, max(1.0, actual_width * 0.45))))  # Keep the pointed tip shallow
                    local_shoulder = point_depth  # Keep the solid bar beginning just below the point

                    bar_surface = pygame.Surface(
                        (actual_width, local_baseline + 1),
                        pygame.SRCALPHA
                    )  # Create the cached transparent bar before building its mask

                    surface_width, surface_height = bar_surface.get_size()  # Read the exact Pygame dimensions so the NumPy mask cannot disagree
                    x_positions = np.arange(surface_width, dtype=np.float32)  # Create horizontal positions from the actual surface width
                    normalized_x = x_positions / max(1.0, surface_width - 1)  # Convert x positions to 0-1

                    fade_width = max(0.0, min(1.0, center_width_setting))  # Read the adjustable center width
                    fade_start = (1.0 - fade_width) * 0.5  # Find where the center section starts
                    fade_end = 1.0 - fade_start  # Find where the center section ends
                    fade_span = max(0.0001, fade_start)  # Prevent division by zero
                    fade_end_span = max(0.0001, 1.0 - fade_end)  # Prevent division by zero

                    horizontal_fade = np.where(
                        normalized_x < fade_start,
                        normalized_x / fade_span,
                        np.where(
                            normalized_x <= fade_end,
                            1.0,
                            (1.0 - normalized_x) / fade_end_span
                        )
                    )  # Create the adjustable center fade
                    horizontal_fade = np.clip(horizontal_fade, 0.0, 1.0)  # Keep the fade valid
                    horizontal_fade = horizontal_fade * horizontal_fade * (3.0 - 2.0 * horizontal_fade)  # Smooth the horizontal transition

                    center_opacity = min(
                        overall_opacity_setting,
                        center_opacity_setting
                    )  # Cap the center at the overall opacity
                    horizontal_alpha = 255.0 * center_opacity * horizontal_fade  # Convert the horizontal fade into alpha values

                    y_positions = np.arange(surface_height, dtype=np.float32)  # Create vertical positions from the actual surface height
                    row_ratio = (y_positions + 0.5) / max(1.0, local_baseline)  # Measure each row from top toward bottom
                    vertical_fade = np.clip(row_ratio, 0.0, 1.0)  # Keep the vertical fade between zero and one
                    vertical_fade = vertical_fade * vertical_fade * (3.0 - 2.0 * vertical_fade)  # Smooth the bottom-to-top fade

                    if surface_width > 1:
                        center_fraction = np.where(
                            x_positions <= local_center,
                            x_positions / max(1.0, local_center),
                            (surface_width - 1 - x_positions) / max(1.0, (surface_width - 1) - local_center)
                        )  # Calculate the pointed-top shape using the real surface width
                    else:
                        center_fraction = np.ones(1, dtype=np.float32)  # Handle a one-pixel-wide bar safely

                    center_fraction = np.clip(center_fraction, 0.0, 1.0)

                    # ------------------------------------------------------------
                    # HEIGHT-BASED CURVATURE
                    # Short bars  = pointed
                    # Tall bars   = flatter / more rounded
                    # ------------------------------------------------------------

                    height_ratio = np.clip(
                        bar_height / max(1.0, height * 0.35),
                        0.0,
                        1.0
                    )

                    # 1.0 = original sharp point
                    # Smaller values = flatter, wider top
                    curve_exponent = 1.0 - (0.75 * height_ratio)

                    curved_fraction = center_fraction ** curve_exponent

                    strip_top = np.rint(
                        local_shoulder - curved_fraction * local_shoulder
                    ).astype(np.int32)
                    alpha_matrix = horizontal_alpha[:, None] * vertical_fade[None, :]  # Combine both fades in one NumPy operation
                    alpha_matrix *= y_positions[None, :] >= strip_top[:, None]  # Remove pixels outside the pointed shape
                    alpha_matrix = np.clip(np.rint(alpha_matrix), 0, 255).astype(np.uint8)  # Convert to Pygame alpha values

                    bar_surface.fill(
                        (
                            PRIMARY_VIBE_COLOR[0],
                            PRIMARY_VIBE_COLOR[1],
                            PRIMARY_VIBE_COLOR[2],
                            0,
                        )
                    )  # Start with a transparent vibe-colored surface
                    alpha_pixels = pygame.surfarray.pixels_alpha(bar_surface)  # Access the alpha channel directly
                    alpha_pixels[:, :] = alpha_matrix  # Copy the complete alpha mask in one operation
                    del alpha_pixels  # Release the surface lock
                    bar_surface_cache[cache_key] = bar_surface  # Keep the finished surface for later frames

                top_y = max(0, baseline - render_height)  # Position the cached bar at the bottom edge
                screen.blit(bar_surface, (left_x, top_y))  # Draw the reusable bar with one fast blit
            # ------------------------------------------------
            # BAR CONTROLS MENU
            # ------------------------------------------------
            def draw_smooth_pill(surface, rect, fill_color, border_color, border_width=1):
                # Render the pill at 4x resolution so its curved edge is anti-aliased.
                scale = 4
                hi_rect = pygame.Rect(0, 0, rect.width * scale, rect.height * scale)
                hi_surface = pygame.Surface(hi_rect.size, pygame.SRCALPHA)
                pygame.draw.rect(hi_surface, fill_color, hi_rect, border_radius=rect.height * scale // 2)
                if border_width > 0:
                    pygame.draw.rect(hi_surface, border_color, hi_rect, border_width * scale, border_radius=rect.height * scale // 2)
                smooth_surface = pygame.transform.smoothscale(hi_surface, rect.size)
                surface.blit(smooth_surface, rect.topleft)

            def draw_smooth_rounded_border(surface, rect, color, width=1, radius=8, scale=4):
                # Draw the border at high resolution, then downsample it.
                # This removes the stair-stepped/pixelated edges from rounded UI borders.
                scale = max(2, int(scale))
                hi_size = (max(1, rect.width * scale), max(1, rect.height * scale))
                hi = pygame.Surface(hi_size, pygame.SRCALPHA)
                hi_rect = hi.get_rect()
                pygame.draw.rect(
                    hi,
                    color,
                    hi_rect,
                    width=max(1, int(width * scale)),
                    border_radius=max(1, int(radius * scale)),
                )
                smooth = pygame.transform.smoothscale(hi, rect.size)
                surface.blit(smooth, rect.topleft)

            def draw_glass_button(surface, rect, blurred_backdrop, hover=False, active=False, square=False):
                # Frosted-glass button rendered at high resolution and then downsampled
                # so the rounded corners are genuinely anti-aliased instead of stair-stepped.
                scale = 12
                hi_size = (max(1, rect.width * scale), max(1, rect.height * scale))
                hi = pygame.Surface(hi_size, pygame.SRCALPHA)

                # Scale the already-blurred backdrop up for the high-resolution pass.
                source = blurred_backdrop.subsurface(rect).copy()
                source_hi = pygame.transform.smoothscale(source, hi_size)
                hi.blit(source_hi, (0, 0))

                radius = 4 if square else rect.height // 2
                hi_rect = hi.get_rect()

                # Subtle translucent glass tint. Hover/active states are only slightly brighter.
                tint_alpha = 34 if not (hover or active) else 48
                pygame.draw.rect(
                    hi,
                    (235, 235, 245, tint_alpha),
                    hi_rect,
                    border_radius=max(1, radius * scale),
                )

                # Draw the border at the same high resolution as the rounded fill.
                border_alpha = 105 if not (hover or active) else 165
                pygame.draw.rect(
                    hi,
                    (245, 245, 255, border_alpha),
                    hi_rect,
                    width=scale,
                    border_radius=max(1, radius * scale),
                )

                smooth = pygame.transform.smoothscale(hi, rect.size)
                surface.blit(smooth, rect.topleft)

            width, height = screen.get_size()  # Read the current window size for the menu position

            # ------------------------------------------------
            # MUSIC PROGRESS INDICATOR — THIN CURVED TRIANGLE
            # ------------------------------------------------
            song_duration = max(0.0, float(state.song_duration))
            progress_fraction = (
                max(0.0, min(1.0, current_time / song_duration))
                if song_duration > 0.0
                else 0.0
            )
            progress_x = int(round(width * progress_fraction))

            # Small, delicate marker: wide enough at the top to read as a
            # curved triangle, but very narrow as it falls to the point.
            triangle_height = max(14, int(round(height * 0.022)))
            triangle_half_width = max(4, int(round(height * 0.0048)))

            # Keep the pointer itself inside the screen, but let its left/right
            # edge touch the screen edge at 0% / 100% progress.
            triangle_center_x = max(
                triangle_half_width,
                min(width - triangle_half_width, progress_x),
            ) if width > triangle_half_width * 2 else width // 2

            def curved_side(center, half_width, tri_height, side=1, samples=48):
                """Smooth concave side from the top edge to one sharp point."""
                points = []
                for i in range(samples + 1):
                    t = i / samples
                    # Ease the sides inward smoothly.  The sides stay fairly
                    # straight through the lower half and converge sharply at
                    # the bottom point, like the hand-drawn reference.
                    inward = (1.0 - t) ** 1.55
                    curve = 0.18 * math.sin(math.pi * t) * (1.0 - t)
                    x_offset = half_width * max(0.0, inward - curve)
                    y = tri_height * t
                    points.append((center + side * x_offset, y))
                return points

            # Render on a larger transparent surface so the curved sides and
            # their surrounding fade stay smooth on every screen size.
            glow_padding = max(5, int(round(height * 0.007)))
            surface_width = triangle_half_width * 2 + glow_padding * 2 + 8
            surface_height = triangle_height + 4
            marker_surface = pygame.Surface(
                (surface_width, surface_height), pygame.SRCALPHA
            )
            marker_center = surface_width // 2

            # ------------------------------------------------
            # POINTER ITSELF — FADED ALONG BOTH LEGS
            # ------------------------------------------------
            # Render the pointer at high resolution first.  This removes the
            # pixelated look while keeping the pointer very thin.
            aa_scale = 4
            hi_width = surface_width * aa_scale
            hi_height = surface_height * aa_scale
            hi_center = marker_center * aa_scale
            hi_half_width = triangle_half_width * aa_scale
            hi_triangle_height = triangle_height * aa_scale

            pointer_surface = pygame.Surface(
                (hi_width, hi_height), pygame.SRCALPHA
            )

            # Build the pointer directly with a per-pixel alpha gradient.
            # The fade is calculated against the CURRENT width of the
            # triangle at every height, so it follows BOTH sloping legs.
            # Center = 80% opacity, both legs fade smoothly to transparent.
            for y in range(hi_triangle_height + 1):
                t = y / max(1.0, float(hi_triangle_height))

                inward = (1.0 - t) ** 1.55
                curve = 0.18 * math.sin(math.pi * t) * (1.0 - t)
                local_half_width = hi_half_width * max(
                    0.0, inward - curve
                )

                if local_half_width <= 0.5:
                    continue

                left_x = int(round(hi_center - local_half_width))
                right_x = int(round(hi_center + local_half_width))

                for x in range(left_x, right_x + 1):
                    distance = abs(x - hi_center)
                    normalized = distance / max(1.0, local_half_width)

                    # Strongest in the middle, smoothly disappearing at
                    # BOTH legs.  This is what makes the fade travel along
                    # the entire legs instead of appearing only at the tip.
                    edge_fade = max(0.0, 1.0 - normalized ** 2.4)
                    alpha = int(round(255.0 * 0.55 * edge_fade))

                    if alpha > 0:
                        pygame.draw.line(
                            pointer_surface,
                            (
                                SECONDARY_VIBE_COLOR[0],
                                SECONDARY_VIBE_COLOR[1],
                                SECONDARY_VIBE_COLOR[2],
                                alpha,
                            ),
                            (x, y),
                            (x, y),
                        )

            # Smooth the high-resolution pointer down to normal resolution.
            pointer_surface = pygame.transform.smoothscale(
                pointer_surface,
                (surface_width, surface_height),
            )

            screen.blit(
                pointer_surface,
                (triangle_center_x - marker_center, 0),
            )

            # ------------------------------------------------
            # IMAGE POSITION / SIZE CONTROLS
            # ------------------------------------------------
            if visualizer_image_editing:
                # ------------------------------------------------
                # CENTER ALIGNMENT GUIDES
                # ------------------------------------------------
                # Show a subtle magenta guide whenever the image is magnetically
                # aligned to the exact horizontal and/or vertical screen center.
                if visualizer_image_dragging and (visualizer_image_center_snap_x or visualizer_image_center_snap_y):
                    guide_surface = pygame.Surface((width, height), pygame.SRCALPHA)

                    if visualizer_image_center_snap_x:
                        center_x = int(round(width / 2.0))
                        pygame.draw.line(guide_surface, (255, 70, 180, 55), (center_x - 1, 0), (center_x - 1, height), 1)
                        pygame.draw.line(guide_surface, (255, 90, 190, 210), (center_x, 0), (center_x, height), 1)
                        pygame.draw.line(guide_surface, (255, 70, 180, 55), (center_x + 1, 0), (center_x + 1, height), 1)

                    if visualizer_image_center_snap_y:
                        center_y = int(round(height / 2.0))
                        pygame.draw.line(guide_surface, (255, 70, 180, 55), (0, center_y - 1), (width, center_y - 1), 1)
                        pygame.draw.line(guide_surface, (255, 90, 190, 210), (0, center_y), (width, center_y), 1)
                        pygame.draw.line(guide_surface, (255, 70, 180, 55), (0, center_y + 1), (width, center_y + 1), 1)

                    screen.blit(guide_surface, (0, 0))

                # Keep the editor directly under the top button row, with the size slider centered.
                slider_track = pygame.Rect(
                    image_size_slider_left, image_size_slider_y - 2,
                    image_size_slider_width, 4
                )
                pygame.draw.rect(screen, (95, 95, 115), slider_track, border_radius=2)
                image_size_max = get_visualizer_image_max_size()
                slider_normalized = max(0.0, min(1.0, (visualizer_image_size - 0.10) / max(0.001, image_size_max - 0.10)))
                knob_x = int(round(image_size_slider_left + slider_normalized * image_size_slider_width))
                pygame.draw.circle(screen, (235, 235, 245), (knob_x, image_size_slider_y), 7)
                pygame.draw.circle(screen, (125, 125, 150), (knob_x, image_size_slider_y), 7, 1)

                # Round Save and Cancel controls beside the slider.
                image_editor_mouse_position = pygame.mouse.get_pos()
                save_hover = image_save_button_rect.collidepoint(image_editor_mouse_position)
                cancel_hover = image_cancel_button_rect.collidepoint(image_editor_mouse_position)
                pygame.draw.circle(
                    screen,
                    (75, 105, 85) if save_hover else (45, 65, 55),
                    image_save_button_rect.center,
                    image_save_button_rect.width // 2,
                )
                pygame.draw.circle(
                    screen,
                    (150, 175, 155) if save_hover else (105, 125, 110),
                    image_save_button_rect.center,
                    image_save_button_rect.width // 2,
                    1,
                )
                check_font = pygame.font.SysFont("Segoe UI Symbol", 18)
                check_text = check_font.render("✓", True, (255, 255, 255))
                screen.blit(check_text, check_text.get_rect(center=image_save_button_rect.center))

                pygame.draw.circle(
                    screen,
                    (80, 65, 65) if cancel_hover else (50, 45, 50),
                    image_cancel_button_rect.center,
                    image_cancel_button_rect.width // 2,
                )
                pygame.draw.circle(
                    screen,
                    (170, 145, 150) if cancel_hover else (120, 105, 110),
                    image_cancel_button_rect.center,
                    image_cancel_button_rect.width // 2,
                    1,
                )
                cancel_font = pygame.font.SysFont("Segoe UI Symbol", 17)
                cancel_text = cancel_font.render("×", True, (255, 255, 255))
                screen.blit(cancel_text, cancel_text.get_rect(center=image_cancel_button_rect.center))

                # Draw the rounded-corners button. It cycles through Off / Soft / Medium / Strong.
                corner_hover = image_corner_button_rect.collidepoint(image_editor_mouse_position)
                corner_fill = (65, 65, 95) if corner_hover else (35, 35, 55)
                corner_border = (170, 170, 205) if corner_hover else (110, 110, 135)
                pygame.draw.circle(screen, corner_fill, image_corner_button_rect.center, image_corner_button_rect.width // 2)
                pygame.draw.circle(screen, corner_border, image_corner_button_rect.center, image_corner_button_rect.width // 2, 1)
                # Render a tiny rounded-square icon at high resolution so it stays sharp.
                icon_scale = 5
                icon_surface = pygame.Surface((24 * icon_scale, 24 * icon_scale), pygame.SRCALPHA)
                icon_rect = pygame.Rect(4 * icon_scale, 4 * icon_scale, 16 * icon_scale, 16 * icon_scale)
                icon_radius = int(max(2, (visualizer_image_corner_roundness * 16.0)) * icon_scale)
                pygame.draw.rect(icon_surface, (245, 245, 250, 255), icon_rect, width=2 * icon_scale, border_radius=icon_radius)
                corner_icon = pygame.transform.smoothscale(icon_surface, (24, 24))
                screen.blit(corner_icon, corner_icon.get_rect(center=image_corner_button_rect.center))

                # Draw the bottom-fade button. The current LEVEL NUMBER is shown
                # directly inside the button so it is easy to see where you are
                # without having to cycle all the way back to the original level.
                fade_hover = image_fade_button_rect.collidepoint(image_editor_mouse_position)
                fade_fill = (65, 65, 95) if fade_hover else (35, 35, 55)
                fade_border = (170, 170, 205) if fade_hover else (110, 110, 135)
                pygame.draw.circle(screen, fade_fill, image_fade_button_rect.center, image_fade_button_rect.width // 2)
                pygame.draw.circle(screen, fade_border, image_fade_button_rect.center, image_fade_button_rect.width // 2, 1)

                # Keep the number tied exactly to the same levels used by the click handler.
                fade_levels = (0.0, 0.25, 0.45, 0.65, 0.90, 0.98)
                fade_level_index = min(
                    range(len(fade_levels)),
                    key=lambda index: abs(fade_levels[index] - visualizer_image_bottom_fade),
                )

                # Keep the fade-preview illustration STATIC.
                # The small level number is simply drawn on top of it.
                # Nothing in this icon is animated.
                preview_scale = 4
                preview_size = 22
                preview_surface = pygame.Surface(
                    (preview_size * preview_scale, preview_size * preview_scale),
                    pygame.SRCALPHA,
                )
                preview_width = preview_size * preview_scale
                preview_height = preview_size * preview_scale

                # Draw the SAME static fade-preview rectangle, but make its
                # darkness reflect the currently selected fade level.
                # The preview is never animated; only its appearance changes
                # when the button is clicked.
                selected_fade_strength = float(fade_levels[fade_level_index])
                for preview_y in range(preview_height):
                    ratio = preview_y / max(1, preview_height - 1)
                    fade_position = max(0.0, (ratio - 0.15) / 0.85)
                    fade_position = fade_position * fade_position * (3.0 - 2.0 * fade_position)

                    # Keep the rectangle visible at every level, while making
                    # the lower portion progressively darker as the level rises.
                    base_alpha = 220
                    black_alpha = int(round(255.0 * selected_fade_strength * fade_position))
                    visible_alpha = max(8, base_alpha - int(round(base_alpha * (black_alpha / 255.0))))

                    pygame.draw.line(
                        preview_surface,
                        (245, 245, 250, visible_alpha),
                        (3 * preview_scale, preview_y),
                        (19 * preview_scale, preview_y),
                        1,
                    )

                preview_icon = pygame.transform.smoothscale(
                    preview_surface,
                    (preview_size, preview_size),
                )
                screen.blit(
                    preview_icon,
                    preview_icon.get_rect(center=image_fade_button_rect.center),
                )

                fade_level_font = pygame.font.SysFont("Segoe UI", 9, bold=True)
                fade_level_text = fade_level_font.render(
                    str(fade_level_index),
                    True,
                    (255, 255, 255),
                )
                screen.blit(
                    fade_level_text,
                    fade_level_text.get_rect(center=image_fade_button_rect.center),
                )

            # ------------------------------------------------
            # ------------------------------------------------
            # LYRICS DISPLAY
            # ------------------------------------------------
            # Match lyrics.py's standalone player for the actual lyric rendering:
            # same synchronized data, transliteration, 34px Unicode font,
            # line wrapping, and genuine word-by-word karaoke highlighting.
            # No panel/background is drawn behind the lyrics.
            if lyrics_visible:
                with lyrics_state_lock:
                    lyrics_loading = bool(lyrics_state["loading"])
                    lyrics_ready = bool(lyrics_state["ready"])
                    lyrics_prepared = lyrics_state["prepared"]

                if lyrics_ready and lyrics_prepared and lyrics_prepared.get("times"):
                    lyric_index = lyrics_engine.get_current_line_index(
                        lyrics_prepared,
                        current_time,
                    )

                    if lyric_index >= 0:
                        has_word_sync = bool(lyrics_prepared.get("has_word_sync"))

                        if has_word_sync and lyric_index < len(lyrics_prepared.get("words", [])):
                            words = lyrics_prepared["words"][lyric_index]
                            word_index = lyrics_engine.get_current_word_index(
                                lyrics_prepared,
                                current_time,
                                lyric_index,
                            )

                            pieces = []
                            for word_number, (_, raw_word) in enumerate(words):
                                word = lyrics_engine.transliterate_lyrics_line(raw_word)
                                if word_number == word_index:
                                    text_color = (255, 255, 255)
                                elif word_number < word_index:
                                    text_color = (210, 210, 210)
                                else:
                                    text_color = (90, 90, 90)
                                pieces.append((word, text_color))

                            total_width = sum(
                                lyrics_font.size(text_value)[0]
                                for text_value, _ in pieces
                            )
                            x = (width - total_width) / 2.0
                            y = (height - lyrics_font.get_height()) / 2.0

                            for text_value, text_color in pieces:
                                lyric_surface = lyrics_font.render(
                                    text_value,
                                    True,
                                    text_color,
                                )
                                screen.blit(
                                    lyric_surface,
                                    (int(round(x)), int(round(y))),
                                )
                                x += lyric_surface.get_width()
                        else:
                            current_lyric = lyrics_engine.get_current_line(
                                lyrics_prepared,
                                current_time,
                            )
                            display_text = lyrics_engine.transliterate_lyrics_line(
                                current_lyric or ""
                            )
                            display_lines = lyrics_engine._wrap_lyric_text(
                                lyrics_font,
                                display_text or "",
                                min(820, max(200, width - 160)),
                            )
                            center_y = height / 2.0
                            start_y = center_y - ((len(display_lines) - 1) * 20)

                            for line_number, line in enumerate(display_lines):
                                lyric_surface = lyrics_font.render(
                                    line,
                                    True,
                                    (255, 255, 255),
                                )
                                screen.blit(
                                    lyric_surface,
                                    lyric_surface.get_rect(
                                        center=(
                                            width // 2,
                                            int(round(start_y + line_number * 40)),
                                        ),
                                    ),
                                )
                elif lyrics_loading:
                    # Stay visually clean while the one-time lyrics lookup is pending.
                    pass

            # FROSTED GLASS BACKDROP FOR THE MAIN-SCREEN BUTTONS
            # ------------------------------------------------
            # Capture the already-rendered image/wave/progress area and blur it once.
            # Every top button then uses this same backdrop, keeping the UI lightweight.
            glass_strip_height = min(70, height)
            glass_strip_rect = pygame.Rect(0, 0, width, glass_strip_height)
            glass_source = screen.subsurface(glass_strip_rect).copy()
            blur_width = max(1, width // 5)
            blur_height = max(1, glass_strip_height // 5)
            glass_blurred = pygame.transform.smoothscale(
                pygame.transform.smoothscale(glass_source, (blur_width, blur_height)),
                (width, glass_strip_height),
            )

            # ------------------------------------------------
            # HOME BUTTON
            # ------------------------------------------------
            home_button_rect = pygame.Rect(5, 12, 40, 30)  # Create the small top-left Home button

            mouse_position = pygame.mouse.get_pos()  # Read the current mouse position for button hover feedback
            mouse_pressed = pygame.mouse.get_pressed()[0]  # Check whether the left mouse button is being held down

            # HOME BUTTON
            # Clickable area only — NO background shape, halo, circle, or glow.
            # The original Home glyph itself is the entire button.
            home_hover = home_button_rect.collidepoint(mouse_position)

            home_button_font = pygame.font.SysFont("Segoe UI Symbol", 36)
            home_text = home_button_font.render("⌂", True, (255, 255, 255)).convert_alpha()
            icon_rect = home_text.get_rect(center=home_button_rect.center)

            # Smoothly hide Home while the song is playing. Mouse movement over
            # the visualizer reveals it again, then it fades back out after a
            # short period of mouse inactivity. Nothing else on the UI is affected.
            now = time.perf_counter()
            home_should_show = (
                not playing
                or user_paused
                or now < home_reveal_until
                or home_hover
            )

            home_target = 1.0 if home_should_show else 0.0
            home_visibility += (home_target - home_visibility) * 0.16

            if home_visibility > 0.01:
                # Translucent icon only. The image/background remains visible through it.
                home_text.set_alpha(int(round(190 * home_visibility)))
                screen.blit(home_text, icon_rect)

            # ------------------------------------------------
            # RIGHT-SIDE BUTTON ROW
            # ------------------------------------------------
            top_button_y = 12
            top_button_gap = 8
            lyrics_button_rect = pygame.Rect(width - 33, 18, 18, 18)  # Keep Lyrics at the far right
            calm_button_rect = pygame.Rect(lyrics_button_rect.left - top_button_gap - 18, 18, 18, 18)
            status_button_rect = pygame.Rect(calm_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            image_button_rect = pygame.Rect(status_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            song_button_rect = pygame.Rect(image_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            color_button_rect = pygame.Rect(song_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)
            menu_button_rect = pygame.Rect(color_button_rect.left - top_button_gap - 40, top_button_y, 40, 30)  # Create the small top-right menu button

            mouse_pressed = pygame.mouse.get_pressed()[0]  # Check whether the left mouse button is being held down

            if menu_button_rect.collidepoint(mouse_position):  # Check whether the mouse is over the menu button
                menu_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and press
                menu_border_color = (170, 170, 205)  # Highlight the menu button border while hovered
            else:
                menu_button_color = (25, 25, 40)  # Keep the normal menu button background
                menu_border_color = (130, 130, 150)  # Keep the normal menu button border

            draw_glass_button(screen, menu_button_rect, glass_blurred, hover=menu_button_rect.collidepoint(mouse_position))  # Draw the smooth menu pill

            # Draw three evenly spaced menu lines, centered precisely inside the button.
            menu_center_x = menu_button_rect.centerx
            menu_center_y = menu_button_rect.centery
            menu_line_half_width = 8  # Keep the lines slightly shorter.
            menu_line_thickness = 1  # Keep the lines slim and subtle.
            menu_line_spacing = 4  # Keep the three lines compact.
            for line_y in (
                menu_center_y - menu_line_spacing,
                menu_center_y,
                menu_center_y + menu_line_spacing,
            ):
                pygame.draw.line(
                    screen,
                    (255, 255, 255),
                    (menu_center_x - menu_line_half_width, line_y),
                    (menu_center_x + menu_line_half_width, line_y),
                    menu_line_thickness,
                )

            # color_button_rect is defined in the right-side horizontal button row above.
            if color_button_rect.collidepoint(mouse_position):  # Check whether the mouse is over the color button
                color_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and press
                color_border_color = (170, 170, 205)  # Highlight the color button border while hovered
            else:
                color_button_color = (25, 25, 40)  # Keep the normal color button background
                color_border_color = (130, 130, 150)  # Keep the normal color button border
            draw_glass_button(screen, color_button_rect, glass_blurred, hover=color_button_rect.collidepoint(mouse_position))  # Draw the smooth color pill
            color_text = small_font.render("C", True, (255, 255, 255))  # Create the custom-color icon
            screen.blit(color_text, (color_button_rect.centerx - color_text.get_width() // 2, color_button_rect.centery - color_text.get_height() // 2))  # Draw the custom-color icon

            # song_button_rect is defined in the right-side horizontal button row above.
            if song_button_rect.collidepoint(mouse_position):  # Check whether the mouse is over the song button
                song_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and press
                song_border_color = (170, 170, 205)  # Highlight the song button border while hovered
            else:
                song_button_color = (25, 25, 40)  # Keep the normal song button background
                song_border_color = (130, 130, 150)  # Keep the normal song button border
            draw_glass_button(screen, song_button_rect, glass_blurred, hover=song_button_rect.collidepoint(mouse_position))  # Draw the smooth song pill
            song_text = font.render("♪", True, (255, 255, 255))  # Create the music-note icon
            screen.blit(song_text, (song_button_rect.centerx - song_text.get_width() // 2, song_button_rect.centery - song_text.get_height() // 2 - 1))  # Draw the music-note icon

            # image_button_rect is the image selector between Info and Calm.
            if image_button_rect.collidepoint(mouse_position):
                image_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)
                image_border_color = (170, 170, 205)
            else:
                image_button_color = (25, 25, 40)
                image_border_color = (130, 130, 150)
            draw_glass_button(screen, image_button_rect, glass_blurred, hover=image_button_rect.collidepoint(mouse_position))
            # Draw a real image/photo icon instead of using a font glyph.
            # The glyph rendered as a rectangle on systems where "▣" is unsupported.
            icon_rect = pygame.Rect(
                image_button_rect.centerx - 9,
                image_button_rect.centery - 7,
                18,
                14,
            )
            pygame.draw.rect(
                screen,
                (245, 245, 250),
                icon_rect,
                1,
                border_radius=2,
            )
            # Small sun/circle in the upper-right of the picture.
            pygame.draw.circle(
                screen,
                (245, 245, 250),
                (icon_rect.right - 5, icon_rect.top + 4),
                2,
            )
            # Two smooth mountain shapes inside the picture.
            pygame.draw.lines(
                screen,
                (245, 245, 250),
                False,
                [
                    (icon_rect.left + 2, icon_rect.bottom - 3),
                    (icon_rect.left + 7, icon_rect.top + 7),
                    (icon_rect.left + 10, icon_rect.top + 10),
                    (icon_rect.left + 13, icon_rect.top + 6),
                    (icon_rect.right - 2, icon_rect.bottom - 3),
                ],
                1,
            )

            # status_button_rect is defined in the right-side horizontal button row above.
            if status_button_rect.collidepoint(mouse_position) or status_open:
                status_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)
                status_border_color = (170, 170, 205)
            else:
                status_button_color = (25, 25, 40)
                status_border_color = (130, 130, 150)
            draw_glass_button(screen, status_button_rect, glass_blurred, hover=status_button_rect.collidepoint(mouse_position), active=status_open)
            status_text = font.render("i", True, (255, 255, 255))
            screen.blit(status_text, (status_button_rect.centerx - status_text.get_width() // 2, status_button_rect.centery - status_text.get_height() // 2 - 1))

            # Draw the Lyrics checkbox at the far right of the button row.
            # Empty means lyrics are hidden; filled means synchronized lyrics are visible.
            lyrics_hover = lyrics_button_rect.collidepoint(mouse_position)
            draw_glass_button(
                screen,
                lyrics_button_rect,
                glass_blurred,
                hover=lyrics_hover,
                active=lyrics_visible,
                square=True,
            )
            if lyrics_visible:
                lyrics_check_font = pygame.font.SysFont("Segoe UI Symbol", 15)
                lyrics_check_text = lyrics_check_font.render("✓", True, (255, 255, 255))
                screen.blit(
                    lyrics_check_text,
                    lyrics_check_text.get_rect(center=lyrics_button_rect.center),
                )

            # Draw the optional Calm mode checkbox.
            # Empty means normal wave response; filled means the extra smoothing is active.
            # calm_button_rect is defined in the right-side horizontal button row above.
            calm_hover = calm_button_rect.collidepoint(mouse_position)
            if calm_mode:
                draw_glass_button(
                    screen,
                    calm_button_rect,
                    glass_blurred,
                    hover=calm_hover,
                    active=True,
                    square=True,
                )
                check_font = pygame.font.SysFont("Segoe UI Symbol", 15)
                check_text = check_font.render("✓", True, (255, 255, 255))
                screen.blit(check_text, check_text.get_rect(center=calm_button_rect.center))
            else:
                draw_glass_button(
                    screen,
                    calm_button_rect,
                    glass_blurred,
                    hover=calm_hover,
                    square=True,
                )

            # ------------------------------------------------
            # CALM MODE NOTIFICATION
            # ------------------------------------------------
            # Keep the message below the button with a clear gap so it can never
            # overlap the button. Its right edge is aligned exactly with the
            # right edge of the Calm button.
            if calm_mode_notice_message:
                now = time.perf_counter()
                if now < calm_mode_notice_until:
                    remaining = calm_mode_notice_until - now
                    elapsed = now - calm_mode_notice_started
                    fade_in = min(1.0, elapsed / 0.12)
                    fade_out = min(1.0, remaining / 0.25)
                    notice_alpha = int(230 * min(fade_in, fade_out))
                    if notice_alpha > 0:
                        notice_font = pygame.font.SysFont("Arial", 16)
                        # Render the notice at 2x resolution and downsample it so the larger
                        # font stays smooth rather than looking pixelated.
                        notice_scale = 2
                        hi_notice_font = pygame.font.SysFont("Arial", 16 * notice_scale)
                        hi_notice_surface = hi_notice_font.render(
                            calm_mode_notice_message,
                            True,
                            (235, 235, 245),
                        ).convert_alpha()
                        notice_surface = pygame.transform.smoothscale(
                            hi_notice_surface,
                            (max(1, hi_notice_surface.get_width() // notice_scale),
                             max(1, hi_notice_surface.get_height() // notice_scale)),
                        )
                        notice_surface.set_alpha(notice_alpha)
                        notice_rect = notice_surface.get_rect(
                            top=calm_button_rect.bottom + 8,
                            right=calm_button_rect.right,
                        )
                        screen.blit(notice_surface, notice_rect)
                else:
                    calm_mode_notice_message = ""

            # Cache the expensive frosted-panel blur. Rebuilding and smoothscaling a
            # 450x/600x panel every visualizer frame is much heavier than the wave
            # drawing itself. Refresh the glass backdrop at ~12 FPS so the panel still
            # follows the moving visualizer while leaving the wave loop at full speed.
            frosted_panel_cache = getattr(run_the_one, "_frosted_panel_cache", {})
            frosted_panel_cache_time = getattr(run_the_one, "_frosted_panel_cache_time", {})

            if status_open:
                status_panel_width = 450
                status_panel_x = max(20, calm_button_rect.right - status_panel_width)
                status_settings_y = get_status_settings_y()
                status_panel_height = status_settings_y + (365 if status_details_open else 43)
                status_panel_rect = pygame.Rect(status_panel_x, 50, status_panel_width, status_panel_height)
                draw_frosted_panel(screen, status_panel_rect, dark_alpha=142, border_alpha=120)
                title_surface = font.render("Song & Status", True, (255, 255, 255))
                screen.blit(title_surface, (status_panel_x + 18, 66))

                def draw_status_heading(text, y):
                    surface = small_font.render(text, True, (170, 175, 195))
                    screen.blit(surface, (status_panel_x + 18, y))

                def draw_status_row(label, value, y, changed=None):
                    label_surface = small_font.render(label, True, (225, 225, 235))
                    screen.blit(label_surface, (status_panel_x + 18, y))
                    value_color = (255, 175, 110) if changed is True else ((165, 190, 170) if changed is False else (185, 188, 205))
                    value_surface = small_font.render(str(value), True, value_color)
                    screen.blit(value_surface, (status_panel_x + 185, y))
                    return y + 26

                def draw_wrapped_status_row(label, value, y, max_width=235, changed=None):
                    label_surface = small_font.render(label, True, (225, 225, 235))
                    screen.blit(label_surface, (status_panel_x + 18, y))
                    value_color = (255, 175, 110) if changed is True else ((165, 190, 170) if changed is False else (185, 188, 205))
                    lines = []
                    current_line = ""

                    # Pixel-based wrapping handles normal titles and long words.
                    for word in str(value).split():
                        candidate = word if not current_line else current_line + " " + word
                        if small_font.size(candidate)[0] <= max_width:
                            current_line = candidate
                            continue

                        if current_line:
                            lines.append(current_line)
                            current_line = ""

                        piece = ""
                        for char in word:
                            test_piece = piece + char
                            if piece and small_font.size(test_piece)[0] > max_width:
                                lines.append(piece)
                                piece = char
                            else:
                                piece = test_piece
                        current_line = piece

                    if current_line or not lines:
                        lines.append(current_line)

                    for index, line in enumerate(lines):
                        value_surface = small_font.render(line, True, value_color)
                        screen.blit(value_surface, (status_panel_x + 185, y + index * 22))
                    return y + max(26, len(lines) * 22)

                draw_status_heading("SONG", 116)
                song_name_y = draw_wrapped_status_row("Name", song_info.get("title", "Unknown title"), 141)
                singer_y = draw_wrapped_status_row("Singer", song_info.get("artist", "Unknown artist"), song_name_y)
                length_y = draw_status_row("Length", format_song_length(song_info.get("duration", 0.0)), singer_y)
                identifier_y = draw_status_row("Identifier", song_info.get("identifier", "Local file"), length_y)

                settings_status = current_settings_status()
                status_settings_y = identifier_y
                draw_status_row("Status settings", "Changed" if settings_status["overall"] else "Unchanged", status_settings_y, settings_status["overall"])

                status_drop_rect = pygame.Rect(status_panel_x + 290, status_settings_y - 5, 30, 30)
                arrow_font = pygame.font.SysFont("Arial", 11)
                arrow_text = arrow_font.render("▲" if status_details_open else "▼", True, (235, 235, 245))
                screen.blit(arrow_text, (status_drop_rect.centerx - arrow_text.get_width() // 2, status_drop_rect.centery - arrow_text.get_height() // 2))

                if status_details_open:
                    draw_status_heading("CHANGES", status_settings_y + 58)
                    draw_status_row("Wave color", "Changed" if settings_status["wave"] else "Unchanged", status_settings_y + 83, settings_status["wave"])
                    draw_status_row("Bass color", "Changed" if settings_status["bass"] else "Unchanged", status_settings_y + 109, settings_status["bass"])
                    draw_status_row("Bass opacity", "Changed" if settings_status["bass_opacity"] else "Unchanged", status_settings_y + 135, settings_status["bass_opacity"])
                    draw_status_row("Bar gap", "Changed" if settings_status["gap"] else "Unchanged", status_settings_y + 161, settings_status["gap"])
                    draw_status_row("Curvature", "Changed" if settings_status["curvature"] else "Unchanged", status_settings_y + 187, settings_status["curvature"])
                    draw_status_row("Overall opacity", "Changed" if settings_status["overall_opacity"] else "Unchanged", status_settings_y + 213, settings_status["overall_opacity"])
                    draw_status_row("Center width", "Changed" if settings_status["center_width"] else "Unchanged", status_settings_y + 239, settings_status["center_width"])
                    draw_status_row("Center opacity", "Changed" if settings_status["center_opacity"] else "Unchanged", status_settings_y + 265, settings_status["center_opacity"])
                    draw_status_row("Calmness", "Changed" if settings_status["calmness"] else "Unchanged", status_settings_y + 291, settings_status["calmness"])
                    draw_status_row("Song settings", "Saved" if settings_status["saved_current"] else "Unsaved changes", status_settings_y + 317, not settings_status["saved_current"])
                    note_surface = small_font.render("Bar settings are global, not song-specific.", True, (130, 135, 155))
                    screen.blit(note_surface, (status_panel_x + 18, status_settings_y + 343))

            def draw_frosted_panel(surface, rect, dark_alpha=132, border_alpha=115):
                # The blur is intentionally cached for a short interval. The old code
                # performed TWO smoothscale operations over the whole panel on EVERY
                # frame while a menu was open, which competed directly with the audio
                # reactive wave rendering. A ~12 FPS glass refresh is visually smooth
                # enough for a frosted panel but removes that per-frame CPU spike.
                cache_key = (rect.x, rect.y, rect.width, rect.height, dark_alpha, border_alpha)
                now_panel = time.perf_counter()
                cached_panel = frosted_panel_cache.get(cache_key)
                cached_at = frosted_panel_cache_time.get(cache_key, 0.0)

                if cached_panel is None or (now_panel - cached_at) >= (1.0 / 12.0):
                    panel = pygame.Surface(rect.size, pygame.SRCALPHA)
                    source = surface.subsurface(rect).copy()
                    blur_w = max(1, rect.width // 8)
                    blur_h = max(1, rect.height // 8)
                    blurred = pygame.transform.smoothscale(source, (blur_w, blur_h))
                    blurred = pygame.transform.smoothscale(blurred, rect.size)
                    panel.blit(blurred, (0, 0))
                    pygame.draw.rect(
                        panel,
                        (8, 8, 18, dark_alpha),
                        panel.get_rect(),
                        border_radius=10,
                    )
                    # Supersampled panel edge for a clean, non-pixelated glass border.
                    draw_smooth_rounded_border(
                        panel, panel.get_rect(), (145, 145, 170, border_alpha),
                        width=2, radius=10, scale=4,
                    )
                    cached_panel = panel.convert_alpha()
                    frosted_panel_cache[cache_key] = cached_panel
                    frosted_panel_cache_time[cache_key] = now_panel
                    setattr(run_the_one, "_frosted_panel_cache", frosted_panel_cache)
                    setattr(run_the_one, "_frosted_panel_cache_time", frosted_panel_cache_time)

                surface.blit(cached_panel, rect.topleft)

            def draw_panel_glass_button(surface, rect, backdrop, panel_origin, hover=False, pressed=False, destructive=False):
                # These menu buttons do not actually need to be rebuilt every frame.
                # Their glass shape is independent of the moving visualizer because the
                # frosted panel behind them is already doing the background work.
                # Building an 8x surface + smoothscale for every button every frame was
                # one of the main causes of the visualizer becoming sluggish when the
                # menu opened. Keep the high-resolution AA, but build each visual state
                # only once and reuse it.
                cache = getattr(run_the_one, "_menu_glass_button_cache", {})
                cache_key = (rect.width, rect.height, bool(hover), bool(pressed), bool(destructive))
                cached = cache.get(cache_key)

                if cached is None:
                    scale = 4
                    hi_size = (max(1, rect.width * scale), max(1, rect.height * scale))
                    hi = pygame.Surface(hi_size, pygame.SRCALPHA)

                    if destructive:
                        tint = (85, 45, 58, 145 if not hover else 175)
                        border = (190, 125, 145, 170 if hover else 115)
                    else:
                        tint = (25, 25, 40, 145 if not hover else 170)
                        border = (150, 150, 175, 170 if hover else 115)

                    radius = max(1, (rect.height // 2) * scale)
                    hi_rect = hi.get_rect()
                    pygame.draw.rect(hi, tint, hi_rect, border_radius=radius)
                    pygame.draw.rect(hi, border, hi_rect, width=scale, border_radius=radius)
                    cached = pygame.transform.smoothscale(hi, rect.size).convert_alpha()
                    cache[cache_key] = cached
                    setattr(run_the_one, "_menu_glass_button_cache", cache)

                surface.blit(cached, rect.topleft)

            if controls_open:
                panel_width = 600  # Wide enough for the controller area and right-side button stack
                panel_x = max(20, calm_button_rect.right - panel_width)  # Align the panel right edge directly under Calm
                panel_rect = pygame.Rect(panel_x, 50, panel_width, 550)  # Fit all eight controllers and all five right-side buttons
                draw_frosted_panel(screen, panel_rect, dark_alpha=142, border_alpha=120)  # Darker frosted glass panel
                panel_button_backdrop = screen.subsurface(panel_rect).copy()  # Clean panel surface used by its glass buttons

                title_surface = font.render("Bar Control", True, (255, 255, 255))  # Create the panel title
                screen.blit(title_surface, (panel_x + 18, 66))  # Draw the panel title inside the panel

                slider_data = [
                    ("Gap", "gap", bar_gap_setting, f"{int(bar_gap_setting)} px"),
                    ("Curvature", "curvature", curvature_setting, f"{round(curvature_setting * 100)}%"),
                    ("Overall height", "wave_height", wave_height_setting, f"{int(wave_height_setting)}/10"),
                    ("Overall opacity", "overall", overall_opacity_setting, f"{round(overall_opacity_setting * 100)}%"),
                    ("Center width", "center_width", center_width_setting, f"{round(center_width_setting * 100)}%"),
                    ("Center opacity", "center_opacity", center_opacity_setting, f"{round(center_opacity_setting * 100)}%"),
                    ("Bass opacity", "bass_opacity", bass_opacity_setting, f"{round(bass_opacity_setting * 100)}%"),
                    ("Calmness", "calmness", calmness_setting, f"{int(calmness_setting)}/10"),
                ]  # Prepare the eight adjustable values
                slider_y_positions = {"gap": 118, "curvature": 168, "wave_height": 218, "overall": 268, "center_width": 318, "center_opacity": 368, "bass_opacity": 418, "calmness": 468}  # Set compact slider positions
                slider_left = panel_x + 205  # Set the left end of each slider
                slider_right = panel_x + 425  # Set the right end of each slider

                for label, slider_name, value, value_text in slider_data:
                    slider_y = slider_y_positions[slider_name]  # Get this slider's vertical position
                    label_surface = small_font.render(label, True, (225, 225, 235))  # Create the slider label
                    screen.blit(label_surface, (panel_x + 18, slider_y - 9))  # Draw the slider label
                    value_surface = small_font.render(value_text, True, (170, 170, 185))  # Create the current value text
                    screen.blit(value_surface, (panel_x + 145, slider_y - 9))  # Draw the current value
                    pygame.draw.line(screen, (80, 80, 100), (slider_left, slider_y), (slider_right, slider_y), 4)  # Draw the slider track
                    if slider_name == "gap":
                        normalized_value = value / 10.0  # Convert the gap to a 0-to-1 slider position
                    elif slider_name == "bass_opacity":
                        normalized_value = value  # Position the knob directly from the user's 0%-100% bass opacity
                    elif slider_name == "wave_height":
                        normalized_value = (value - 1.0) / 9.0  # Map the 1-10 height scale onto the full slider track
                    elif slider_name == "calmness":
                        normalized_value = value / 10.0  # Map Calmness 0-10 onto the full slider track
                    else:
                        normalized_value = value  # The other sliders already use a direct 0-to-1 position
                    normalized_value = float(np.clip(normalized_value, 0.0, 1.0))  # Keep the knob inside the slider track
                    knob_x = int(round(slider_left + normalized_value * (slider_right - slider_left)))  # Calculate the knob position
                    pygame.draw.circle(screen, (225, 225, 235), (knob_x, slider_y), 7)  # Draw the draggable point

                button_x = panel_x + 450
                button_width = 132
                button_gap = 12
                button_y = 207  # Center the four-button stack on the midpoint of the eight controllers
                default_width = 92  # Leave room for the compact square Undo button beside Default
                undo_gap = 8
                undo_size = 34
                default_rect = pygame.Rect(button_x, button_y, default_width, 34)  # Create the factory Default button
                undo_rect = pygame.Rect(button_x + default_width + undo_gap, button_y, undo_size, undo_size)  # Create the compact Undo button
                mouse_position = pygame.mouse.get_pos()  # Read the current mouse position for button hover feedback
                mouse_pressed = pygame.mouse.get_pressed()[0]  # Check whether the left mouse button is currently held down
                if default_rect.collidepoint(mouse_position):  # Check whether the mouse is over the Default button
                    default_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and brighten further while clicking
                    default_border_color = (170, 170, 205)  # Highlight the button border while hovered
                else:
                    default_button_color = (35, 35, 55)  # Keep the normal button background when not hovered
                    default_border_color = (110, 110, 135)  # Keep the normal button border when not hovered
                draw_panel_glass_button(screen, default_rect, panel_button_backdrop, (panel_rect.x, panel_rect.y), hover=default_rect.collidepoint(mouse_position), pressed=mouse_pressed)  # Draw the smooth Default pill
                default_text = small_font.render("Default", True, (255, 255, 255))  # Create the Default label
                screen.blit(default_text, (default_rect.centerx - default_text.get_width() // 2, default_rect.centery - default_text.get_height() // 2))  # Draw the Default label

                # Draw the Undo button as a true circle, matching the rounded style of the other buttons.
                if undo_rect.collidepoint(mouse_position):
                    undo_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)
                    undo_border_color = (170, 170, 205)
                else:
                    undo_button_color = (35, 35, 55)
                    undo_border_color = (110, 110, 135)

                undo_cache = getattr(run_the_one, "_undo_button_cache", {})
                undo_key = (undo_rect.width, undo_rect.height, undo_rect.collidepoint(mouse_position), bool(mouse_pressed))
                smooth_undo = undo_cache.get(undo_key)
                if smooth_undo is None:
                    scale = 4
                    diameter = undo_rect.width * scale
                    hi_surface = pygame.Surface((diameter, diameter), pygame.SRCALPHA)
                    center = (diameter // 2, diameter // 2)
                    radius = diameter // 2 - 1 * scale
                    pygame.draw.circle(hi_surface, undo_button_color, center, radius)
                    pygame.draw.circle(hi_surface, undo_border_color, center, radius, 1 * scale)
                    smooth_undo = pygame.transform.smoothscale(hi_surface, undo_rect.size).convert_alpha()
                    undo_cache[undo_key] = smooth_undo
                    setattr(run_the_one, "_undo_button_cache", undo_cache)
                screen.blit(smooth_undo, undo_rect.topleft)

                # Draw a thin, compact undo arrow at high resolution so it stays crisp.
                icon_scale = 6
                icon_size = 32
                icon_surface = pygame.Surface(
                    (icon_size * icon_scale, icon_size * icon_scale),
                    pygame.SRCALPHA,
                )

                cx = icon_size * icon_scale // 2
                cy = icon_size * icon_scale // 2
                r = 10 * icon_scale
                line_width = 1 * icon_scale
                icon_color = (240, 240, 250)

                # Circular undo arc with a clean opening on the right.
                pygame.draw.arc(
                    icon_surface,
                    icon_color,
                    (cx - r, cy - r, 2 * r, 2 * r),
                    0.45,
                    5.55,
                    line_width,
                )

                # Small left-pointing arrow head.
                arrow_tip = (cx - r - 1 * icon_scale, cy - 2 * icon_scale)
                arrow_top = (cx - r + 6 * icon_scale, cy - 7 * icon_scale)
                arrow_bottom = (cx - r + 6 * icon_scale, cy + 3 * icon_scale)
                pygame.draw.line(icon_surface, icon_color, arrow_tip, arrow_top, line_width)
                pygame.draw.line(icon_surface, icon_color, arrow_tip, arrow_bottom, line_width)

                undo_icon = pygame.transform.smoothscale(
                    icon_surface,
                    (icon_size, icon_size),
                )
                undo_icon_rect = undo_icon.get_rect(center=undo_rect.center)
                undo_icon_rect.centery -= 2
                screen.blit(undo_icon, undo_icon_rect)

                save_default_rect = pygame.Rect(button_x, button_y + (34 + button_gap), button_width, 34)  # Create the Save as Default button
                if save_default_rect.collidepoint(mouse_position):  # Check whether the mouse is over the Save as Default button
                    save_default_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and brighten further while clicking
                    save_default_border_color = (170, 170, 205)  # Highlight the button border while hovered
                else:
                    save_default_button_color = (35, 35, 55)  # Keep the normal button background when not hovered
                    save_default_border_color = (110, 110, 135)  # Keep the normal button border when not hovered
                draw_panel_glass_button(screen, save_default_rect, panel_button_backdrop, (panel_rect.x, panel_rect.y), hover=save_default_rect.collidepoint(mouse_position), pressed=mouse_pressed)  # Draw the smooth Save as Default pill
                save_default_text = small_font.render("Save as Default", True, (255, 255, 255))  # Create the save button label
                screen.blit(save_default_text, (save_default_rect.centerx - save_default_text.get_width() // 2, save_default_rect.centery - save_default_text.get_height() // 2))  # Draw the save button label

                save_colors_rect = pygame.Rect(button_x, button_y + 2 * (34 + button_gap), button_width, 34)  # Create the song-specific Save Colors button
                if save_colors_rect.collidepoint(mouse_position):  # Check whether the mouse is over the Save Colors button
                    save_colors_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and press
                    save_colors_border_color = (170, 170, 205)  # Highlight the Save Colors border while hovered
                else:
                    save_colors_button_color = (35, 35, 55)  # Keep the normal Save Colors background
                    save_colors_border_color = (110, 110, 135)  # Keep the normal Save Colors border
                draw_panel_glass_button(screen, save_colors_rect, panel_button_backdrop, (panel_rect.x, panel_rect.y), hover=save_colors_rect.collidepoint(mouse_position), pressed=mouse_pressed)  # Draw the smooth Save Colors pill
                save_colors_text = small_font.render("Save Colors", True, (255, 255, 255))  # Create the Save Colors label
                screen.blit(save_colors_text, (save_colors_rect.centerx - save_colors_text.get_width() // 2, save_colors_rect.centery - save_colors_text.get_height() // 2))  # Draw the Save Colors label

                bass_default_rect = pygame.Rect(button_x, button_y + 3 * (34 + button_gap), button_width, 34)  # Create the Bass factory-default reset button
                if bass_default_rect.collidepoint(mouse_position):
                    bass_default_button_color = (65, 65, 95) if not mouse_pressed else (90, 90, 125)  # Brighten on hover and press
                    bass_default_border_color = (170, 170, 205)  # Highlight the reset button border while hovered
                else:
                    bass_default_button_color = (35, 35, 55)  # Keep the normal reset button background
                    bass_default_border_color = (110, 110, 135)  # Keep the normal reset button border
                draw_panel_glass_button(screen, bass_default_rect, panel_button_backdrop, (panel_rect.x, panel_rect.y), hover=bass_default_rect.collidepoint(mouse_position), pressed=mouse_pressed)  # Draw the Bass factory-default pill
                bass_default_text = small_font.render("Bass Default", True, (255, 255, 255))  # Create the Bass Default label
                screen.blit(bass_default_text, (bass_default_rect.centerx - bass_default_text.get_width() // 2, bass_default_rect.centery - bass_default_text.get_height() // 2))  # Draw the Bass Default label

                remove_image_rect = pygame.Rect(button_x, button_y + 4 * (34 + button_gap), button_width, 34)  # Create the permanent image removal button
                if remove_image_rect.collidepoint(mouse_position):
                    remove_image_button_color = (85, 45, 55) if not mouse_pressed else (115, 55, 65)
                    remove_image_border_color = (205, 125, 140)
                else:
                    remove_image_button_color = (45, 30, 38)
                    remove_image_border_color = (125, 85, 95)
                draw_panel_glass_button(screen, remove_image_rect, panel_button_backdrop, (panel_rect.x, panel_rect.y), hover=remove_image_rect.collidepoint(mouse_position), pressed=mouse_pressed, destructive=True)
                remove_image_text = small_font.render("Remove Image", True, (255, 235, 240))
                screen.blit(remove_image_text, (remove_image_rect.centerx - remove_image_text.get_width() // 2, remove_image_rect.centery - remove_image_text.get_height() // 2))

            # ------------------------------------------------
            # UPDATE SCREEN
            # ------------------------------------------------

            pygame.display.flip()  # Show the completed frame

            clock.tick(
                60
            )  # Keep the visualizer at up to 60 FPS

    except Exception as error:

        print(
            f"The One error: {error}"
        )  # Print the unexpected error

        show_error_message(
            "The One - Unexpected Error",
            f"Something went wrong:\n\n{error}"
        )  # Show unexpected errors instead of silently closing

    finally:

        bass_analysis_stop.set()  # Tell the independent bass analysis to stop

        if state is not None:

            state.stop_event.set()  # Tell background analysis to stop

        try:

            pygame.mixer.music.stop()  # Stop playback safely

        except Exception:

            pass  # Ignore shutdown errors

        try:

            pygame.mixer.quit()  # Shut down the mixer safely

        except Exception:

            pass  # Ignore shutdown errors

        if not new_song_requested:

            pygame.quit()  # Shut down Pygame only when the visualizer is really closing

        # When a new song was selected, keep the Pygame display alive so the next song
        # can take over the exact same window instead of opening a new one.

    return new_song_requested  # Return a newly selected song so the caller can load it


# ============================================================
# RUN DIRECTLY
# ============================================================

if __name__ == "__main__":

    next_song = None  # Hold a song selected from inside the visualizer
    while True:
        next_song = run_the_one(source_path=next_song)  # Start the visualizer and load a requested replacement song
        if not next_song:
            break  # Exit when the visualizer closes without selecting another song