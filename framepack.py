#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""FramePack - 動画フレーム抽出ツール（Linux / GUI）

ローカルの動画ファイルから指定した数秒間を切り取り、フレーム画像（JPEG）と
メタデータ（manifest.json）の2つを含むZIPファイル（解析データファイル）を生成する。
完成したZIPをAIチャット（Vibe）に渡すことで、動画内のデザイン・構図・配色などの
解析を依頼できる。

依存パッケージ: flask, opencv-python（それぞれの依存としてインストールされる numpy を含む）
その他は Python 標準ライブラリのみ。動画データは外部ネットワークに一切送信しない。
"""

import base64
import json
import logging
import math
import os
import re
import shutil
import socket
import tempfile
import threading
import time
import webbrowser
import zipfile
from datetime import datetime

import cv2
import numpy as np
from flask import Flask, Response, jsonify, request, send_file

HOST = "127.0.0.1"
PORT = 8765
OUTPUT_DIR_NAME = "framepack_output"
JPEG_QUALITY = 92
CONTACT_SHEET_JPEG_QUALITY = 90
CONTACT_SHEET_CELL_WIDTH = 480
CONTACT_SHEET_COLS = 4
CONTACT_SHEET_MAX_FRAMES = 20
MAX_TOTAL_FRAMES = 60
POLL_INTERVAL_MS = 500

WHITE_JPEG_B64 = (
    "/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAMCAgMCAgMDAwMEAwMEBQgFBQQEBQoHBwYIDAoMDAsK"
    "CwsNDhIQDQ4RDgsLEBYQERMUFRUVDA8XGBYUGBIUFRT/2wBDAQMEBAUEBQkFBQkUDQsNFBQUFBQU"
    "FBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQU"
    "FBT/wAARCAAEAAQDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QA"
    "tRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkK"
    "FhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJ"
    "ipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx"
    "8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcF"
    "BAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygp"
    "KjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJma"
    "oqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oA"
    "DAMBAAIRAxEAPwD9U6KKKAP/2Q=="
)

INDEX_HTML = """<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>FramePack — 動画フレーム抽出ツール</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: "Hiragino Sans", "Yu Gothic", "Meiryo", "Noto Sans JP", sans-serif; background: #f0f2f5; color: #333; line-height: 1.6; }
.container { max-width: 920px; margin: 0 auto; padding: 24px 16px 64px; }
h1 { font-size: 28px; margin-bottom: 4px; }
.subtitle { color: #666; margin-bottom: 24px; font-size: 14px; }
.step { background: #fff; border-radius: 12px; padding: 20px 24px; margin-bottom: 20px; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }
.step h2 { font-size: 17px; margin-bottom: 14px; display: flex; align-items: center; gap: 8px; font-weight: 600; }
.step-num { display: inline-flex; align-items: center; justify-content: center; width: 26px; height: 26px; border-radius: 50%; background: #4a6cf7; color: #fff; font-size: 14px; flex-shrink: 0; }
.dropzone { border: 2px dashed #b0b8c8; border-radius: 10px; padding: 36px 16px; text-align: center; color: #667; cursor: pointer; transition: border-color .2s, background .2s; font-size: 15px; }
.dropzone:hover, .dropzone.dragover { border-color: #4a6cf7; background: #f4f7ff; }
.video-info { margin-top: 16px; }
.video-info video { width: 100%; max-height: 360px; border-radius: 8px; background: #000; display: block; }
.info-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 8px 16px; margin-top: 12px; font-size: 14px; }
.info-grid .label { color: #888; margin-right: 6px; }
.form-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 12px 16px; margin-bottom: 16px; }
.form-grid label { font-size: 14px; color: #555; display: flex; flex-direction: column; gap: 4px; }
.form-grid input { padding: 8px 10px; border: 1px solid #ccd; border-radius: 8px; font-size: 15px; font-family: inherit; }
.form-grid input:focus { outline: 2px solid #4a6cf7; outline-offset: -1px; border-color: #4a6cf7; }
.btn-primary { display: inline-block; background: #4a6cf7; color: #fff; border: none; border-radius: 8px; padding: 10px 28px; font-size: 15px; cursor: pointer; text-decoration: none; font-family: inherit; }
.btn-primary:disabled, .btn-primary.disabled { background: #b8c2e8; cursor: not-allowed; pointer-events: none; }
.progress-bar { height: 10px; background: #e4e8f2; border-radius: 5px; overflow: hidden; margin: 14px 0 8px; }
#progressFill { height: 100%; width: 0%; background: #4a6cf7; border-radius: 5px; transition: width .3s; }
#progressText { font-size: 14px; color: #555; font-variant-numeric: tabular-nums; }
.thumbnail-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 12px; margin: 14px 0; }
.thumb { position: relative; border-radius: 8px; overflow: hidden; box-shadow: 0 1px 3px rgba(0,0,0,0.15); background: #fff; }
.thumb img { width: 100%; display: block; }
.thumb-time { position: absolute; left: 6px; bottom: 6px; background: rgba(0,0,0,0.65); color: #fff; font-size: 12px; padding: 2px 8px; border-radius: 4px; font-variant-numeric: tabular-nums; }
.error-box { background: #fdecea; border: 1px solid #f5c6c0; color: #b3261e; border-radius: 8px; padding: 12px 16px; margin-top: 16px; font-size: 14px; }
#zipName { font-size: 14px; color: #555; margin-bottom: 12px; word-break: break-all; }
#resultMessage { font-size: 15px; font-weight: 600; }
.hint { font-size: 12px; color: #999; margin-top: 4px; }
</style>
</head>
<body>
<div class="container">
  <h1>FramePack</h1>
  <p class="subtitle">ローカルの動画ファイルからフレーム画像とメタデータを抽出し、ZIP（解析データファイル）を生成します。</p>

  <section class="step" id="step1">
    <h2><span class="step-num">1</span>動画読み込み</h2>
    <div id="dropzone" class="dropzone">
      <p>クリックまたはドラッグ＆ドロップで動画ファイルを選択</p>
      <input type="file" id="fileInput" accept="video/*" hidden>
    </div>
    <div id="videoInfo" class="video-info" hidden>
      <video id="preview" controls></video>
      <div class="info-grid">
        <div><span class="label">ファイル名</span><span id="infoName"></span></div>
        <div><span class="label">長さ</span><span id="infoDuration"></span></div>
        <div><span class="label">サイズ</span><span id="infoSize"></span></div>
        <div><span class="label">解像度</span><span id="infoResolution"></span></div>
      </div>
    </div>
  </section>

  <section class="step" id="step2">
    <h2><span class="step-num">2</span>抽出範囲指定</h2>
    <div class="form-grid">
      <label>開始時間（例: 0:05 または 83）
        <input type="text" id="startTime" placeholder="0:05" value="0:00">
      </label>
      <label>切り取る長さ（秒、0.5以上）
        <input type="number" id="duration" min="0.5" step="0.1" value="3">
      </label>
      <label>抽出間隔（秒、0.1以上。既定 0.5）
        <input type="number" id="interval" min="0.1" step="0.1" value="0.5">
      </label>
    </div>
    <button id="extractBtn" class="btn-primary" disabled>フレーム抽出</button>
    <div id="progressArea" hidden>
      <div class="progress-bar"><div id="progressFill"></div></div>
      <p id="progressText">抽出中… 0 / 0</p>
    </div>
  </section>

  <section class="step" id="step3">
    <h2><span class="step-num">3</span>結果</h2>
    <p id="resultMessage"></p>
    <div id="thumbnailGrid" class="thumbnail-grid"></div>
    <p id="zipName"></p>
    <a id="downloadBtn" class="btn-primary disabled" href="/download">ZIPをダウンロード</a>
  </section>

  <div id="errorBox" class="error-box" hidden></div>
</div>
<script>
const dropzone = document.getElementById("dropzone");
const fileInput = document.getElementById("fileInput");
const videoInfo = document.getElementById("videoInfo");
const preview = document.getElementById("preview");
const extractBtn = document.getElementById("extractBtn");
const progressArea = document.getElementById("progressArea");
const progressText = document.getElementById("progressText");
const progressFill = document.getElementById("progressFill");
const errorBox = document.getElementById("errorBox");
const downloadBtn = document.getElementById("downloadBtn");
let pollTimer = null;
let pollFailCount = 0;

function showError(msg) {
  errorBox.textContent = msg;
  errorBox.hidden = false;
}
function hideError() {
  errorBox.hidden = true;
  errorBox.textContent = "";
}
function formatTime(sec) {
  const m = Math.floor(sec / 60);
  const s = sec - m * 60;
  return m + ":" + s.toFixed(1).padStart(4, "0");
}
function formatSize(bytes) {
  if (bytes >= 1e9) return (bytes / 1e9).toFixed(2) + " GB";
  if (bytes >= 1e6) return (bytes / 1e6).toFixed(2) + " MB";
  if (bytes >= 1e3) return (bytes / 1e3).toFixed(2) + " KB";
  return bytes + " B";
}

dropzone.addEventListener("click", () => fileInput.click());
dropzone.addEventListener("dragover", (e) => { e.preventDefault(); dropzone.classList.add("dragover"); });
dropzone.addEventListener("dragleave", () => dropzone.classList.remove("dragover"));
dropzone.addEventListener("drop", (e) => {
  e.preventDefault();
  dropzone.classList.remove("dragover");
  if (e.dataTransfer.files.length > 0) handleFile(e.dataTransfer.files[0]);
});
fileInput.addEventListener("change", () => {
  if (fileInput.files.length > 0) handleFile(fileInput.files[0]);
});

function handleFile(file) {
  if (!file) return;
  if (!file.type.startsWith("video/")) {
    showError("動画ファイルのみ選択できます（video/*）");
    return;
  }
  hideError();
  const formData = new FormData();
  formData.append("video", file);
  fetch("/api/upload", { method: "POST", body: formData })
    .then((r) => r.json())
    .then((data) => {
      if (data.error) { showError(data.error); return; }
      preview.src = "/video?t=" + Date.now();
      document.getElementById("infoName").textContent = data.filename;
      document.getElementById("infoDuration").textContent = formatTime(data.duration_seconds) + "（" + data.duration_seconds.toFixed(1) + "秒）";
      document.getElementById("infoSize").textContent = formatSize(data.file_size_bytes);
      document.getElementById("infoResolution").textContent = data.width + " × " + data.height + " / " + data.fps.toFixed(2) + " fps / " + data.codec;
      videoInfo.hidden = false;
      extractBtn.disabled = false;
    })
    .catch(() => showError("サーバーとの通信に失敗しました。サーバーが停止している可能性があります"));
}

extractBtn.addEventListener("click", () => {
  hideError();
  const start = document.getElementById("startTime").value.trim();
  const duration = document.getElementById("duration").value;
  const interval = document.getElementById("interval").value;
  if (!start || !duration || !interval) {
    showError("開始時間・長さ・間隔をすべて入力してください");
    return;
  }
  fetch("/api/extract", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ start: start, duration: duration, interval: interval })
  })
    .then((r) => r.json())
    .then((data) => {
      if (data.error) { showError(data.error); return; }
      startPolling();
    })
    .catch(() => showError("サーバーとの通信に失敗しました。サーバーが停止している可能性があります"));
});

function startPolling() {
  progressArea.hidden = false;
  extractBtn.disabled = true;
  pollFailCount = 0;
  pollTimer = setInterval(pollStatus, POLL_INTERVAL_MS_PLACEHOLDER);
}

function pollStatus() {
  fetch("/api/status")
    .then((r) => r.json())
    .then((data) => {
      pollFailCount = 0;
      if (data.status === "running" || data.status === "starting") {
        progressText.textContent = "抽出中… " + data.progress_current + " / " + data.progress_total + "（" + data.percent + "%）";
        progressFill.style.width = data.percent + "%";
      } else if (data.status === "done") {
        clearInterval(pollTimer);
        pollTimer = null;
        showResult(data.result);
      } else if (data.status === "error") {
        clearInterval(pollTimer);
        pollTimer = null;
        progressArea.hidden = true;
        extractBtn.disabled = false;
        showError(data.error || "抽出処理でエラーが発生しました");
      }
    })
    .catch(() => {
      pollFailCount++;
      if (pollFailCount >= 3) {
        clearInterval(pollTimer);
        pollTimer = null;
        progressArea.hidden = true;
        extractBtn.disabled = false;
        showError("サーバーとの通信に失敗しました。サーバーが停止している可能性があります");
      }
    });
}

function showResult(result) {
  progressArea.hidden = true;
  extractBtn.disabled = false;
  document.getElementById("resultMessage").textContent = result.frame_count + "枚のフレームを抽出しました" + (result.incomplete ? "（動画の終端に達したため途中で終了しました）" : "");
  const grid = document.getElementById("thumbnailGrid");
  grid.innerHTML = "";
  result.frames.forEach((f) => {
    const div = document.createElement("div");
    div.className = "thumb";
    const img = document.createElement("img");
    img.src = "/api/result/frame/" + f.index;
    img.alt = f.file;
    const cap = document.createElement("span");
    cap.className = "thumb-time";
    cap.textContent = formatTime(f.timestamp_seconds);
    div.appendChild(img);
    div.appendChild(cap);
    grid.appendChild(div);
  });
  document.getElementById("zipName").textContent = "ZIPファイル: " + result.zip_name;
  downloadBtn.classList.remove("disabled");
  downloadBtn.href = "/download";
}
</script>
</body>
</html>
""".replace("POLL_INTERVAL_MS_PLACEHOLDER", str(POLL_INTERVAL_MS))

app = Flask(__name__)
logging.getLogger("werkzeug").setLevel(logging.ERROR)

job_lock = threading.Lock()
job_state = {
    "status": "idle",
    "progress_current": 0,
    "progress_total": 0,
    "percent": 0,
    "error": None,
    "result": None,
}

upload_lock = threading.Lock()
upload_state = {"dir": None, "path": None, "filename": None, "mimetype": None, "info": None}

_white_pixel = None
_white_pixel_lock = threading.Lock()


def get_white_pixel():
    global _white_pixel
    if _white_pixel is None:
        with _white_pixel_lock:
            if _white_pixel is None:
                data = base64.b64decode(WHITE_JPEG_B64)
                arr = cv2.imdecode(np.frombuffer(data, dtype=np.uint8), cv2.IMREAD_COLOR)
                _white_pixel = arr
    return _white_pixel


def white_canvas(width, height):
    pixel = get_white_pixel()
    canvas = np.empty((height, width, 3), dtype=np.uint8)
    canvas[:] = pixel[0, 0]
    return canvas


def parse_time_input(s):
    s = s.strip()
    if not s:
        raise ValueError("empty")
    if ":" in s:
        parts = s.split(":")
        if len(parts) != 2:
            raise ValueError("bad format")
        minutes = int(parts[0].strip())
        seconds = float(parts[1].strip())
        if minutes < 0 or seconds < 0 or seconds >= 60:
            raise ValueError("out of range")
        return minutes * 60 + seconds
    value = float(s)
    if value < 0:
        raise ValueError("negative")
    return value


def format_timestamp(t):
    minutes = int(t // 60)
    seconds = t - minutes * 60
    return "t{:02d}m{:04.1f}s".format(minutes, seconds)


def sanitize_basename(filename):
    base = os.path.splitext(os.path.basename(filename))[0]
    base = re.sub(r'[\\/:*?"<>|]', "_", base)
    base = base.strip()
    if not base or base in (".", ".."):
        base = "video"
    return base


def fourcc_to_codec(fourcc_int):
    if not fourcc_int:
        return "unknown"
    chars = []
    for i in range(4):
        c = (int(fourcc_int) >> (8 * i)) & 0xFF
        if c == 0:
            return "unknown"
        chars.append(chr(c))
    s = "".join(chars).lower()
    if s in ("h264", "avc1", "x264"):
        return "h264"
    return s


def get_video_info(path):
    cap = cv2.VideoCapture(path)
    if not cap.isOpened():
        cap.release()
        return None
    fps = cap.get(cv2.CAP_PROP_FPS)
    frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
    width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
    height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
    fourcc = int(cap.get(cv2.CAP_PROP_FOURCC))
    cap.release()
    if fps and fps > 0 and frame_count and frame_count > 0:
        duration = frame_count / fps
    else:
        duration = 0.0
    return {
        "duration_seconds": duration,
        "width": width,
        "height": height,
        "fps": fps,
        "codec": fourcc_to_codec(fourcc),
        "frame_count": int(frame_count) if frame_count and frame_count > 0 else 0,
    }


def validate_params(start, duration, interval, video_duration):
    if math.isnan(start) or math.isnan(duration) or math.isnan(interval):
        return ("入力値が不正です", None, None)
    if math.isinf(start) or math.isinf(duration) or math.isinf(interval):
        return ("入力値が不正です", None, None)
    if start < 0 or start >= video_duration:
        return ("開始時間は0以上、動画の長さ未満の値にしてください", None, None)
    if duration < 0.5:
        return ("長さは0.5秒以上にしてください", None, None)
    if interval < 0.1:
        return ("間隔は0.1秒以上にしてください", None, None)
    expected = int(round(duration / interval)) + 1
    if expected > MAX_TOTAL_FRAMES:
        return ("総フレーム数が60枚を超えるため、間隔を広げてください", None, None)
    if start + duration > video_duration:
        duration = round(video_duration - start, 3)
        expected = int(round(duration / interval)) + 1
    return (None, duration, expected)


def extract_frames(video_path, start, duration, interval, quality, out_dir, progress_cb=None):
    frames_dir = os.path.join(out_dir, "frames")
    os.makedirs(frames_dir, exist_ok=True)
    cap = cv2.VideoCapture(video_path)
    if not cap.isOpened():
        raise RuntimeError("動画情報を取得できませんでした")
    frames = []
    try:
        k = 0
        end = start + duration
        while True:
            t = start + k * interval
            if t > end + 1e-9:
                break
            cap.set(cv2.CAP_PROP_POS_MSEC, t * 1000)
            ok, frame = cap.read()
            if not ok or frame is None:
                break
            index = k + 1
            filename = "{:03d}_{}.jpg".format(index, format_timestamp(t))
            rel_path = "frames/" + filename
            abs_path = os.path.join(out_dir, rel_path)
            cv2.imwrite(abs_path, frame, [cv2.IMWRITE_JPEG_QUALITY, quality])
            h, w = frame.shape[:2]
            frames.append({
                "index": index,
                "file": rel_path,
                "timestamp_seconds": round(t, 3),
                "width": w,
                "height": h,
                "path": abs_path,
            })
            if progress_cb:
                progress_cb(len(frames))
            k += 1
    finally:
        cap.release()
    return frames


def build_manifest(video_info, extraction_config, frames):
    manifest = {
        "schema_version": "1.0",
        "tool": "framepack",
        "created_at": datetime.now().astimezone().replace(microsecond=0).isoformat(),
        "source": {
            "filename": video_info["filename"],
            "file_size_bytes": video_info["file_size_bytes"],
            "duration_seconds": round(video_info["duration_seconds"], 1),
            "width": video_info["width"],
            "height": video_info["height"],
            "fps": round(video_info["fps"], 2),
            "codec": video_info["codec"],
        },
        "extraction": {
            "start_time_seconds": extraction_config["start_time_seconds"],
            "duration_seconds": extraction_config["duration_seconds"],
            "interval_seconds": extraction_config["interval_seconds"],
            "frame_count": len(frames),
            "image_format": "jpeg",
            "jpeg_quality": extraction_config["jpeg_quality"],
        },
        "frames": [
            {
                "index": f["index"],
                "file": f["file"],
                "timestamp_seconds": f["timestamp_seconds"],
                "width": f["width"],
                "height": f["height"],
            }
            for f in frames
        ],
        "contact_sheet": "contact_sheet.jpg",
    }
    if extraction_config.get("incomplete"):
        manifest["extraction"]["incomplete"] = True
    if extraction_config.get("contact_sheet_truncated"):
        manifest["extraction"]["contact_sheet_truncated"] = True
    return manifest


def draw_text_with_outline(img, text, org, font_scale=0.6, thickness=2):
    x, y = org
    cv2.putText(img, text, (x + 2, y + 2), cv2.FONT_HERSHEY_SIMPLEX, font_scale, (0, 0, 0), thickness + 2, cv2.LINE_AA)
    cv2.putText(img, text, (x, y), cv2.FONT_HERSHEY_SIMPLEX, font_scale, (255, 255, 255), thickness, cv2.LINE_AA)


def build_contact_sheet(frames, out_dir):
    cell_w = CONTACT_SHEET_CELL_WIDTH
    cols = CONTACT_SHEET_COLS
    if frames:
        first = cv2.imread(frames[0]["path"])
        h0, w0 = first.shape[:2]
        cell_h = max(1, int(round(cell_w * h0 / w0)))
    else:
        cell_h = 270
    n = len(frames)
    rows = max(1, math.ceil(n / cols)) if n else 1
    canvas = white_canvas(cell_w * cols, cell_h * rows)
    for i in range(n):
        img = cv2.imread(frames[i]["path"])
        if img is None:
            continue
        resized = cv2.resize(img, (cell_w, cell_h), interpolation=cv2.INTER_AREA)
        r, c = divmod(i, cols)
        y, x = r * cell_h, c * cell_w
        canvas[y:y + cell_h, x:x + cell_w] = resized
        label = format_timestamp(frames[i]["timestamp_seconds"])
        draw_text_with_outline(canvas, label, (x + 8, y + cell_h - 10))
    out_path = os.path.join(out_dir, "contact_sheet.jpg")
    cv2.imwrite(out_path, canvas, [cv2.IMWRITE_JPEG_QUALITY, CONTACT_SHEET_JPEG_QUALITY])
    return out_path


def build_zip(out_dir, zip_path):
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        manifest_path = os.path.join(out_dir, "manifest.json")
        if os.path.exists(manifest_path):
            zf.write(manifest_path, "manifest.json")
        frames_dir = os.path.join(out_dir, "frames")
        if os.path.isdir(frames_dir):
            for name in sorted(os.listdir(frames_dir)):
                zf.write(os.path.join(frames_dir, name), "frames/" + name)
        sheet_path = os.path.join(out_dir, "contact_sheet.jpg")
        if os.path.exists(sheet_path):
            zf.write(sheet_path, "contact_sheet.jpg")
    return zip_path


def run_extraction(params):
    tmp_dir = None
    try:
        with job_lock:
            job_state.update({
                "status": "running",
                "progress_current": 0,
                "progress_total": params["expected"],
                "percent": 0,
                "error": None,
                "result": None,
            })
        start = params["start"]
        duration = params["duration"]
        interval = params["interval"]
        tmp_dir = tempfile.mkdtemp(prefix="framepack_job_")

        def progress_cb(current):
            with job_lock:
                total = job_state["progress_total"]
                job_state["progress_current"] = current
                job_state["percent"] = int(current * 100 / total) if total else 100

        frames = extract_frames(params["video_path"], start, duration, interval, JPEG_QUALITY, tmp_dir, progress_cb)
        incomplete = len(frames) < params["expected"]
        truncated = len(frames) > CONTACT_SHEET_MAX_FRAMES
        sheet_frames = frames[:CONTACT_SHEET_MAX_FRAMES] if truncated else frames
        build_contact_sheet(sheet_frames, tmp_dir)
        info = params["video_info"]
        video_info = {
            "filename": params["filename"],
            "file_size_bytes": params["file_size_bytes"],
            "duration_seconds": info["duration_seconds"],
            "width": info["width"],
            "height": info["height"],
            "fps": info["fps"],
            "codec": info["codec"],
        }
        extraction_config = {
            "start_time_seconds": start,
            "duration_seconds": duration,
            "interval_seconds": interval,
            "jpeg_quality": JPEG_QUALITY,
            "incomplete": incomplete,
            "contact_sheet_truncated": truncated,
        }
        manifest = build_manifest(video_info, extraction_config, frames)
        with open(os.path.join(tmp_dir, "manifest.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f, ensure_ascii=False, indent=2)
        base = sanitize_basename(params["filename"])
        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        zip_name = "{}_frames_{}.zip".format(base, ts)
        out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_DIR_NAME)
        os.makedirs(out_dir, exist_ok=True)
        zip_path = os.path.join(out_dir, zip_name)
        build_zip(tmp_dir, zip_path)
        result = {
            "zip_name": zip_name,
            "zip_path": zip_path,
            "zip_size_bytes": os.path.getsize(zip_path),
            "frame_count": len(frames),
            "incomplete": incomplete,
            "contact_sheet_truncated": truncated,
            "frames": [
                {
                    "index": f["index"],
                    "file": f["file"],
                    "timestamp_seconds": f["timestamp_seconds"],
                }
                for f in frames
            ],
        }
        with job_lock:
            job_state.update({
                "status": "done",
                "progress_current": len(frames),
                "percent": 100,
                "result": result,
            })
    except Exception as e:
        with job_lock:
            if isinstance(e, OSError):
                msg = "ディスク容量が不足している可能性があります。不要なファイルを削除してから再度お試しください"
            else:
                msg = str(e) or "抽出処理でエラーが発生しました"
            job_state.update({"status": "error", "error": msg})
    finally:
        if tmp_dir:
            shutil.rmtree(tmp_dir, ignore_errors=True)


@app.route("/")
def index():
    return Response(INDEX_HTML, mimetype="text/html")


@app.route("/api/upload", methods=["POST"])
def api_upload():
    if "video" not in request.files:
        return jsonify({"error": "動画ファイルが選択されていません"}), 400
    file = request.files["video"]
    if not file or not file.filename:
        return jsonify({"error": "動画ファイルが選択されていません"}), 400
    filename = os.path.basename(file.filename)
    ext = os.path.splitext(filename)[1].lower()[:10] or ".mp4"
    tmp_dir = tempfile.mkdtemp(prefix="framepack_upload_")
    save_path = os.path.join(tmp_dir, "video" + ext)
    try:
        file.save(save_path)
    except OSError:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return jsonify({"error": "ディスク容量が不足している可能性があります。不要なファイルを削除してから再度お試しください"}), 500
    info = get_video_info(save_path)
    if info is None:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return jsonify({"error": "この動画形式は読み込めません（MP4/H.264推奨）"}), 400
    if not info["fps"] or info["fps"] <= 0 or info["duration_seconds"] <= 0:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return jsonify({"error": "動画情報を取得できませんでした"}), 400
    info["file_size_bytes"] = os.path.getsize(save_path)
    with upload_lock:
        old_dir = upload_state["dir"]
        upload_state.update({
            "dir": tmp_dir,
            "path": save_path,
            "filename": filename,
            "mimetype": file.mimetype or "video/mp4",
            "info": info,
        })
    if old_dir:
        shutil.rmtree(old_dir, ignore_errors=True)
    return jsonify({
        "filename": filename,
        "duration_seconds": info["duration_seconds"],
        "width": info["width"],
        "height": info["height"],
        "fps": info["fps"],
        "codec": info["codec"],
        "file_size_bytes": info["file_size_bytes"],
    })


@app.route("/video")
def video():
    with upload_lock:
        path = upload_state["path"]
        mimetype = upload_state["mimetype"] or "video/mp4"
    if not path or not os.path.exists(path):
        return jsonify({"error": "動画が読み込まれていません"}), 404
    return send_file(path, mimetype=mimetype)


@app.route("/api/extract", methods=["POST"])
def api_extract():
    with upload_lock:
        if not upload_state["path"]:
            return jsonify({"error": "動画ファイルを先に読み込んでください"}), 400
        video_path = upload_state["path"]
        filename = upload_state["filename"]
        info = upload_state["info"]
    data = request.get_json(silent=True) or {}
    try:
        start = parse_time_input(str(data.get("start", "")))
        duration = float(data.get("duration", 0))
        interval = float(data.get("interval", 0))
    except (ValueError, TypeError):
        return jsonify({"error": "入力値が不正です"}), 400
    error, duration, expected = validate_params(start, duration, interval, info["duration_seconds"])
    if error:
        return jsonify({"error": error}), 400
    with job_lock:
        if job_state["status"] in ("running", "starting"):
            return jsonify({"error": "抽出処理が実行中です"}), 409
        job_state["status"] = "starting"
    params = {
        "video_path": video_path,
        "filename": filename,
        "file_size_bytes": info["file_size_bytes"],
        "video_info": info,
        "start": start,
        "duration": duration,
        "interval": interval,
        "expected": expected,
    }
    t = threading.Thread(target=run_extraction, args=(params,), daemon=True)
    t.start()
    return jsonify({"ok": True})


@app.route("/api/status")
def api_status():
    with job_lock:
        status = job_state["status"]
        progress_current = job_state["progress_current"]
        progress_total = job_state["progress_total"]
        percent = job_state["percent"]
        error = job_state["error"]
        result = job_state["result"]
    result_out = None
    if result:
        result_out = {
            "zip_name": result["zip_name"],
            "frame_count": result["frame_count"],
            "incomplete": result["incomplete"],
            "contact_sheet_truncated": result["contact_sheet_truncated"],
            "frames": result["frames"],
        }
    return jsonify({
        "status": status,
        "progress_current": progress_current,
        "progress_total": progress_total,
        "percent": percent,
        "error": error,
        "result": result_out,
    })


@app.route("/api/result/frame/<int:index>")
def result_frame(index):
    with job_lock:
        result = job_state["result"]
    if not result:
        return jsonify({"error": "結果がありません"}), 404
    target = None
    for f in result["frames"]:
        if f["index"] == index:
            target = f["file"]
            break
    if not target:
        return jsonify({"error": "フレームが見つかりません"}), 404
    try:
        with zipfile.ZipFile(result["zip_path"]) as zf:
            data = zf.read(target)
    except (OSError, zipfile.BadZipFile, KeyError):
        return jsonify({"error": "フレームを読み込めませんでした"}), 500
    return Response(data, mimetype="image/jpeg")


@app.route("/download")
def download():
    with job_lock:
        result = job_state["result"]
    if not result:
        return jsonify({"error": "ダウンロード可能な結果がありません"}), 404
    return send_file(result["zip_path"], as_attachment=True, download_name=result["zip_name"])


@app.errorhandler(404)
def not_found(e):
    return jsonify({"error": "リクエスト先が見つかりません"}), 404


@app.errorhandler(500)
def internal_error(e):
    return jsonify({"error": "サーバー内部でエラーが発生しました"}), 500


def find_available_port(start_port, max_tries=20):
    for p in range(start_port, start_port + max_tries):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind((HOST, p))
                return p
            except OSError:
                continue
    return None


def main():
    port = find_available_port(PORT)
    if port is None:
        print("エラー: 使用可能なポートが見つかりませんでした（8765-8784）")
        return
    url = "http://localhost:{}".format(port)
    print("FramePack を起動しました: {}".format(url))
    print("ブラウザが自動で開きます。終了するには Ctrl+C を押してください。")
    threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        app.run(host=HOST, port=port, threaded=True)
    except KeyboardInterrupt:
        print("\n終了しました")
    finally:
        with upload_lock:
            d = upload_state["dir"]
        if d:
            shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    main()
