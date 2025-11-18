from PyQt5.QtCore import QTimer, QSettings, Qt, pyqtSignal
from PyQt5.QtWidgets import (
    QApplication,
    QWidget,
    QVBoxLayout,
    QHBoxLayout,
    QLineEdit,
    QPushButton,
    QLabel,
    QCheckBox,
    QListWidget,
    QListWidgetItem,
    QComboBox,
    QTextEdit,
    QProgressBar,
    QFileDialog,
    QMessageBox,
    QSplitter,
)
from PyQt5.QtGui import QPixmap, QImage, QIcon, QTextCursor
from yt_dlp import YoutubeDL
import queue
import copy
import sys
import os
import subprocess
import time
import ctypes
import re
import urllib.request


def resource_path(filename: str) -> str:
    """
    取得資源的正確路徑（支援 PyInstaller 的 sys._MEIPASS）。
    """
    base_path = getattr(sys, "_MEIPASS", None)
    if base_path is None:
        base_path = os.path.abspath(os.path.dirname(__file__))
    return os.path.join(base_path, filename)


# 全域錯誤日誌
def _global_excepthook(exc_type, exc_value, exc_tb):
    log = os.path.join(os.path.dirname(__file__), "error_log.txt")
    with open(log, "a", encoding="utf-8") as f:
        ts = time.time()
        f.write(f"\n[{ts}]\n")
        import traceback

        traceback.print_exception(exc_type, exc_value, exc_tb, file=f)


def set_windows_creation_time(path, timestamp=None):
    """
    在 Windows 設定檔案建立時間（timestamp 為 epoch 秒）。
    若不是 Windows 或失敗，會安靜忽略。
    """
    try:
        if os.name != "nt":
            return
        timestamp = time.time() if timestamp is None else float(timestamp)
        # Windows FILETIME expects 100-nanosecond intervals since Jan 1, 1601
        from ctypes import wintypes

        wintime = int((timestamp + 11644473600) * 10000000)
        ctime = wintypes.FILETIME(wintime & 0xFFFFFFFF, wintime >> 32)

        # open file handle
        handle = ctypes.windll.kernel32.CreateFileW(
            str(path),
            256,  # GENERIC_WRITE
            0,
            None,
            3,  # OPEN_EXISTING
            0x02000000,  # FILE_FLAG_BACKUP_SEMANTICS
            None,
        )
        if handle == -1:
            return
        # set creation, access, write times (we set all to same time)
        res = ctypes.windll.kernel32.SetFileTime(
            handle, ctypes.byref(ctime), ctypes.byref(ctime), ctypes.byref(ctime)
        )
        ctypes.windll.kernel32.CloseHandle(handle)
        return bool(res)
    except Exception:
        return


# Dark QSS 樣式（PyQt5 專案預設 QSS）
dark_qss = """
QWidget {
    background-color: #2e2e2e;
    color: #f0f0f0;
    font-family: "Microsoft JhengHei";
    font-size: 14px;
}
QPushButton {
    background-color: #444;
    color: white;
    padding: 8px 16px;
    border-radius: 6px;
}
QPushButton:disabled {
    background-color: #2a2a2a;
    color: #888;
}
QPushButton:hover:!disabled {
    background-color: #666;
}
QLineEdit, QTextEdit, QComboBox {
    background-color: #1e1e1e;
    color: #f0f0f0;
    border: 1px solid #555;
    border-radius: 4px;
    padding: 4px;
}
QLabel, QCheckBox {
    font-weight: bold;
    color: #f0f0f0;
}
QProgressBar {
    border: 1px solid #555;
    border-radius: 4px;
    background-color: #1e1e1e;
    text-align: center;
    color: #f0f0f0;
}
QProgressBar::chunk {
    background-color: #88c0d0;
    border-radius: 4px;
}
QComboBox QAbstractItemView {
    background-color: #1e1e1e;
    border: 1px solid #555;
    selection-background-color: #444;
    color: #f0f0f0;
}
QScrollBar:vertical {
    border: none;
    background: #2e2e2e;
    width: 8px;
    margin: 0px;
    border-radius: 4px;
}
QScrollBar::handle:vertical {
    background: #555;
    min-height: 20px;
    border-radius: 4px;
}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
    height: 0px;
}
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
    background: none;
}
"""


class YTMediaDownloader(QWidget):
    log_signal = pyqtSignal(str, str)

    progress_signal = pyqtSignal(int)
    status_signal = pyqtSignal(str)
    analyzed = pyqtSignal()
    err_signal = pyqtSignal(str)
    info_signal = pyqtSignal(str)
    thumbnail_loaded_signal = pyqtSignal(bytes)
    thumbnail_error_signal = pyqtSignal()
    download_button_signal = pyqtSignal(bool)
    analyze_button_signal = pyqtSignal(bool)

    def __init__(self):
        super().__init__()
        # ---- 安全設定 icon（只有在檔案存在時才設定） ----
        icon_path = resource_path("icon.ico")
        try:
            if os.path.exists(icon_path):
                app = QApplication.instance()
                if app is not None:
                    app.setWindowIcon(
                        QIcon(icon_path)
                    )  # 全域 icon（taskbar / Alt+Tab）
                self.setWindowIcon(QIcon(icon_path))  # 視窗左上角
            else:
                # 若找不到 icon，僅在 console 記錄警告（避免拋例外）
                print(f"[WARN] icon not found: {icon_path}")
        except Exception as e:
            # 保險起見：任何異常都不要讓 GUI 崩潰
            print(f"[WARN] 無法設定 icon: {e}")

        self.formats = []
        self.info = None
        self.queue_keys = []

        self.settings = QSettings("YTMediaDownloader", "YTMediaDownloader")

        self._init_ui()
        self._toggle_audio_mode(self.audio_only.isChecked())
        self.analyzed.connect(self._on_analysis_done)
        self.err_signal.connect(self._show_error)
        self.info_signal.connect(self._show_info)
        self.log_queue = queue.Queue()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._process_log_queue)
        self.timer.start(100)
        self.log_signal.connect(lambda msg, lvl: self.log_queue.put((msg, lvl)))
        self.progress_signal.connect(self.progress.setValue)
        self.status_signal.connect(self.status.setText)
        self.thumbnail_loaded_signal.connect(self._set_thumbnail_pixmap)
        self.thumbnail_error_signal.connect(self._set_thumbnail_error)
        self.download_button_signal.connect(self.download_btn.setEnabled)
        self.analyze_button_signal.connect(self.analyze_btn.setEnabled)

        self._updating_check_state = 0
        self._selected_items = []
        self.select_all_checkbox.stateChanged.connect(self._on_select_all_state_changed)
        self.queue_list.itemChanged.connect(self._on_queue_item_check_state_changed)

        self._load_settings()

        self.queue_list.currentItemChanged.connect(self._on_queue_item_selected)
        self.queue_list.itemSelectionChanged.connect(self._update_remove_button_state)
        self.url_input.textChanged.connect(self._on_url_changed)

        # 確保初始化時按鈕狀態正確
        self._update_add_button_state()
        self._update_remove_button_state()
        self._update_select_all_checkbox()

    def _init_ui(self):
        self.setWindowTitle("YT Media Downloader")
        self.resize(960, 720)
        main_splitter = QSplitter(Qt.Vertical, self)

        top_url_analysis_box = QWidget()
        top_url_analysis_layout = QHBoxLayout(top_url_analysis_box)
        self.url_input = QLineEdit()
        top_url_analysis_layout.addWidget(self.url_input)
        self.analyze_btn = QPushButton("分析資訊")
        self.analyze_btn.clicked.connect(self.analyze_url)
        top_url_analysis_layout.addWidget(self.analyze_btn)

        self.thumbnail_label = QLabel("無縮圖")
        self.thumbnail_label.setAlignment(Qt.AlignCenter)
        self.thumbnail_label.setFixedSize(320, 180)
        self.thumbnail_label.setStyleSheet(
            "border: 1px solid #555; background-color: #1a1a1a;"
        )

        top_content_layout = QHBoxLayout()
        top_content_layout.addWidget(top_url_analysis_box)
        top_content_layout.addWidget(self.thumbnail_label)
        self._set_thumbnail_placeholder()

        top_widget = QWidget()
        top_widget.setLayout(top_content_layout)
        main_splitter.addWidget(top_widget)

        queue_box = QWidget()
        queue_layout = QVBoxLayout(queue_box)
        select_all_layout = QHBoxLayout()
        self.select_all_checkbox = QCheckBox("全選")
        self.select_all_checkbox.setTristate(True)
        select_all_layout.addWidget(self.select_all_checkbox)
        select_all_layout.addStretch()
        queue_layout.addLayout(select_all_layout)
        self.queue_list = QListWidget()
        self.queue_list.setSelectionMode(QListWidget.MultiSelection)
        btns = QHBoxLayout()
        self.add_btn = QPushButton("加入佇列")
        self.add_btn.clicked.connect(self.add_current_to_queue)
        self.remove_btn = QPushButton("移除所選")
        self.remove_btn.clicked.connect(self.remove_selected_queue_items)
        btns.addWidget(self.add_btn)
        btns.addWidget(self.remove_btn)
        queue_layout.addWidget(self.queue_list)
        queue_layout.addLayout(btns)
        main_splitter.addWidget(queue_box)

        opts_box = QWidget()
        opts = QHBoxLayout(opts_box)
        self.res_label = QLabel("解析度：")
        opts.addWidget(self.res_label)
        self.res_combo = QComboBox()
        opts.addWidget(self.res_combo)
        self.audio_label = QLabel("音訊格式：")
        opts.addWidget(self.audio_label)
        self.audio_combo = QComboBox()
        opts.addWidget(self.audio_combo)
        self.audio_only = QCheckBox("僅音訊")
        opts.addWidget(self.audio_only)
        self.audio_only.toggled.connect(self._toggle_audio_mode)
        self.ext_label = QLabel("封裝格式：")
        opts.addWidget(self.ext_label)
        self.ext_combo = QComboBox()
        self.ext_combo.addItems(["mp4", "mkv", "webm"])
        self.ext_combo.setCurrentText("mp4")
        opts.addWidget(self.ext_combo)
        main_splitter.addWidget(opts_box)

        cmd_box = QWidget()
        cmd_layout = QVBoxLayout(cmd_box)
        d = QHBoxLayout()
        d.addWidget(QLabel("下載到："))
        self.dir_label = QLabel(os.path.join(os.path.expanduser("~"), "Downloads"))
        d.addWidget(self.dir_label, 3)
        choose = QPushButton("選擇下載資料夾")
        choose.clicked.connect(self.choose_directory)
        d.addWidget(choose)
        cmd_layout.addLayout(d)
        self.cmd_text = QTextEdit()
        self.cmd_text.setFixedHeight(60)
        self.cmd_text.setReadOnly(False)
        cmd_layout.addWidget(self.cmd_text)
        btnbar = QHBoxLayout()
        self.gen_btn = QPushButton("產生指令")
        self.gen_btn.clicked.connect(self.generate_command)
        self.download_btn = QPushButton("下載")
        self.download_btn.clicked.connect(self.handle_download_click)
        btnbar.addWidget(self.gen_btn)
        btnbar.addWidget(self.download_btn)
        cmd_layout.addLayout(btnbar)
        main_splitter.addWidget(cmd_box)

        bottom_box = QWidget()
        bottom_layout = QVBoxLayout(bottom_box)
        self.progress = QProgressBar()
        bottom_layout.addWidget(self.progress)
        self.status = QLabel()
        bottom_layout.addWidget(self.status)
        self.log_checkbox = QCheckBox("顯示訊息記錄")
        self.log_checkbox.setChecked(False)
        self.log_checkbox.toggled.connect(self.toggle_log_output)
        bottom_layout.addWidget(self.log_checkbox)
        self.log_output = QTextEdit()
        self.log_output.setReadOnly(True)
        self.log_output.setVisible(False)
        bottom_layout.addWidget(self.log_output)
        main_splitter.addWidget(bottom_box)
        layout = QVBoxLayout(self)
        layout.addWidget(main_splitter)

    def _on_url_changed(self, _txt: str):
        """
        只要 URL 被修改，就視為『尚未分析』狀態：
        1. 把 self.info 清空
        2. 重新評估「加入佇列」按鈕是否能按
        """
        self.info = None
        self._update_add_button_state()

    def _load_settings(self):
        last_download_path = self.settings.value("download_path", "")
        if last_download_path and os.path.isdir(last_download_path):
            self.dir_label.setText(last_download_path)
        else:
            self.dir_label.setText(os.path.join(os.path.expanduser("~"), "Downloads"))

    def _toggle_audio_mode(self, checked):
        self.res_label.setVisible(not checked)
        self.res_combo.setVisible(not checked)
        self.ext_label.setVisible(not checked)
        self.ext_combo.setVisible(not checked)
        self.audio_label.setVisible(checked)
        self.audio_combo.setVisible(checked)

    def analyze_url(self):
        url = self.url_input.text().strip()
        if not url:
            QMessageBox.warning(self, "提醒", "請輸入 URL")
            return
        self.analyze_btn.setEnabled(False)
        self.status.setText("分析中...")
        self._set_thumbnail_placeholder("載入縮圖中...")

        if "playlist?list=" in url:
            QMessageBox.warning(self, "提醒", "不支援整個清單下載，請提供單一影片連結")
            self._set_thumbnail_placeholder()
            self.analyze_btn.setEnabled(True)
            self.status.setText("請提供影片連結")
            return

        analysis_url = url

        def job(target_url):
            try:
                ydl_opts = {
                    "quiet": True,
                    "skip_download": True,
                    "forcethumbnail": True,
                    "noplaylist": True,
                }
                info = YoutubeDL(ydl_opts).extract_info(target_url, download=False)
                self.info = info
                self.formats = info.get("formats", [])
                self.analyzed.emit()
            except Exception as e:
                self.err_signal.emit(f"解析失敗：{e}")
                self.thumbnail_error_signal.emit()
                self.analyze_button_signal.emit(True)

        import threading

        threading.Thread(target=job, args=(analysis_url,), daemon=True).start()

    def _on_analysis_done(self):
        # 解析可用影片畫質
        heights = sorted({f["height"] for f in self.formats if f.get("height")})
        res_list = [f"{h}p" for h in heights]
        self.res_combo.clear()
        self.res_combo.addItems(res_list)

        # 解析可用音訊格式（副檔名 + codec 顯示）
        audio_exts = []
        self.audio_map = {}  # 顯示文字 → 副檔名（ext）
        self.audio_codec_map = {}  # 顯示文字 → 音訊編碼（acodec）

        for f in self.formats:
            if f.get("vcodec") == "none" and f.get("acodec") not in ["none", None]:
                ext = f.get("ext")
                acodec = f.get("acodec")
                label = f"{ext} ({acodec})"
                if label not in audio_exts:
                    audio_exts.append(label)
                    self.audio_map[label] = ext
                    codec_map = {
                        "mp4a.40.2": "aac",
                        "mp4a.40.5": "aac",
                    }
                    self.audio_codec_map[label] = codec_map.get(acodec, acodec)

        self.audio_combo.clear()
        if audio_exts:
            self.audio_combo.addItems(audio_exts)
        else:
            self.audio_combo.addItem("m4a (aac)")
            self.audio_map = {"m4a (aac)": "m4a"}
            self.audio_codec_map = {"m4a (aac)": "aac"}

        # 顯示狀態與啟用按鈕
        self.status.setText("分析完成")
        self.analyze_btn.setEnabled(True)

        # 縮圖處理
        if self.info and self.info.get("id"):
            self._load_thumbnail(self.info["id"])
        else:
            self.thumbnail_error_signal.emit()
        self._update_add_button_state()

    def _load_thumbnail(self, video_id):
        thumbnail_url = f"http://img.youtube.com/vi/{video_id}/hqdefault.jpg"

        def download_and_set_thumbnail():
            try:
                with urllib.request.urlopen(thumbnail_url, timeout=5) as url_response:
                    image_data = url_response.read()

                if image_data:
                    self.thumbnail_loaded_signal.emit(image_data)
                else:
                    self.log_signal.emit("載入縮圖時收到空的資料", "error")
                    self.thumbnail_error_signal.emit()
            except Exception as e:
                self.log_signal.emit(f"載入縮圖失敗: {e}", "error")
                self.thumbnail_error_signal.emit()

        import threading

        threading.Thread(target=download_and_set_thumbnail, daemon=True).start()

    def _set_thumbnail_placeholder(self, text="無縮圖"):
        self.thumbnail_label.setPixmap(QPixmap())
        self.thumbnail_label.setText(text)

    def _set_thumbnail_pixmap(self, image_data):
        if not image_data:
            self._set_thumbnail_error()
            return

        qimage = QImage()
        if not qimage.loadFromData(image_data):
            self.log_signal.emit("載入縮圖失敗：無法從資料建立影像", "error")
            self._set_thumbnail_error()
            return

        pixmap = QPixmap.fromImage(qimage)
        scaled_pixmap = pixmap.scaled(
            self.thumbnail_label.size(),
            Qt.KeepAspectRatio,
            Qt.SmoothTransformation,
        )
        self.thumbnail_label.setPixmap(scaled_pixmap)
        self.thumbnail_label.setText("")

    def _set_thumbnail_error(self):
        self._set_thumbnail_placeholder("載入縮圖失敗")

    def add_current_to_queue(self):
        url = self.url_input.text().strip()
        if not self.info or not url:
            QMessageBox.warning(self, "提醒", "請先分析影片並確保 URL 已填寫")
            return

        title = self.info.get("title", "No title")
        video_id = self.info.get("id")

        item_data = {
            "url": url,
            "title": title,
            "video_id": video_id,
        }

        if self.audio_only.isChecked():
            audio_label = self.audio_combo.currentText()
            audio_format = self.audio_map.get(audio_label, "m4a")
            acodec_format = self.audio_codec_map.get(audio_label, "aac")

            queue_key = f"{video_id}|audio|{audio_format}"
            display_text = f"{title} | 僅音訊 ({audio_format})"
            item_data["is_audio_only"] = True
            item_data["format_param"] = acodec_format
            item_data["ext_param"] = audio_format
            item_data["queue_key"] = queue_key
        else:
            resolution = self.res_combo.currentText()
            container_format = self.ext_combo.currentText()
            if resolution:
                format_param = resolution.replace("p", "")
                queue_key = f"{video_id}|{resolution}|{container_format}"
                display_resolution = resolution
            else:
                format_param = None
                display_resolution = "最佳可用"
                queue_key = f"{video_id}|best|{container_format}"
            display_text = f"{title} | {display_resolution} | {container_format}"
            item_data["is_audio_only"] = False
            item_data["format_param"] = format_param
            item_data["ext_param"] = container_format
            item_data["queue_key"] = queue_key

        if queue_key in self.queue_keys:
            self.status.setText("相同影片與參數已存在佇列")
            return

        item = QListWidgetItem(display_text)
        item.setData(Qt.UserRole, item_data)
        item.setFlags(
            item.flags()
            | Qt.ItemIsUserCheckable
            | Qt.ItemIsSelectable
            | Qt.ItemIsEnabled
        )
        self._updating_check_state += 1
        try:
            item.setCheckState(Qt.Checked)
        finally:
            self._updating_check_state -= 1

        self.queue_list.addItem(item)
        self.queue_keys.append(queue_key)
        self.status.setText("已加入佇列")
        self._update_select_all_checkbox()
        self._update_remove_button_state()

    def remove_selected_queue_items(self):
        checked_items = self._get_checked_items()
        if not checked_items:
            return

        for item in checked_items:
            row = self.queue_list.row(item)
            item_data = item.data(Qt.UserRole)

            queue_key_to_remove = None
            if item_data:
                queue_key_to_remove = item_data.get("queue_key")

            if not queue_key_to_remove and item_data:
                video_id_to_remove = item_data.get("video_id")
                if not video_id_to_remove:
                    match = re.search(
                        r"(?:v=|youtu\.be/|embed/)([A-Za-z0-9_-]+)",
                        item_data.get("url", ""),
                    )
                    if match:
                        video_id_to_remove = match.group(1)

                ext_param = item_data.get("ext_param")
                format_param = item_data.get("format_param")

                candidates = []
                if video_id_to_remove:
                    if item_data.get("is_audio_only"):
                        audio_ext = ext_param or format_param or "m4a"
                        candidates.append(f"{video_id_to_remove}|audio|{audio_ext}")
                        if format_param and format_param != audio_ext:
                            candidates.append(
                                f"{video_id_to_remove}|audio|{format_param}"
                            )
                    else:
                        container_format = ext_param or "mp4"
                        if format_param:
                            candidates.append(
                                f"{video_id_to_remove}|{format_param}p|{container_format}"
                            )
                        candidates.append(
                            f"{video_id_to_remove}|best|{container_format}"
                        )

                for candidate in candidates:
                    if candidate in self.queue_keys:
                        queue_key_to_remove = candidate
                        break

            self.queue_list.takeItem(row)
            if queue_key_to_remove and queue_key_to_remove in self.queue_keys:
                self.queue_keys.remove(queue_key_to_remove)
        self.status.setText("已移除所選項目")
        self._update_select_all_checkbox()
        self._update_remove_button_state()

    def choose_directory(self):
        initial_path = self.dir_label.text()
        if not os.path.isdir(initial_path):
            initial_path = os.path.join(os.path.expanduser("~"), "Downloads")

        new_directory = QFileDialog.getExistingDirectory(
            self, "選擇下載資料夾", initial_path
        )

        if new_directory:
            self.dir_label.setText(new_directory)
            self.settings.setValue("download_path", new_directory)
            self.log_signal.emit(f"下載資料夾已更新並儲存為: {new_directory}", "info")

    def generate_command(self):
        url = self.url_input.text().strip() or "<URL>"
        resolution_text = self.res_combo.currentText()
        res = resolution_text.replace("p", "") if resolution_text else None
        ext = self.ext_combo.currentText()
        cmd = ["yt-dlp"]
        if self.audio_only.isChecked():
            audio_label = self.audio_combo.currentText()
            audio_map = getattr(self, "audio_map", {})
            audio_codec_map = getattr(self, "audio_codec_map", {})
            container = audio_map.get(audio_label)
            codec = audio_codec_map.get(audio_label)
            if not container and audio_label:
                container = audio_label.split(" ")[0]
            if not codec and audio_label:
                codec = audio_label.split(" ")[0]
            if not container:
                container = "m4a"
            if not codec:
                codec = container

            if container == "webm" and codec == "opus":
                cmd += [
                    "-f",
                    "bestaudio[ext=webm]/bestaudio",
                ]
            else:
                valid_formats = {
                    "best",
                    "aac",
                    "flac",
                    "mp3",
                    "m4a",
                    "opus",
                    "vorbis",
                    "wav",
                    "alac",
                }
                audio_format_arg = (
                    container
                    if container in valid_formats
                    else (codec if codec in valid_formats else "best")
                )
                cmd += [
                    "-f",
                    "bestaudio",
                    "--extract-audio",
                    "--audio-format",
                    audio_format_arg,
                ]
        else:
            format_expr = (
                f"bestvideo[height<={res}]+bestaudio/best"
                if res
                else "bestvideo+bestaudio/best"
            )
            cmd += ["-f", format_expr]
            cmd += ["--merge-output-format", ext]

        ffmpeg_path = self._get_ffmpeg_path()
        ffmpeg_arg = ffmpeg_path
        if any(ch.isspace() for ch in ffmpeg_path):
            ffmpeg_arg = f'"{ffmpeg_path}"'
        cmd += ["--ffmpeg-location", ffmpeg_arg]

        outtpl = os.path.join(self.dir_label.text(), "%(title)s.%(ext)s")
        out_arg = outtpl
        if any(ch.isspace() for ch in outtpl):
            out_arg = f'"{outtpl}"'

        url_arg = url
        special_chars = ' "&|<>^'
        if url and not (url.startswith('"') and url.endswith('"')):
            if any(ch in url for ch in special_chars):
                url_arg = f'"{url}"'

        cmd += ["-o", out_arg, url_arg]
        self.cmd_text.setPlainText(" ".join(cmd))

    def handle_download_click(self):
        queued_items = self._get_checked_items()

        if not queued_items:
            QMessageBox.warning(self, "提醒", "請至少勾選一個下載項目。")
            return

        download_jobs = []
        for item in queued_items:
            item_data = item.data(Qt.UserRole)
            display_text = item.text() or ""
            if not item_data:
                fallback_name = display_text or "未命名項目"
                self.log_signal.emit(
                    f"錯誤：項目 {fallback_name} 沒有下載資料。", "error"
                )
                continue
            if not display_text:
                display_text = (
                    item_data.get("title") or item_data.get("url") or "未命名項目"
                )
            download_jobs.append(
                {
                    "display_text": display_text,
                    "data": copy.deepcopy(item_data),
                }
            )

        if not download_jobs:
            self.status.setText("選取的項目沒有可用的下載資料")
            return

        download_dir = self.dir_label.text()

        self.status.setText(f"準備下載 {len(download_jobs)} 個勾選項目...")
        self.download_btn.setEnabled(False)

        import threading

        threading.Thread(
            target=self._start_batch_download,
            args=(download_jobs, download_dir),
            daemon=True,
        ).start()

    def _sanitize_filename(self, title):
        # 清理 Windows 禁用的檔名符號
        return re.sub(r'[\\/:*?"<>|]', "_", title)

    def _start_batch_download(self, download_jobs, download_dir):
        """批次下載處理"""
        total_items = len(download_jobs)

        try:
            for i, job in enumerate(download_jobs):
                item_data = job.get("data") or {}
                display_text = (
                    job.get("display_text")
                    or item_data.get("title")
                    or item_data.get("url")
                    or "未命名項目"
                )

                url = item_data.get("url")
                if not url:
                    self.log_signal.emit(
                        f"錯誤：項目 {display_text} 缺少下載連結。", "error"
                    )
                    continue

                title_source = item_data.get("title") or os.path.basename(url)
                title = self._sanitize_filename(title_source or "未命名項目")
                is_audio = item_data.get("is_audio_only", False)
                format_param = item_data.get("format_param")
                ext_param = item_data.get("ext_param")
                out_base = os.path.join(download_dir, title)
                outtmpl = f"{out_base}.%(ext)s"

                self.status_signal.emit(f"下載中 {i+1}/{total_items}: {display_text}")
                self.log_signal.emit(f"[下載] {display_text}", "info")

                # 準備 yt-dlp 選項
                opts = {
                    "progress_hooks": [self._progress_hook],
                    "postprocessor_hooks": [self._postprocessor_hook],
                    "noplaylist": True,
                    "outtmpl": outtmpl,
                    "quiet": True,
                    "retries": 3,
                }
                opts["ffmpeg_location"] = self._get_ffmpeg_path()

                if is_audio:
                    self._setup_audio_options(opts, format_param, ext_param)
                else:
                    self._setup_video_options(opts, format_param, ext_param)

                # 捕捉實際下載路徑
                final_path = None

                def on_finish(d):
                    nonlocal final_path
                    if d.get("status") == "finished":
                        final_path = d.get("filename")
                        if final_path:
                            self.log_signal.emit(
                                f"完成: {os.path.basename(final_path)}", "success"
                            )

                opts["progress_hooks"].append(on_finish)

                # 執行下載
                try:
                    YoutubeDL(opts).download([url])
                    self._verify_download_result(
                        final_path,
                        display_text,
                        item_data,
                        out_base,
                        is_audio,
                        format_param,
                    )
                except Exception as e:
                    msg = f"下載失敗：{display_text} - {str(e)}"
                    self.log_signal.emit(msg, "error")
                    self.err_signal.emit(msg)
                    import traceback

                    self.log_signal.emit(traceback.format_exc(), "error")

                self.progress_signal.emit(0)

            self.status_signal.emit("所有下載任務完成")
            self.log_signal.emit("所有下載任務完成", "success")

        except Exception as e:
            self.status_signal.emit("批次下載發生錯誤")
            self.log_signal.emit(f"[致命錯誤] {str(e)}", "error")
            import traceback

            self.log_signal.emit(traceback.format_exc(), "error")

        finally:
            self.download_button_signal.emit(True)

    def _get_ffmpeg_path(self):
        if hasattr(sys, "_MEIPASS"):
            return os.path.join(sys._MEIPASS, "ffmpeg.exe")
        else:
            exe_path = os.path.join(
                os.path.abspath(os.path.dirname(__file__)), "ffmpeg.exe"
            )
            return exe_path if os.path.exists(exe_path) else "ffmpeg"

    def _setup_audio_options(self, opts, format_param, ext_param):
        """設定音訊下載選項"""

        # 特例：webm (opus) → 保留原始 webm，不轉檔
        if format_param == "opus" and ext_param == "webm":
            opts["format"] = "bestaudio[ext=webm]/bestaudio"
            return

        # 其他音訊格式 → 使用 FFmpegExtractAudio 轉檔
        opts["format"] = "bestaudio/best"

        valid_formats = {
            "best",
            "aac",
            "flac",
            "mp3",
            "m4a",
            "opus",
            "vorbis",
            "wav",
            "alac",
        }

        # ext_param 優先，其次 format_param
        target = ext_param or format_param or "best"
        if target not in valid_formats:
            if format_param in valid_formats:
                target = format_param
            else:
                target = "best"

        opts["postprocessors"] = [
            {
                "key": "FFmpegExtractAudio",
                "preferredcodec": target,
                "preferredquality": "0",
            }
        ]

    def _setup_video_options(self, opts, format_param, ext_param):
        """設定影片下載選項"""
        if format_param:
            opts["format"] = f"bestvideo[height<={format_param}]+bestaudio/best"
        else:
            opts["format"] = "bestvideo+bestaudio/best"
        opts["merge_output_format"] = ext_param

        if ext_param == "mp4":
            opts.setdefault("postprocessor_args", []).extend(
                [
                    "-c:v",
                    "copy",
                    "-c:a",
                    "aac",
                    "-b:a",
                    "192k",
                ]
            )

    def _verify_download_result(
        self,
        final_downloaded_path,
        display_text,
        metadata,
        out_base,
        is_audio_only,
        format_param,
    ):
        """驗證下載結果"""
        if final_downloaded_path and os.path.exists(final_downloaded_path):
            self._update_download_timestamp(final_downloaded_path)
            self.log_signal.emit(
                f"完成下載：{display_text} -> {os.path.basename(final_downloaded_path)}",
                "success",
            )
            return True

        self.log_signal.emit("未能捕獲最終檔案路徑，正在搜尋可能的輸出檔案...", "info")

        metadata = metadata or {}
        ext_param = metadata.get("ext_param")
        possible_extensions = []

        if ext_param:
            possible_extensions.append(ext_param)

        if is_audio_only and format_param:
            if format_param not in possible_extensions:
                possible_extensions.append(format_param)

        if is_audio_only:
            fallback_exts = ["m4a", "aac", "mp3", "flac", "opus", "wav", "webm"]
        else:
            fallback_exts = ["mp4", "mkv", "webm"]

        for ext in fallback_exts:
            if ext not in possible_extensions:
                possible_extensions.append(ext)

        for ext in possible_extensions:
            potential_path = f"{out_base}.{ext}"
            if os.path.exists(potential_path):
                self._update_download_timestamp(potential_path)
                self.log_signal.emit(
                    f"找到輸出檔案：{os.path.basename(potential_path)}", "success"
                )
                return True

        self.log_signal.emit(f"無法找到任何輸出檔案：{display_text}", "error")
        return False

    def _update_download_timestamp(self, path, timestamp=None):
        """強制將下載完成檔案的時間戳更新為當前系統時間。"""
        if not path:
            return
        if isinstance(path, (list, tuple)):
            for single_path in path:
                self._update_download_timestamp(single_path, timestamp)
            return
        normalized_path = os.path.abspath(path)
        if not os.path.exists(normalized_path):
            return
        ts = time.time() if timestamp is None else float(timestamp)
        try:
            os.utime(normalized_path, (ts, ts))
        except Exception:
            pass
        set_windows_creation_time(normalized_path, ts)

    def _progress_hook(self, d):
        status = d.get("status")
        if status == "downloading":
            try:
                total = d.get("total_bytes") or d.get("total_bytes_estimate") or 1
                downloaded = d.get("downloaded_bytes", 0)
                p = downloaded / total * 100
            except Exception:
                p = 0.0

            self.progress_signal.emit(int(p))
            eta = d.get("_eta_str")
            if eta:
                self.status_signal.emit(f"下載中：{p:.1f}%（約 {eta} 剩餘時間）")
            else:
                self.status_signal.emit(f"下載中：{p:.1f}%")

        elif status == "postprocessing":
            self.status_signal.emit("正在使用 FFmpeg 轉檔 / 合併…")
            self.log_queue.put(("[轉檔] 執行 FFmpeg...", "action"))

        elif status == "finished":
            info_dict = d.get("info_dict") or {}
            filename = (
                d.get("filename")
                or info_dict.get("_filename")
                or info_dict.get("filepath")
            )
            self._update_download_timestamp(filename)
            self.status_signal.emit("單一項目處理完成")
            self.log_queue.put(("[完成] 檔案已成功處理", "success"))
            self.progress_signal.emit(100)

        elif status == "error":
            self.status_signal.emit("下載失敗")
            self.log_queue.put(("[錯誤] 下載失敗", "error"))

    def _postprocessor_hook(self, d):
        if d.get("status") != "finished":
            return
        filepath = d.get("filepath")
        if not filepath:
            info_dict = d.get("info_dict") or {}
            filepath = info_dict.get("_filename") or info_dict.get("filepath")
        self._update_download_timestamp(filepath)

    def _show_error(self, msg):
        clean = re.sub(r"\x1b\[[0-9;]*m", "", msg)
        QMessageBox.critical(self, "錯誤", clean)
        self.status_signal.emit(clean)
        self.log_queue.put((clean, "error"))

    def toggle_log_output(self, checked):
        self.log_output.setVisible(checked)

    def append_log(self, text, level="info"):
        from datetime import datetime

        timestamp = datetime.now().strftime("[%H:%M:%S]")
        color = "#f0f0f0"
        if level == "error":
            color = "#ff6666"
        elif level == "progress":
            color = "#66ccff"
        elif level == "success":
            color = "#88ff88"
        elif level == "action":
            color = "#ffaa44"
        styled = f'<span style="color:{color}">{timestamp} {text}</span>'
        self.log_output.append(styled)
        self.log_output.moveCursor(QTextCursor.End)

    def _show_info(self, msg):
        QMessageBox.information(self, "提示", msg)
        self.status_signal.emit(msg)
        self.log_queue.put((msg, "info"))

    def _process_log_queue(self):
        while not self.log_queue.empty():
            try:
                line, level = self.log_queue.get()
            except Exception as e:
                self.append_log(f"[錯誤] 無法解析 log queue: {e}", "error")
                continue
            self.append_log(line, level)

    def _on_queue_item_selected(self, current_item, previous_item):
        """
        當佇列清單中的選取項目變更時呼叫此函式。
        從選取項目的資料中提取影片 ID 並顯示縮圖。
        """
        if current_item:
            item_data = current_item.data(Qt.UserRole)
            if item_data:
                video_id = item_data.get("video_id")

                if video_id:
                    self.log_signal.emit(
                        f"選取項目：{current_item.text()}，影片 ID (從 data): {video_id}",
                        "info",
                    )
                    self._load_thumbnail(video_id)
                elif "url" in item_data:
                    video_url = item_data["url"]
                    match = re.search(
                        r"(?:v=|youtu\.be/|embed/)([A-Za-z0-9_-]+)", video_url
                    )
                    if match:
                        video_id = match.group(1)
                        self.log_signal.emit(
                            f"選取項目：{current_item.text()}，影片 ID (從 URL 解析): {video_id}",
                            "info",
                        )
                        self._load_thumbnail(video_id)
                    else:
                        self.log_signal.emit(
                            f"無法從 URL 解析影片 ID: {video_url}", "error"
                        )
                        self.thumbnail_error_signal.emit()
                else:
                    self.log_signal.emit("選取項目無有效影片 ID 或 URL 資料。", "error")
                    self.thumbnail_error_signal.emit()
            else:
                self.log_signal.emit("選取項目無有效資料。", "error")
                self.thumbnail_error_signal.emit()
        else:
            self._set_thumbnail_placeholder()
        self._update_remove_button_state()

    def _sync_selected_items(self):
        checked_items = []
        for i in range(self.queue_list.count()):
            item = self.queue_list.item(i)
            if item and item.checkState() == Qt.Checked:
                checked_items.append(item)
        self._selected_items = list(checked_items)
        return checked_items

    def _get_checked_items(self):
        return list(self._sync_selected_items())

    def _on_select_all_state_changed(self, state):
        if self._updating_check_state > 0:
            return

        total_items = self.queue_list.count()
        currently_selected = len(self._selected_items)

        if total_items == 0:
            self._update_select_all_checkbox()
            self._update_remove_button_state()
            return

        if state == Qt.PartiallyChecked:
            target_state = (
                Qt.Checked if currently_selected < total_items else Qt.Unchecked
            )
        else:
            target_state = Qt.Checked if state == Qt.Checked else Qt.Unchecked

        self._updating_check_state += 1
        try:
            for i in range(total_items):
                item = self.queue_list.item(i)
                if item:
                    item.setCheckState(target_state)
        finally:
            self._updating_check_state -= 1

        self._update_select_all_checkbox()
        self._update_remove_button_state()

    def _on_queue_item_check_state_changed(self, _item):
        if self._updating_check_state > 0:
            return
        self._update_select_all_checkbox()
        self._update_remove_button_state()

    def _update_select_all_checkbox(self):
        checked_items = self._sync_selected_items()
        total = self.queue_list.count()
        checked = len(checked_items)
        self._updating_check_state += 1
        try:
            if total == 0:
                self.select_all_checkbox.setCheckState(Qt.Unchecked)
            elif checked == 0:
                self.select_all_checkbox.setCheckState(Qt.Unchecked)
            elif checked == total:
                self.select_all_checkbox.setCheckState(Qt.Checked)
            else:
                self.select_all_checkbox.setCheckState(Qt.PartiallyChecked)
            self.select_all_checkbox.setEnabled(total > 0)
        finally:
            self._updating_check_state -= 1

    def _update_add_button_state(self):
        """根據是否已分析完成與 URL 是否填寫，決定是否啟用加入佇列按鈕"""
        url_filled = bool(self.url_input.text().strip())
        self.add_btn.setEnabled(bool(self.info) and url_filled)

    def _update_remove_button_state(self):
        """根據當前勾選項目決定移除按鈕狀態"""
        checked_items = self._sync_selected_items()
        self.remove_btn.setEnabled(len(checked_items) > 0)


if __name__ == "__main__":
    sys.excepthook = _global_excepthook
    QApplication.setAttribute(Qt.AA_EnableHighDpiScaling, True)
    app = QApplication(sys.argv)
    app.setStyleSheet(dark_qss)
    win = YTMediaDownloader()
    win.show()
    sys.exit(app.exec_())
