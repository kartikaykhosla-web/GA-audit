import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import parse_qs, urlparse

from selenium import webdriver
from selenium.common.exceptions import TimeoutException, WebDriverException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.common.by import By


DEFAULT_URL = (
    "https://www.jagran.com/uttar-pradesh/"
    "hardoi-pm-modi-inaugurates-ganga-expressway-in-hardoi-slams-sp-40222463.html"
)

PRELOAD_SCRIPT = r"""
(function () {
  try {
    if (window.__videoMvpInstalled) return;
    window.__videoMvpInstalled = true;

    var state = window.__videoMvpState = window.__videoMvpState || {
      dataLayerPushes: [],
      gtagCalls: [],
      transportHits: []
    };

    function trim(list) {
      if (list.length > 60) {
        list.splice(0, list.length - 60);
      }
    }

    function safeClone(value, depth) {
      depth = depth || 0;
      if (depth > 2) return "[MaxDepth]";
      if (value === null || value === undefined) return value;
      var type = typeof value;
      if (type === "string" || type === "number" || type === "boolean") return value;
      if (type === "function") return "[Function]";
      if (Array.isArray(value)) {
        return value.slice(0, 20).map(function (entry) {
          return safeClone(entry, depth + 1);
        });
      }
      if (typeof FormData !== "undefined" && value instanceof FormData) {
        var pairs = [];
        value.forEach(function (entryValue, entryKey) {
          pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
        });
        return pairs.join("&");
      }
      if (typeof URLSearchParams !== "undefined" && value instanceof URLSearchParams) {
        return value.toString();
      }
      if (typeof Blob !== "undefined" && value instanceof Blob) {
        return "[Blob size=" + value.size + "]";
      }
      if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
        return "[ArrayBuffer byteLength=" + value.byteLength + "]";
      }
      if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView && ArrayBuffer.isView(value)) {
        return "[TypedArray byteLength=" + value.byteLength + "]";
      }
      if (type === "object") {
        var output = {};
        Object.keys(value).slice(0, 60).forEach(function (key) {
          try {
            output[key] = safeClone(value[key], depth + 1);
          } catch (e) {}
        });
        return output;
      }
      return String(value);
    }

    function push(target, payload) {
      try {
        state[target].push(Object.assign({ timestamp: Date.now() }, payload));
        trim(state[target]);
      } catch (e) {}
    }

    function isInterestingUrl(url) {
      if (typeof url !== "string") return false;
      return (
        url.indexOf("google-analytics.com") !== -1 ||
        url.indexOf("/g/collect") !== -1 ||
        url.indexOf("/mp/collect") !== -1 ||
        url.indexOf("/collect") !== -1
      );
    }

    function asText(data) {
      try {
        if (data === null || data === undefined) return "";
        if (typeof data === "string") return data;
        if (typeof URLSearchParams !== "undefined" && data instanceof URLSearchParams) return data.toString();
        if (typeof FormData !== "undefined" && data instanceof FormData) {
          var pairs = [];
          data.forEach(function (entryValue, entryKey) {
            pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
          });
          return pairs.join("&");
        }
        return String(data);
      } catch (e) {
        return "[unserializable]";
      }
    }

    function recordTransport(api, url, method, body) {
      try {
        if (!isInterestingUrl(url)) return;
        push("transportHits", {
          api: api,
          url: String(url || ""),
          method: String(method || "GET").toUpperCase(),
          bodyText: asText(body)
        });
      } catch (e) {}
    }

    function wrapDataLayer(list) {
      if (!list) list = [];
      if (list.__videoMvpWrappedPush) return list;
      var originalPush = typeof list.push === "function" ? list.push : Array.prototype.push;
      Object.defineProperty(list, "__videoMvpWrappedPush", {
        value: true,
        configurable: true
      });
      list.push = function () {
        var args = Array.prototype.slice.call(arguments);
        push("dataLayerPushes", {
          entry: safeClone(args[0], 0),
          event: args[0] && args[0].event ? args[0].event : ""
        });
        return originalPush.apply(this, arguments);
      };
      return list;
    }

    var currentDataLayer = wrapDataLayer(window.dataLayer || []);
    Object.defineProperty(window, "dataLayer", {
      configurable: true,
      enumerable: true,
      get: function () {
        return currentDataLayer;
      },
      set: function (value) {
        currentDataLayer = wrapDataLayer(value || []);
      }
    });
    window.dataLayer = currentDataLayer;

    function wrapGtag(original) {
      if (original && original.__videoMvpWrapped) return original;
      var wrapped = function () {
        var args = Array.prototype.slice.call(arguments);
        push("gtagCalls", {
          command: args[0],
          event_name: args[0] === "event" ? args[1] : "",
          params: args[0] === "event" && args[2] && typeof args[2] === "object"
            ? safeClone(args[2], 0)
            : null
        });
        if (typeof original === "function") {
          return original.apply(this, arguments);
        }
      };
      Object.defineProperty(wrapped, "__videoMvpWrapped", {
        value: true,
        configurable: true
      });
      return wrapped;
    }

    var currentGtag = typeof window.gtag === "function" ? wrapGtag(window.gtag) : undefined;
    Object.defineProperty(window, "gtag", {
      configurable: true,
      enumerable: true,
      get: function () {
        return currentGtag;
      },
      set: function (value) {
        currentGtag = typeof value === "function" ? wrapGtag(value) : value;
      }
    });
    if (currentGtag) {
      window.gtag = currentGtag;
    }

    if (navigator && typeof navigator.sendBeacon === "function" && !navigator.sendBeacon.__videoMvpWrapped) {
      var originalSendBeacon = navigator.sendBeacon.bind(navigator);
      var wrappedSendBeacon = function (url, data) {
        recordTransport("sendBeacon", url, "POST", data);
        return originalSendBeacon(url, data);
      };
      wrappedSendBeacon.__videoMvpWrapped = true;
      navigator.sendBeacon = wrappedSendBeacon;
    }

    if (typeof window.fetch === "function" && !window.fetch.__videoMvpWrapped) {
      var originalFetch = window.fetch.bind(window);
      var wrappedFetch = function (input, init) {
        var url = typeof input === "string" ? input : (input && input.url) || "";
        var method = (init && init.method) || (input && input.method) || "GET";
        var body = (init && init.body) || null;
        recordTransport("fetch", url, method, body);
        return originalFetch(input, init);
      };
      wrappedFetch.__videoMvpWrapped = true;
      window.fetch = wrappedFetch;
    }

    if (typeof XMLHttpRequest !== "undefined" && XMLHttpRequest.prototype && !XMLHttpRequest.prototype.__videoMvpWrapped) {
      var originalOpen = XMLHttpRequest.prototype.open;
      var originalSend = XMLHttpRequest.prototype.send;
      XMLHttpRequest.prototype.open = function (method, url) {
        try {
          this.__videoMvpUrl = url || "";
          this.__videoMvpMethod = method || "GET";
        } catch (e) {}
        return originalOpen.apply(this, arguments);
      };
      XMLHttpRequest.prototype.send = function (body) {
        try {
          recordTransport("xhr", this.__videoMvpUrl || "", this.__videoMvpMethod || "GET", body);
        } catch (e) {}
        return originalSend.apply(this, arguments);
      };
      Object.defineProperty(XMLHttpRequest.prototype, "__videoMvpWrapped", {
        value: true,
        configurable: true
      });
    }
  } catch (e) {}
})();
"""


LIGHTWEIGHT_CONSENT_SELECTORS = [
    "#onetrust-accept-btn-handler",
    ".onetrust-accept-btn-handler",
    "#CybotCookiebotDialogBodyLevelButtonLevelOptinAllowAll",
    "#didomi-notice-agree-button",
    "[id*='didomi-notice-agree-button']",
    "[data-testid*='accept']",
    "[aria-label*='Accept']",
]


ARTICLE_OPEN_SELECTORS = [
    ".Short_wrapper_fixed img[alt='video thumbnail']",
    ".Short_wrapper_fixed img[src*='thumbnail' i]",
    ".Short_wrapper_fixed i.videoImage",
    ".Short_wrapper_fixed [class*='play' i]",
    ".Short_wrapper_fixed [role='button']",
    ".ArticleDetail_relatedvideo__wvgRP img",
    ".ArticleDetail_relatedvideo__wvgRP .article",
    ".ArticleDetail_relatedvideo__wvgRP i.videoImage",
    ".ArticleDetail_relatedvideo__wvgRP [class*='play' i]",
    ".ArticleDetail_relatedvideo__wvgRP [role='button']",
    ".ArticleDetail_relatedvideo__wvgRP media-theme-sutro",
    ".ArticleDetail_relatedvideo__wvgRP youtube-video",
    ".ArticleDetail_relatedvideo__wvgRP .video-player-container",
    ".relatedvideo media-theme-sutro",
    ".relatedvideo youtube-video",
    ".relatedvideo .video-player-container",
    ".relatedvideo img",
    ".relatedvideo .article",
    ".relatedvideo a",
    "img[alt='video thumbnail']",
]

PRIMARY_ARTICLE_OPEN_SELECTORS = [
    ".Short_wrapper_fixed img[alt='video thumbnail']",
    ".Short_wrapper_fixed img[src*='thumbnail' i]",
    ".Short_wrapper_fixed i.videoImage",
    ".Short_wrapper_fixed [class*='play' i]",
    ".Short_wrapper_fixed [role='button']",
    "img[alt='video thumbnail']",
]


PLAY_CONTROL_SELECTORS = [
    ".ArticleDetail_relatedvideo__wvgRP media-theme-sutro",
    ".ArticleDetail_relatedvideo__wvgRP youtube-video",
    ".ArticleDetail_relatedvideo__wvgRP .video-player-container",
    ".relatedvideo media-theme-sutro",
    ".relatedvideo youtube-video",
    ".relatedvideo .video-player-container",
    ".video-player-container [aria-label*='play' i]",
    ".VideoSwiper_videoContainer [aria-label*='play' i]",
    ".video-player-container [class*='play' i]",
    ".VideoSwiper_videoContainer [class*='play' i]",
    ".video-player-container [role='button']",
    ".VideoSwiper_videoContainer [role='button']",
    ".video-player-container button",
    ".VideoSwiper_videoContainer button",
]

PRIMARY_PLAY_CONTROL_SELECTORS = [
    ".video-player-container [aria-label*='play' i]",
    ".VideoSwiper_videoContainer [aria-label*='play' i]",
    ".video-player-container [class*='play' i]",
    ".VideoSwiper_videoContainer [class*='play' i]",
    ".video-player-container [role='button']",
    ".VideoSwiper_videoContainer [role='button']",
    ".video-player-container button",
    ".VideoSwiper_videoContainer button",
]


RELATED_VIDEO_SELECTORS = [
    ".ArticleDetail_relatedvideo__wvgRP media-theme-sutro",
    ".ArticleDetail_relatedvideo__wvgRP youtube-video",
    ".ArticleDetail_relatedvideo__wvgRP .video-player-container",
    ".ArticleDetail_relatedvideo__wvgRP",
    ".relatedvideo media-theme-sutro",
    ".relatedvideo youtube-video",
    ".relatedvideo .video-player-container",
    ".relatedvideo",
]

PRIMARY_DETECT_SELECTORS = [
    ".Short_wrapper_fixed img[alt='video thumbnail']",
    ".Short_wrapper_fixed i.videoImage",
    ".Short_wrapper_fixed [class*='play' i]",
    ".Short_wrapper_fixed [role='button']",
    ".VideoSwiper_videoContainer",
]


def resolve_chrome_paths() -> Tuple[str, str]:
    binary_candidates = [
        os.environ.get("CHROME_BINARY"),
        "/usr/bin/chromium",
        "/usr/bin/chromium-browser",
        "/usr/bin/google-chrome",
        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    ]
    driver_candidates = [
        os.environ.get("CHROMEDRIVER_PATH"),
        shutil.which("chromedriver"),
        "/usr/bin/chromedriver",
    ]

    chrome_binary = next((item for item in binary_candidates if item and os.path.exists(item)), "")
    chromedriver = next((item for item in driver_candidates if item and os.path.exists(item)), "")
    return chrome_binary, chromedriver


def _major_version(version_text: str) -> str:
    match = re.search(r"\b(\d+)\.", version_text or "")
    return match.group(1) if match else ""


def _command_output(args: List[str]) -> str:
    try:
        completed = subprocess.run(args, capture_output=True, text=True, timeout=5)
        return f"{completed.stdout or ''} {completed.stderr or ''}".strip()
    except Exception:
        return ""


def _path_without_incompatible_chromedriver(chrome_binary: str, chromedriver: str) -> Optional[str]:
    if not chrome_binary or not chromedriver:
        return None

    chrome_major = _major_version(_command_output([chrome_binary, "--version"]))
    driver_major = _major_version(_command_output([chromedriver, "--version"]))
    if not chrome_major or not driver_major or chrome_major == driver_major:
        return None

    driver_dir = os.path.dirname(os.path.abspath(chromedriver))
    path_parts = os.environ.get("PATH", "").split(os.pathsep)
    filtered_parts = [
        part for part in path_parts
        if os.path.abspath(part or ".") != driver_dir
    ]
    return os.pathsep.join(filtered_parts)


def create_driver(headless: bool) -> webdriver.Chrome:
    chrome_binary, chromedriver = resolve_chrome_paths()
    options = Options()
    if headless:
        options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--window-size=1440,2200")
    options.add_argument("--autoplay-policy=no-user-gesture-required")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_argument("--disable-background-timer-throttling")
    options.add_argument("--disable-backgrounding-occluded-windows")
    options.add_argument("--disable-renderer-backgrounding")
    options.add_argument("--mute-audio")
    if chrome_binary:
        options.binary_location = chrome_binary

    explicit_driver = os.environ.get("CHROMEDRIVER_PATH")
    service = Service(executable_path=explicit_driver) if explicit_driver and os.path.exists(explicit_driver) else None
    original_path = os.environ.get("PATH", "")
    fallback_path = _path_without_incompatible_chromedriver(chrome_binary, chromedriver)
    try:
        if fallback_path is not None and not service:
            os.environ["PATH"] = fallback_path
        driver = webdriver.Chrome(options=options, service=service) if service else webdriver.Chrome(options=options)
    except WebDriverException as exc:
        message = str(exc)
        if service and (
            "only supports Chrome version" in message
            or "session not created" in message.lower()
        ):
            if fallback_path is not None:
                os.environ["PATH"] = fallback_path
            driver = webdriver.Chrome(options=options)
        else:
            raise
    finally:
        os.environ["PATH"] = original_path
    driver.set_page_load_timeout(20)
    driver.set_script_timeout(5)
    try:
        driver.execute_cdp_cmd("Page.addScriptToEvaluateOnNewDocument", {"source": PRELOAD_SCRIPT})
        driver.execute_cdp_cmd("Network.enable", {})
    except Exception:
        pass
    return driver


def safe_quit(driver: Optional[webdriver.Chrome]) -> None:
    if not driver:
        return
    try:
        driver.quit()
    except Exception:
        pass


def native_click(driver: webdriver.Chrome, element) -> bool:
    if not element:
        return False
    try:
        driver.execute_script("arguments[0].scrollIntoView({block:'center', inline:'center'});", element)
    except Exception:
        pass
    try:
        ActionChains(driver).move_to_element(element).pause(0.08).click().perform()
        return True
    except Exception:
        pass
    try:
        element.click()
        return True
    except Exception:
        return False


def click_first_visible(driver: webdriver.Chrome, selectors: List[str]) -> bool:
    for selector in selectors:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:5]:
            try:
                if not element.is_displayed():
                    continue
                if native_click(driver, element):
                    return True
            except Exception:
                continue
    return False


def click_related_video_embed(driver: webdriver.Chrome) -> bool:
    try:
        clicked = driver.execute_script(
            """
            const selectors = arguments[0];
            const visible = (element) => {
              if (!element) return false;
              const rect = element.getBoundingClientRect();
              return !!(rect.width && rect.height);
            };
            for (const selector of selectors) {
              const elements = Array.from(document.querySelectorAll(selector));
              for (const element of elements) {
                if (!visible(element)) continue;
                try {
                  element.scrollIntoView({ block: "center", inline: "center" });
                } catch (e) {}
                const targets = [
                  element.shadowRoot && element.shadowRoot.querySelector("button, [role='button'], video, iframe"),
                  element.querySelector && element.querySelector("button, [role='button'], video, iframe"),
                  element
                ].filter(Boolean);
                for (const target of targets) {
                  try {
                    target.click();
                    return true;
                  } catch (e) {}
                }
              }
            }
            return false;
            """,
            RELATED_VIDEO_SELECTORS,
        )
        if clicked:
            time.sleep(0.2)
            return True
    except Exception:
        pass
    return click_first_visible(driver, RELATED_VIDEO_SELECTORS)


def has_primary_video_target(driver: webdriver.Chrome) -> bool:
    try:
        return bool(
            driver.execute_script(
                """
                const selectors = arguments[0];
                const visible = (element) => {
                  if (!element) return false;
                  const rect = element.getBoundingClientRect();
                  return !!(rect.width && rect.height);
                };
                for (const selector of selectors) {
                  for (const element of Array.from(document.querySelectorAll(selector))) {
                    if (visible(element)) return true;
                  }
                }
                for (const video of Array.from(document.querySelectorAll("video"))) {
                  const src = String(video.currentSrc || video.src || "");
                  if (src.includes("vdo.ai") || src.includes("h5.vdo.ai")) continue;
                  if (visible(video)) return true;
                }
                return false;
                """,
                PRIMARY_DETECT_SELECTORS,
            )
        )
    except Exception:
        return False


def scroll_to_related_video_embed(driver: webdriver.Chrome) -> bool:
    try:
        for _ in range(8):
            found = driver.execute_script(
                """
                const selectors = arguments[0];
                for (const selector of selectors) {
                  const element = document.querySelector(selector);
                  if (!element) continue;
                  try {
                    element.scrollIntoView({ block: "center", inline: "center" });
                  } catch (e) {}
                  return true;
                }
                window.scrollBy(0, Math.max(600, Number(window.innerHeight || 0) * 0.75));
                return false;
                """,
                RELATED_VIDEO_SELECTORS,
            )
            time.sleep(0.45)
            if found:
                return True
    except Exception:
        return False
    return False


def accept_common_consent(driver: webdriver.Chrome) -> List[str]:
    clicked = []
    for selector in LIGHTWEIGHT_CONSENT_SELECTORS:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:2]:
            try:
                if not element.is_displayed():
                    continue
                driver.execute_script("arguments[0].click();", element)
                clicked.append(selector)
                time.sleep(0.15)
                return clicked
            except Exception:
                continue
    return clicked


def reset_visible_videos(driver: webdriver.Chrome) -> None:
    try:
        driver.execute_script(
            """
            document.querySelectorAll("video").forEach((video) => {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) return;
              try {
                video.pause();
                video.currentTime = 0;
              } catch (e) {}
            });
            """
        )
    except Exception:
        pass


def capture_primary_video_state(driver: webdriver.Chrome) -> Dict[str, Any]:
    try:
        return driver.execute_script(
            """
            const relatedEmbed = document.querySelector(
              ".ArticleDetail_relatedvideo__wvgRP youtube-video, .relatedvideo youtube-video, " +
              ".ArticleDetail_relatedvideo__wvgRP media-theme-sutro, .relatedvideo media-theme-sutro"
            );
            if (relatedEmbed) {
              const rect = relatedEmbed.getBoundingClientRect();
              if (rect.width && rect.height && rect.top >= -20 && rect.top <= window.innerHeight + 20) {
                return {
                  embed: true,
                  visible: true,
                  width: Number(rect.width || 0),
                  height: Number(rect.height || 0),
                  top: Number(rect.top || 0),
                  src: String(relatedEmbed.getAttribute("src") || "")
                };
              }
            }
            const videos = Array.from(document.querySelectorAll("video"));
            for (const video of videos) {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) continue;
              const src = String(video.currentSrc || video.src || "");
              if (src.includes("vdo.ai") || src.includes("h5.vdo.ai")) continue;
              return {
                paused: !!video.paused,
                muted: !!video.muted,
                currentTime: Number(video.currentTime || 0),
                duration: Number(video.duration || 0),
                readyState: Number(video.readyState || 0),
                width: Number(rect.width || 0),
                height: Number(rect.height || 0),
                top: Number(rect.top || 0),
                src: src
              };
            }
            if (relatedEmbed) {
              const rect = relatedEmbed.getBoundingClientRect();
              return {
                embed: true,
                visible: !!(rect.width && rect.height),
                width: Number(rect.width || 0),
                height: Number(rect.height || 0),
                top: Number(rect.top || 0),
                src: String(relatedEmbed.getAttribute("src") || "")
              };
            }
            return {};
            """
        ) or {}
    except Exception as exc:
        return {"error": str(exc)}


def extract_state(driver: webdriver.Chrome) -> Dict[str, Any]:
    try:
        return driver.execute_script(
            """
            return window.__videoMvpState ? JSON.parse(JSON.stringify(window.__videoMvpState)) : {};
            """
        ) or {}
    except Exception:
        return {}


def decode_collect(url: str, body_text: str = "") -> List[Dict[str, Any]]:
    parsed = urlparse(url)
    payloads: List[Dict[str, Any]] = []
    query_payload = {key: values[-1] if values else "" for key, values in parse_qs(parsed.query, keep_blank_values=True).items()}
    body_text = (body_text or "").strip()
    if not body_text:
        payloads = [query_payload]
    elif "=" in body_text:
        body_payload = {key: values[-1] if values else "" for key, values in parse_qs(body_text, keep_blank_values=True).items()}
        payloads = [{**query_payload, **body_payload}]
    else:
        payloads = [{**query_payload, "_body_text": body_text}]

    events = []
    for payload in payloads:
        params = {}
        for key, value in payload.items():
            if key.startswith(("ep.", "epn.", "epf.")):
                params[key.split(".", 1)[1]] = value
        for raw_key, clean_key in {
            "dl": "page_location",
            "dt": "page_title",
            "dr": "page_referrer",
            "en": "event_name",
        }.items():
            if raw_key in payload and clean_key not in params:
                params[clean_key] = payload[raw_key]
        event_name = str(payload.get("en") or payload.get("event_name") or "")
        events.append({"event_name": event_name, "params": params, "raw_fields": payload})
    return [event for event in events if event.get("event_name")]


def normalize_video_events(state: Dict[str, Any]) -> Dict[str, Any]:
    gtag_calls = state.get("gtagCalls", []) or []
    data_layer_pushes = state.get("dataLayerPushes", []) or []
    transport_hits = state.get("transportHits", []) or []

    gtag_video = [
        call for call in gtag_calls
        if isinstance(call, dict) and str(call.get("event_name") or "").strip().lower() == "video_interaction"
    ]

    data_layer_video = []
    for push_entry in data_layer_pushes:
        if not isinstance(push_entry, dict):
            continue
        entry = push_entry.get("entry")
        if isinstance(entry, dict) and str(entry.get("event") or "").strip().lower() == "video_interaction":
            data_layer_video.append(entry)
            continue
        if isinstance(entry, list) and len(entry) >= 2 and str(entry[0]).strip().lower() == "event" and str(entry[1]).strip().lower() == "video_interaction":
            data_layer_video.append({"event": entry[1], **(entry[2] if len(entry) > 2 and isinstance(entry[2], dict) else {})})

    transport_video = []
    for hit in transport_hits:
        if not isinstance(hit, dict):
            continue
        for event in decode_collect(str(hit.get("url") or ""), str(hit.get("bodyText") or "")):
            if str(event.get("event_name") or "").strip().lower() == "video_interaction":
                transport_video.append({"transport": hit.get("api"), **event})

    for event in [*gtag_video, *data_layer_video, *transport_video]:
        if not isinstance(event, dict):
            continue
        params = event.get("params") if isinstance(event.get("params"), dict) else event
        embed_type = str(params.get("dynamic_video_embed_type") or event.get("dynamic_video_embed_type") or "").strip().lower()
        section_name = str(params.get("section_name") or event.get("section_name") or "").strip().lower()
        normalized_embed_type = ""
        if embed_type in {"in house video", "in-house video"} or section_name == "featured video":
            normalized_embed_type = "in-house video"
        elif embed_type == "view this video also" or section_name == "view this video also":
            normalized_embed_type = "view this video also"
        if normalized_embed_type:
            params["dynamic_video_embed_type"] = normalized_embed_type
            event["dynamic_video_embed_type"] = normalized_embed_type

    return {
        "gtag_video_events": gtag_video,
        "data_layer_video_events": data_layer_video,
        "transport_video_events": transport_video,
        "raw_state": state,
    }


def normalized_has_field(normalized: Dict[str, Any], field_name: str) -> bool:
    for event in normalized.get("gtag_video_events") or []:
        params = event.get("params") if isinstance(event, dict) else {}
        if isinstance(params, dict) and params.get(field_name):
            return True
        if isinstance(event, dict) and event.get(field_name):
            return True
    for event in normalized.get("data_layer_video_events") or []:
        if isinstance(event, dict) and event.get(field_name):
            return True
    for event in normalized.get("transport_video_events") or []:
        params = event.get("params") if isinstance(event, dict) else {}
        if isinstance(params, dict) and params.get(field_name):
            return True
        if isinstance(event, dict) and event.get(field_name):
            return True
    return False


def normalized_has_video_percent_milestone(normalized: Dict[str, Any]) -> bool:
    values = []
    for event in normalized.get("gtag_video_events") or []:
        if not isinstance(event, dict):
            continue
        params = event.get("params") if isinstance(event.get("params"), dict) else {}
        values.append(params.get("video_percent") or event.get("video_percent"))
    for event in normalized.get("data_layer_video_events") or []:
        if isinstance(event, dict):
            values.append(event.get("video_percent"))
    for event in normalized.get("transport_video_events") or []:
        if not isinstance(event, dict):
            continue
        params = event.get("params") if isinstance(event.get("params"), dict) else {}
        values.append(params.get("video_percent") or event.get("video_percent"))

    for value in values:
        text = str(value or "").strip()
        if not text:
            continue
        match = re.search(r"\d+(?:\.\d+)?", text)
        if match and float(match.group(0)) >= 25:
            return True
    return False


def capture_video_event(url: str, headless: bool, prefer_related_embed: Optional[bool] = None) -> Dict[str, Any]:
    driver = None
    debug_steps: List[Dict[str, Any]] = []
    try:
        driver = create_driver(headless=headless)

        print("Loading page...")
        driver.get(url)
        debug_steps.append({"step": "driver.get", "success": True})

        consent_actions = accept_common_consent(driver)
        debug_steps.append({"step": "accept_common_consent", "actions": consent_actions})

        try:
            driver.execute_script(
                """
                try {
                    if (typeof gtag === "function") {
                        gtag('consent', 'update', {
                            analytics_storage: 'granted',
                            ad_storage: 'granted',
                            ad_user_data: 'granted',
                            ad_personalization: 'granted'
                        });
                    }
                } catch (e) {}
                """
            )
        except Exception:
            pass

        time.sleep(1.0)
        auto_target = prefer_related_embed is None
        primary_target_found = has_primary_video_target(driver)
        if prefer_related_embed is None:
            prefer_related_embed = not primary_target_found
        debug_steps.append(
            {
                "step": "select_video_target",
                "primary_target_found": primary_target_found,
                "target": "related_embed" if prefer_related_embed else "primary_video",
            }
        )

        if prefer_related_embed:
            related_found = scroll_to_related_video_embed(driver)
            debug_steps.append({"step": "scroll_to_related_video_embed", "success": related_found})
            time.sleep(0.4)

        print("Opening video UI...")
        if prefer_related_embed:
            clicked_initial = click_related_video_embed(driver)
            if not clicked_initial:
                clicked_initial = click_first_visible(driver, ARTICLE_OPEN_SELECTORS)
        else:
            clicked_initial = click_first_visible(driver, ARTICLE_OPEN_SELECTORS)
            if not clicked_initial:
                clicked_initial = click_related_video_embed(driver)
        time.sleep(0.8)
        if prefer_related_embed:
            clicked_control = click_related_video_embed(driver)
            if not clicked_control:
                clicked_control = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
        else:
            clicked_control = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
            if not clicked_control:
                clicked_control = click_related_video_embed(driver)
        time.sleep(0.8)

        reset_visible_videos(driver)
        time.sleep(0.3)

        # Try again after reset so we get a manual-ish start from 0.
        if prefer_related_embed:
            clicked_control_after_reset = click_related_video_embed(driver)
            if not clicked_control_after_reset:
                clicked_control_after_reset = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
        else:
            clicked_control_after_reset = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
            if not clicked_control_after_reset:
                clicked_control_after_reset = click_related_video_embed(driver)
        if not clicked_control_after_reset:
            try:
                driver.execute_script(
                    """
                    const video = Array.from(document.querySelectorAll("video")).find((candidate) => {
                        const src = String(candidate.currentSrc || candidate.src || "");
                        return !src.includes("vdo.ai") && !src.includes("h5.vdo.ai");
                    });
                    if (video) {
                        video.muted = false;
                        video.defaultMuted = false;
                        const p = video.play();
                        if (p && typeof p.catch === "function") p.catch(() => {});
                    }
                    """
                )
            except Exception:
                pass

        debug_steps.append(
            {
                "step": "video_probe",
                "clicked_initial": clicked_initial,
                "clicked_control": clicked_control,
                "clicked_control_after_reset": clicked_control_after_reset,
            }
        )

        start = time.time()
        matched = None
        first_match_at = None
        latest_state = {}
        latest_video_state = {}
        any_click = clicked_initial or clicked_control or clicked_control_after_reset
        poll_seconds = 20 if any_click else 2
        while time.time() - start < poll_seconds:
            latest_state = extract_state(driver)
            normalized = normalize_video_events(latest_state)
            latest_video_state = capture_primary_video_state(driver)
            if normalized["gtag_video_events"] or normalized["data_layer_video_events"] or normalized["transport_video_events"]:
                matched = normalized
                if first_match_at is None:
                    first_match_at = time.time()
                if (
                    normalized_has_field(normalized, "dynamic_video_embed_type")
                    and normalized_has_video_percent_milestone(normalized)
                ) or time.time() - first_match_at >= 10:
                    break
            time.sleep(1.0)

        if matched is None and auto_target and not prefer_related_embed:
            debug_steps.append({"step": "fallback_to_related_embed", "reason": "primary_video_no_event"})
            related_found = scroll_to_related_video_embed(driver)
            debug_steps.append({"step": "scroll_to_related_video_embed", "success": related_found})
            time.sleep(0.4)

            clicked_initial = click_related_video_embed(driver)
            time.sleep(0.8)
            clicked_control = click_related_video_embed(driver)
            time.sleep(0.8)
            reset_visible_videos(driver)
            time.sleep(0.3)
            clicked_control_after_reset = click_related_video_embed(driver)
            debug_steps.append(
                {
                    "step": "fallback_video_probe",
                    "clicked_initial": clicked_initial,
                    "clicked_control": clicked_control,
                    "clicked_control_after_reset": clicked_control_after_reset,
                }
            )

            start = time.time()
            first_match_at = None
            while time.time() - start < 15:
                latest_state = extract_state(driver)
                normalized = normalize_video_events(latest_state)
                latest_video_state = capture_primary_video_state(driver)
                if normalized["gtag_video_events"] or normalized["data_layer_video_events"] or normalized["transport_video_events"]:
                    matched = normalized
                    if first_match_at is None:
                        first_match_at = time.time()
                    if (
                        normalized_has_field(normalized, "dynamic_video_embed_type")
                        and normalized_has_video_percent_milestone(normalized)
                    ) or time.time() - first_match_at >= 10:
                        break
                time.sleep(1.0)

        if matched is None:
            matched = normalize_video_events(latest_state)

        result = {
            "url": url,
            "debug_steps": debug_steps,
            "video_state": latest_video_state,
            "matched": {
                "gtag_video_events": matched["gtag_video_events"],
                "data_layer_video_events": matched["data_layer_video_events"],
                "transport_video_events": matched["transport_video_events"],
            },
            "counts": {
                "gtag_calls": len((matched["raw_state"].get("gtagCalls") or [])),
                "data_layer_pushes": len((matched["raw_state"].get("dataLayerPushes") or [])),
                "transport_hits": len((matched["raw_state"].get("transportHits") or [])),
            },
        }
        return result

    except TimeoutException as exc:
        return {"error": f"Timeout: {exc}", "url": url, "debug_steps": debug_steps}
    except Exception as exc:
        return {"error": str(exc), "url": url, "debug_steps": debug_steps}
    finally:
        safe_quit(driver)


def run_capture(url: str, headless: bool, output_path: Optional[str], prefer_related_embed: Optional[bool] = None) -> int:
    result = capture_video_event(url=url, headless=headless, prefer_related_embed=prefer_related_embed)
    text = json.dumps(result, ensure_ascii=False, indent=2)
    print(text)
    if output_path:
        with open(output_path, "w", encoding="utf-8") as handle:
            handle.write(text)
        print(f"\nSaved output to: {output_path}")
    return 0 if not result.get("error") else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Minimal local probe for Jagran video_interaction capture.")
    parser.add_argument("--url", default=DEFAULT_URL, help="Article URL to probe")
    parser.add_argument("--headless", action="store_true", help="Run Chrome headless")
    parser.add_argument("--prefer-related-embed", action="store_true", help="Target the end-of-page related video embed")
    parser.add_argument("--output", default="", help="Optional JSON output file path")
    args = parser.parse_args()
    return run_capture(
        args.url,
        headless=args.headless,
        output_path=args.output or None,
        prefer_related_embed=True if args.prefer_related_embed else None,
    )


def event_rows(source: str, events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for index, event in enumerate(events or [], start=1):
        for key, value in sorted((event or {}).items()):
            rows.append(
                {
                    "source": source,
                    "event_index": index,
                    "field": key,
                    "value": json.dumps(value, ensure_ascii=False) if isinstance(value, (dict, list)) else str(value),
                }
            )
    return rows


def build_event_value_table(result: Dict[str, Any]):
    import pandas as pd

    matched = result.get("matched") or {}
    rows: List[Dict[str, Any]] = []
    rows.extend(event_rows("gtag", matched.get("gtag_video_events") or []))
    rows.extend(event_rows("dataLayer", matched.get("data_layer_video_events") or []))
    rows.extend(event_rows("transport", matched.get("transport_video_events") or []))
    return pd.DataFrame(rows)


def render_error(st_module, message: str) -> None:
    chrome_match = re.search(r"Current browser version is ([^\\s;]+)", message or "")
    driver_match = re.search(r"only supports Chrome version (\\d+)", message or "")
    if chrome_match and driver_match:
        st_module.error(
            "ChromeDriver version mismatch. "
            f"Chrome is {chrome_match.group(1)}, but the detected driver only supports "
            f"Chrome {driver_match.group(1)}. The app will now ignore stale PATH drivers "
            "and let Selenium choose a matching driver."
        )
        return
    st_module.error(message)


def render_streamlit_app() -> None:
    import pandas as pd
    import streamlit as st

    st.set_page_config(page_title="Video Event MVP", layout="wide")
    st.title("Video Event MVP")
    st.caption("Minimal local probe for Jagran video_interaction capture. No template mapping, no rule checks.")

    url = st.text_input("URL", value=DEFAULT_URL)
    headless = st.checkbox("Run headless", value=False)

    if "video_mvp_result" not in st.session_state:
        st.session_state["video_mvp_result"] = None

    if st.button("Capture video event", type="primary"):
        with st.spinner("Running MVP probe..."):
            st.session_state["video_mvp_result"] = capture_video_event(url=url, headless=headless)

    result = st.session_state.get("video_mvp_result")
    if result:
        if result.get("error"):
            render_error(st, result["error"])
        else:
            counts = result.get("counts") or {}
            col1, col2, col3, col4 = st.columns(4)
            col1.metric("Gtag Calls", counts.get("gtag_calls", 0))
            col2.metric("dataLayer Pushes", counts.get("data_layer_pushes", 0))
            col3.metric("Transport Hits", counts.get("transport_hits", 0))
            matched = result.get("matched") or {}
            matched_count = sum(
                len(matched.get(key) or [])
                for key in ("gtag_video_events", "data_layer_video_events", "transport_video_events")
            )
            col4.metric("Matched Events", matched_count)

            st.subheader("Event Values")
            value_table = build_event_value_table(result)
            if value_table.empty:
                st.warning("No video_interaction event was captured.")
            else:
                st.dataframe(value_table, use_container_width=True, hide_index=True)

            st.subheader("Video State")
            video_state = result.get("video_state") or {}
            if video_state:
                state_rows = [{"field": key, "value": value} for key, value in video_state.items()]
                st.dataframe(pd.DataFrame(state_rows), use_container_width=True, hide_index=True)

            with st.expander("Debug Steps", expanded=False):
                st.json(result.get("debug_steps") or [])

            with st.expander("Raw JSON", expanded=False):
                st.json(result)


def running_in_streamlit() -> bool:
    try:
        from streamlit.runtime.scriptrunner import get_script_run_ctx

        return get_script_run_ctx() is not None
    except Exception:
        return False


if __name__ == "__main__":
    if running_in_streamlit():
        render_streamlit_app()
    else:
        sys.exit(main())
