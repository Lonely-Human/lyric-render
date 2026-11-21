'use strict';

/**
 * Create an Apple-Music-inspired vertical lyric video for a WhatsApp bot.
 * Requires: ffmpeg, yt-dlp, and the bot's existing axios/canvas/sharp packages.
 *
 * Song metadata (official album art, clean title/artist/album) comes from YouTube Music
 * via the InnerTube WEB_REMIX search, which reports `musicVideoType` so unofficial lyric
 * reuploads (UGC) are skipped in favour of official tracks (ATV/OMV).
 *
 * Word timing is resolved word-sync-first across several providers (BetterLyrics TTML, the
 * BetterLyrics QQ provider's QRC, LyricsPlus, and NetEase YRC); a line-level source is kept
 * only as a fallback. A track that genuinely has no word timing is swept as one continuous
 * line fill (Spotify-style) rather than a character-weighted per-word estimate.
 *
 * The visuals follow the Android player the feature is modelled on
 * (cabrata/utaloom-android, package com.metrolist.music): its `LyricsLine.kt` and
 * `ExperimentalLyrics.kt` define the typography, the dimming curve, the karaoke wipe and
 * the interlude dots, and `AppleMeshBackground.kt` defines the animated cover backdrop.
 */
const fs = require('fs');
const fsp = fs.promises;
const os = require('os');
const path = require('path');
const { spawn } = require('child_process');
const { once } = require('events');
const axios = require('axios');
const { createCanvas, loadImage } = require('canvas');

// [REMOTE RENDER] Config dari global.* (settings.js) / env.
function getRemoteConfig() {
  const g = typeof global !== 'undefined' ? global : {};
  const r = g.lyricVideoRemote || {};
  return {
    enabled: r.enabled === true,
    cdnApiBase: r.cdnApiBase || process.env.CDN_API_BASE_URL || 'https://cdn.patrickbotz.com',
    cdnApiKey: r.cdnApiKey || process.env.CDN_API_KEY || '',
    githubRepo: r.githubRepo || process.env.GITHUB_REPO || '',
    githubToken: r.githubToken || process.env.GITHUB_TOKEN || '',
    workflowFile: r.workflowFile || process.env.LYRIC_WORKFLOW_FILE || 'lyric-video.yml',
    resultPrefix: r.resultPrefix || 'lyric-video-results/',
    pollIntervalMs: Number(r.pollIntervalMs) || 8000,
    pollTimeoutMs: Number(r.pollTimeoutMs) || 30 * 60 * 1000,
  };
}

const sharp = require('sharp');
const { resolveFont } = require('./lyric-fonts');
const {
  romanizeLyrics,
  romanizeLine,
  romanizeKoreanWithSlices,
  romanizeChineseWithSlices,
  detectSongScript,
  detectCyrillicLanguage,
} = require('./lyric-romanize');

const WIDTH = 720;
const HEIGHT = 1280;
const FPS = 30;
const MAX_DURATION_SEC = 8 * 60;

// Typography measured from the reference video: Roboto Bold 44px, a 57px row pitch
// (line spacing 1.3) and a 38px gap between items, with the active line's baseline at
// 466/1280. The max width is what reproduces the reference's wrap points.
const LYRIC_FONT_SIZE = 44;
const LYRIC_FONT_WEIGHT = 'bold';
const LYRIC_ROW_HEIGHT = 57;
const LYRIC_LINE_GAP = 38;
const LYRIC_LEFT = 52;
const LYRIC_MAX_WIDTH = 616;
const LYRIC_ANCHOR_BASELINE = 466;
// Roboto Bold's cap/ascender height is ~0.78em; used to place a line's ink top from its baseline.
const LYRIC_ASCENT_RATIO = 0.78;
// Height reserved for an interlude (three dots) item in the lyric stack. It is small so the
// line after a gap lands where the reference puts it.
const LYRIC_ITEM_HEIGHT = 20;
// Unsung text on the active line. Both the Android player (`PENDING_ALPHA = 0.38`) and AMLL
// (`wordFadeWidth` pending stop at 0.4) settle around here, and the reference frames measure
// the same, so the unsung half of a line stays clearly readable instead of going grey.
const LYRIC_PENDING_ALPHA = 0.38;
// Background-vocal lines are dimmer and smaller than the main line, like the Android player
// (`opacity 0.4`, `font-size 0.7em`, italic).
const LYRIC_BG_ALPHA = 0.4;
// Inactive lines: AMLL uses a flat 0.2, the Android player 0.32, and the reference frames
// measure 0.35. The measured value is used so the stack keeps the reference's weight instead
// of going uniformly faint; the depth is carried by the blur, not by an opacity ramp.
const LYRIC_DIM_ALPHA = 0.35;
const LYRIC_FADE_TOP = 130;
const LYRIC_FADE_BOTTOM = 160;
const LYRIC_BAND_TOP = 170;
const LYRIC_BAND_BOTTOM = 1150;
// Romanization is a small secondary line under the original (the Utaloom `LyricRow` default:
// romanizeAsMain = false). Its size is the reference's 0.65em and it sits at a gentler alpha
// than the main line, so it reads as support text rather than competing with the karaoke.
const LYRIC_ROMAN_FONT_SIZE = 28;
const LYRIC_ROMAN_ROW_HEIGHT = 36;
const LYRIC_ROMAN_GAP = 6;
const LYRIC_ROMAN_ALPHA = 0.7;
// Fraction of the romanization's resting alpha an *unsung* romanized word sits at, mirroring the
// main line's pending level so the secondary line also reads as "filling in" word by word.
const LYRIC_ROMAN_PENDING_ALPHA = 0.45;
// The romanization runs the same karaoke effects as the main line — wipe, lift and held-syllable
// glow — scaled to its smaller font so the two lines read as one unit. The lift/clearance/pad are
// the main line's values multiplied by LYRIC_ROMAN_FONT_SIZE / LYRIC_FONT_SIZE (28/44 ≈ 0.64).
const LYRIC_ROMAN_WORD_LIFT = 2;
const LYRIC_ROMAN_LIFT_CLEARANCE = 7;
const LYRIC_ROMAN_GLOW_PAD = 4;
const LYRIC_ROMAN_HELD_GLOW_SCALE = 0.5;
// Minimum share of the romanization's characters that must line up with the per-syllable
// romanization before that alignment's timings are trusted. Below it (segmentations that differ
// too much, e.g. a kanji compound kuromoji reads as one word but the provider splits) the
// syllable-length spread is used instead, so the highlight can never jump backwards.
const LYRIC_ROMAN_ALIGN_MIN = 0.7;
// The reference scrolls with FastOutSlowIn over 550ms, each line delayed 45ms per row of
// distance (max 360ms) so the stack chases the active line instead of sliding as one block.
const LYRIC_SCROLL_MS = 550;
const LYRIC_STAGGER_MS = 45;
const LYRIC_STAGGER_MAX_MS = 360;
// Karaoke: a soft left-to-right wipe and a 4px lift while a word is being sung. The wipe
// tracks the syllable's own start/end times exactly (as AMLL and the Android player do) — the
// "already white" look came from the pending half of the line being composited with
// premultiplied alpha, which is fixed in `unpremultiplyBgra`.
//
// The gradient edge is a fixed width in em, not a fraction of the word. Measuring the reference
// shows the lit front is about half a letter wide no matter how long the word is; a word-relative
// edge makes the whole word fade at once, which is what reads as a per-word (not per-letter)
// wipe. AMLL does the same thing via `wordFadeWidth` (1.0 = Android, 0.5 = iPad), expressed as a
// multiple of the font size.
const LYRIC_WIPE_EM = 0.5;
// The Android player lifts a word 3dp while it is sung (`liftPx = 3.dp.toPx()`), eased out over
// max(250ms, syllable duration).
const LYRIC_WORD_LIFT = 3;
// Room above the word's ink that has to be erased before the lifted copy is drawn, so the
// un-lifted copy cannot show through and make the front look doubled.
const LYRIC_LIFT_CLEARANCE = 10;
// How far the held-syllable glow may extend past the glyph ink. It must stay well under the
// gap between two rows (≈13px), otherwise the glow of one row bleeds onto the row below it.
const LYRIC_GLOW_PAD = 6;
// Peak alpha of the held-syllable glow. A syllable that is held (sung for over a second) glows
// as it is held, peaking mid-syllable; this scales that peak. The glow is computed per syllable
// so a held syllable cannot light the syllables around it.
const LYRIC_HELD_GLOW_SCALE = 0.5;
// Inactive lines are blurred by distance the way AMLL does it (`1 + distance` px, and the
// Android player `min(distance, 4) * 0.9` dp). The strips below are pre-rendered per line, so
// the blur costs nothing per frame; index 0 is for the nearest inactive line. Kept gentle:
// the reference blurs just enough to read as depth, not enough to make the line unreadable.
const LYRIC_BLUR_RADII = [0.8, 1.3, 1.9, 2.5];
// Blur used for the held-syllable glow strip.
const LYRIC_GLOW_BLUR = 4;
// Interlude dots: radius 8px, 30px apart, starting just inside the lyric column.
const INTERLUDE_DOT_RADIUS = 8;
const INTERLUDE_DOT_STEP = 30;
const INTERLUDE_DOT_X = LYRIC_LEFT + 3.5;
// The reference shows a gap indicator once a pause passes 4.5s (2s for a blank line).
const GAP_MIN_MS = 4500;
const BLANK_GAP_MIN_MS = 2000;
const GAP_LEAD_MS = 300;
// A line-level lyric (no word timing) is sung as one continuous sweep across the whole line,
// the way Spotify fills a line, instead of the words being estimated by character count. The
// sweep runs from the line's start to the next line's start, so it finishes right as the next
// line takes over; when there is no next line (or it is too far) a length-based guess is used.
const LINE_LEVEL_MIN_MS = 1600;
const LINE_LEVEL_PER_CHAR_MS = 90;
const LINE_LEVEL_MAX_MS = 9000;

// Lyrics in these scripts are worth romanizing; Latin (and Greek/Cyrillic, which are read
// letter-for-letter) are already legible, so a song that is entirely in them is never sent to
// Romanization is strictly restricted to Japanese, Korean, and Chinese (CJK).
// Other languages (Latin, Cyrillic, Indic, Arabic, Thai, etc.) are never romanized.
const NON_LATIN_SCRIPT_RE = /[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff\uac00-\ud7a3\u1100-\u11ff\u3130-\u318f]/;

// Backdrop: the Apple Music mesh gradient, ported from amll-dev/applemusic-like-lyrics
// (`packages/core/src/bg-render/mesh-renderer/index.ts`, `mesh.frag.glsl`, `cp-presets.ts`
// and `packages/core/src/bg-render/img.ts`).
//
// The cover is reduced to a 32px texture, graded hard so only its colours survive, box-blurred,
// then warped through a bicubic Hermite control-point mesh. The texture lookup is spun about
// the (0.2, 0.2) uv point (scaled 0.8) and the result is vignetted — exactly the fragment
// shader AMLL uses, with the same `MIRRORED_REPEAT` wrap.
const BACKDROP_TEXTURE = 32;
// The mesh is rasterised per frame in JS. It is drawn straight at the output resolution —
// upscaling a smaller raster through node-canvas' smoothed `drawImage` costs far more than
// drawing the extra quads (measured ~52ms vs ~6ms per frame).
const BACKDROP_MESH_WIDTH = WIDTH;
const BACKDROP_MESH_HEIGHT = HEIGHT;
// The 32px texture sheet is upscaled once by this factor before it is blitted; a smooth,
// pre-blurred sheet blitted with smoothing disabled is much cheaper than letting cairo
// resample the tiny sheet on every triangle.
const BACKDROP_TILE_SCALE = 8;
// `setAlbum` grade: contrast 0.4 → saturate 3.0 → contrast 1.7 → brightness 0.75, then a
// box blur of radius 2 run 4 times (AMLL's `blurImage(imageData, 2, 4)`).
const BACKDROP_CONTRAST_A = 0.4;
const BACKDROP_SATURATION = 3.0;
const BACKDROP_CONTRAST_B = 1.7;
const BACKDROP_BRIGHTNESS = 0.75;
const BACKDROP_BLUR_RADIUS = 2;
const BACKDROP_BLUR_PASSES = 4;
// `setLowFreqVolume(1.0)` gives `u_volume = 0.1`, so `volumeEffect = 0.2` and the texture
// lookup is scaled to 0.8 about the (0.2, 0.2) point.
const BACKDROP_UV_ZOOM = 0.8;
const BACKDROP_UV_PIVOT = 0.2;
// `angle = (uTime + u_volume) * 2` with `uTime = t / 10` → 0.2 rad/s plus a 0.2 rad phase.
const BACKDROP_SPIN = 0.2;
const BACKDROP_SPIN_PHASE = 0.2;
// Vignette from `mesh.frag.glsl`: `mask = 0.6 + smoothstep(0.8, 0.3, distance(uv, 0.5)) * 0.4`.
const BACKDROP_VIGNETTE_INNER = 0.3;
const BACKDROP_VIGNETTE_OUTER = 0.8;
const BACKDROP_VIGNETTE_BASE = 0.6;
// AMLL's 5x5 control-point preset. Each row is [x, y, uRot°, vRot°, uScale, vScale] in
// column-major control-point order (cx fastest), positions in [-1, 1] with y pointing up.
const BACKDROP_CONTROL_POINTS = {
  width: 5,
  height: 5,
  rows: [
    [-1, -1, 0, 0, 1, 1], [-0.4501953125, -1, 0, 55, 1, 2.075], [0.1953125, -1, 0, 0, 1, 1], [0.4580078125, -1, 0, -25, 1, 1], [1, -1, 0, 0, 1, 1],
    [-1, -0.2514475377525607, -16, 0, 2.327, 0.943], [-0.55859375, -0.6609325945787148, 47, 0, 2.358, 0.377], [0.232421875, -0.5244375756366635, -66, -25, 1.855, 1.164], [0.685546875, -0.3753706470552125, 0, 0, 1, 1], [1, -0.6699125300354287, 0, 0, 1, 1],
    [-1, 0.035910396862284255, 0, 0, 1, 1], [-0.4921875, 0.005378616309457018, 90, 23, 1, 1.981], [0.021484375, -0.1365043639066228, 0, 42, 1, 1], [0.4765625, 0.05925822904974043, -30, 0, 1.95, 0.44], [1, 0.251428847823418, 0, 0, 1, 1],
    [-1, 0.6968336464764276, -68, 0, 1, 0.786], [-0.6904296875, 0.5890744209958608, -68, 0, 1, 1], [0.1845703125, 0.3879238667654693, 61, 0, 1, 1], [0.60546875, 0.4633553246018661, -47, -59, 0.849, 1.73], [1, 0.6214021886400309, -33, 0, 0.377, 1.604],
    [-1, 1, 0, 0, 1, 1], [-0.5, 1, 0, -73, 1, 1], [-0.3271484375, 1, 0, -24, 0.314, 2.704], [0.5, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1],
  ],
};
// Subdivision level for the control-point mesh (AMLL uses 50 at full WebGL resolution; the
// texture is only 32px and this raster is upscaled, so a much coarser grid is invisible).
const MESH_SUBDIVISIONS = 5;
const RAW_INPUT = 0;
const AUDIO_INPUT = 1;

function cleanText(value = '') {
  return String(value)
    .replace(/\[[^\]]*(official|video|audio|lyrics?|visuali[sz]er|remaster|hd)[^\]]*\]/ig, '')
    .replace(/\([^)]*(official|video|audio|lyrics?|visuali[sz]er|remaster|hd)[^)]*\)/ig, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function isYouTubeUrl(input) {
  try {
    const u = new URL(input);
    return ['youtube.com', 'www.youtube.com', 'm.youtube.com', 'music.youtube.com', 'youtu.be', 'www.youtu.be'].includes(u.hostname.toLowerCase());
  } catch {
    return false;
  }
}

function runProcess(command, args, options = {}) {
  const timeoutMs = options.timeoutMs || 120000;
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      cwd: options.cwd,
      windowsHide: true,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let settled = false;
    const timeout = setTimeout(() => {
      if (!settled) child.kill('SIGKILL');
    }, timeoutMs);
    child.stdout.on('data', d => { stdout += d.toString(); if (stdout.length > 8 * 1024 * 1024) stdout = stdout.slice(-8 * 1024 * 1024); });
    child.stderr.on('data', d => { stderr += d.toString(); if (stderr.length > 64 * 1024) stderr = stderr.slice(-64 * 1024); });
    child.on('error', err => {
      if (settled) return;
      settled = true;
      clearTimeout(timeout);
      reject(err);
    });
    child.on('close', code => {
      if (settled) return;
      settled = true;
      clearTimeout(timeout);
      if (code !== 0) return reject(new Error(stderr.trim() || `${command} exited with code ${code}`));
      resolve({ stdout, stderr });
    });
  });
}

function youtubeMusicThumbnail(url) {
  if (!url) return null;
  // YT Music serves the square album art at any size; ask for the largest one.
  return String(url).replace(/w\d+-h\d+/, 'w1000-h1000');
}

/**
 * Rejects the flat grey "no artwork" placeholders Deezer/iTunes/YouTube return, plus images
 * too small to look right, so a real cover (or the generated card) is used instead of a
 * grey music-note logo.
 */
async function isUsableCover(filePath) {
  try {
    const info = await sharp(filePath).metadata();
    if (!info.width || !info.height || info.width < 300 || info.height < 300) return false;
    const stats = await sharp(filePath).stats();
    const spread = Math.max(...stats.channels.slice(0, 3).map(channel => channel.stdev || 0));
    return spread > 10;
  } catch {
    return false;
  }
}

/**
 * Official album art by title/artist, independent of the video source. Deezer returns up
 * to 1000x1000, iTunes 600x600. Results are scored so a loose title match does not win.
 */
async function fetchOfficialCover(meta) {
  const term = `${meta.artist || ''} ${meta.title || ''}`.trim();
  if (!term) return null;
  const pick = (items, map) => {
    const titleKey = normalized(meta.title);
    const artistKey = normalized(meta.artist);
    let best = null;
    for (const item of items) {
      const info = map(item);
      if (!info || !info.cover) continue;
      const candidateTitle = normalized(info.title || '');
      const candidateArtist = normalized(info.artist || '');
      let score = 0;
      if (candidateTitle && candidateTitle === titleKey) score += 100;
      else if (candidateTitle && (candidateTitle.includes(titleKey) || titleKey.includes(candidateTitle))) score += 50;
      if (candidateArtist && candidateArtist === artistKey) score += 60;
      else if (candidateArtist && artistKey && (candidateArtist.includes(artistKey) || artistKey.includes(candidateArtist))) score += 25;
      if (info.duration && meta.duration) score -= Math.min(Math.abs(info.duration - meta.duration), 120) * 0.6;
      if (!best || score > best.score) best = { cover: info.cover, score };
    }
    return best && best.score > 30 ? best.cover : null;
  };
  try {
    const response = await axios.get('https://api.deezer.com/search', {
      params: { q: term, limit: 8 }, timeout: 12000, headers: { 'User-Agent': 'Mozilla/5.0' },
    });
    const cover = pick(Array.isArray(response.data?.data) ? response.data.data : [],
      it => ({ title: it.title, artist: it.artist?.name, duration: it.duration, cover: it.album?.cover_xl || it.album?.cover_big }));
    if (cover) return cover;
  } catch { /* try iTunes next */ }
  try {
    const response = await axios.get('https://itunes.apple.com/search', {
      params: { term, entity: 'song', limit: 8 }, timeout: 12000, headers: { 'User-Agent': 'Mozilla/5.0' },
    });
    const cover = pick(Array.isArray(response.data?.results) ? response.data.results : [],
      it => ({ title: it.trackName, artist: it.artistName, duration: it.trackTimeMillis ? it.trackTimeMillis / 1000 : null, cover: String(it.artworkUrl100 || '').replace(/100x100/, '600x600') }));
    if (cover) return cover;
  } catch { /* no official cover available */ }
  return null;
}

/**
 * YouTube Music search through the InnerTube WEB_REMIX endpoint — the same catalog
 * utaloom/ViMusic use. Unlike a plain YouTube search it reports `musicVideoType`, which
 * lets us keep official tracks (ATV/OMV) and drop unofficial user uploads (UGC) — the
 * usual source of "Artist - Song (Lyrics)" reuploads.
 */
const YTM_CLIENT_VERSION = '1.20241202.01.00';
// YT Music search filter for the "Songs" tab. Without it the search returns a mix dominated by
// videos and user uploads, and the real track can be missing entirely (e.g. "seasons" by
// wave to earth only appears under this filter).
const YTM_SONGS_FILTER = 'EgWKAQIIAWoKEAkQBRAKEAMQBA%3D%3D';
const MUSIC_VIDEO_TYPE_ATV = 'MUSIC_VIDEO_TYPE_ATV'; // official audio (Art Track)
const MUSIC_VIDEO_TYPE_OMV = 'MUSIC_VIDEO_TYPE_OMV'; // official music video
const MUSIC_VIDEO_TYPE_UGC = 'MUSIC_VIDEO_TYPE_UGC'; // user-generated upload

function walkJson(node, visit) {
  if (!node || typeof node !== 'object') return;
  visit(node);
  for (const key of Object.keys(node)) walkJson(node[key], visit);
}

/** Flattens a YT Music search response into candidate tracks with their video type. */
function extractYtMusicSongs(json) {
  const songs = [];
  walkJson(json, node => {
    const renderer = node.musicResponsiveListItemRenderer;
    if (!renderer) return;
    const runs = (renderer.flexColumns || [])
      .map(column => column?.musicResponsiveListItemFlexColumnRenderer?.text?.runs || [])
      .flat();
    const title = runs[0]?.text;
    const videoId = renderer.playlistItemData?.videoId
      || renderer.navigationEndpoint?.watchEndpoint?.videoId
      || renderer.overlay?.musicItemThumbnailOverlayRenderer?.content?.musicPlayButtonRenderer
        ?.playNavigationEndpoint?.watchEndpoint?.videoId
      || runs[0]?.navigationEndpoint?.watchEndpoint?.videoId;
    if (!title || !videoId) return;
    let videoType = null;
    walkJson(renderer, inner => {
      const type = inner.watchEndpoint?.watchEndpointMusicSupportedConfigs?.watchEndpointMusicConfig?.musicVideoType;
      if (type) videoType = type;
    });
    // The square YT Music artwork (yt3.googleusercontent.com) is the official album art for
    // Art Tracks; for UGC rows it is just the 16:9 video thumbnail, which callers discard.
    let thumbnail = null;
    walkJson(renderer, inner => {
      const thumbs = inner.musicThumbnailRenderer?.thumbnail?.thumbnails;
      if (!Array.isArray(thumbs) || !thumbs.length) return;
      const largest = thumbs.reduce((a, b) => ((b.width || 0) > (a.width || 0) ? b : a));
      if (largest?.url) thumbnail = largest.url;
    });
    const pageTypeOf = run => run?.navigationEndpoint?.browseEndpoint
      ?.browseEndpointContextSupportedConfigs?.browseEndpointContextMusicConfig?.pageType;
    const artists = runs.filter(run => pageTypeOf(run) === 'MUSIC_PAGE_TYPE_ARTIST').map(run => run.text).filter(Boolean);
    const albumRun = runs.find(run => pageTypeOf(run) === 'MUSIC_PAGE_TYPE_ALBUM');
    const durationRun = [...runs].reverse().find(run => /^\d+:\d{2}$/.test(run.text || ''));
    const duration = durationRun
      ? durationRun.text.split(':').reduce((total, part) => total * 60 + Number(part), 0)
      : null;
    songs.push({ title, videoId, videoType, artists, album: albumRun?.text || '', duration, thumbnail });
  });
  return songs;
}

/** Titles that advertise themselves as reuploads rather than official releases. */
function isUnofficialTitle(title = '') {
  return /\b(lyric|lirik|karaoke|cover|reaction|mashup|nightcore|speed ?up|slowed|instrumental|tanpa vokal)\b/i.test(title);
}

/**
 * Picks the best candidate.
 *
 * Relevance dominates: the query words are matched against the title and artist, and a
 * candidate must cover at least half of them (never just one of several). Clean titles whose
 * words all come from the query are rewarded, while titles padded with extra words ("... Live
 * at ...", "... (tradução)") are penalised — that padding is what marks a reupload. The video
 * type and duration then only break ties, because weighting the type heavily is what
 * previously let an unrelated official track ("closing.") beat the requested song ("seasons").
 */
function pickBestSong(songs, query, duration) {
  const words = normalized(query).split(' ').filter(word => word.length > 1);
  const wordSet = new Set(words);
  const covers = (queryWord, haystack) =>
    haystack.has(queryWord) || (queryWord.length >= 4 && [...haystack].some(word => word.includes(queryWord)));

  const evaluate = minMatches => {
    let best = null;
    for (const song of songs) {
      if (!song.videoType || song.videoType === 'MUSIC_VIDEO_TYPE_PODCAST_EPISODE') continue;
      if (song.videoType === MUSIC_VIDEO_TYPE_UGC && isUnofficialTitle(song.title)) continue;

      const titleWords = normalized(song.title).split(' ').filter(Boolean);
      const artistWords = normalized((song.artists || []).join(' ')).split(' ').filter(Boolean);
      const haystack = new Set([...titleWords, ...artistWords]);
      const hits = words.filter(word => covers(word, haystack)).length;
      if (hits < minMatches) continue;

      let score = hits * 40;
      // A title built only from the query's words is a clean, almost certainly official match;
      // extra words ("... Live at ...", "... (tradução)") mark a reupload.
      const extraTitleWords = titleWords.filter(word => !wordSet.has(word) && !words.some(q => word.includes(q) || q.includes(word)));
      if (titleWords.length && extraTitleWords.length === 0) score += 60;
      score -= extraTitleWords.length * 15;
      // The requested artist should be credited, but this only ever breaks ties.
      const artistSet = new Set(artistWords);
      score += words.filter(word => covers(word, artistSet)).length * 15;

      if (song.videoType === MUSIC_VIDEO_TYPE_ATV) score += 25;
      else if (song.videoType === MUSIC_VIDEO_TYPE_OMV) score += 20;
      else if (song.videoType === MUSIC_VIDEO_TYPE_UGC) score -= 20;

      if (song.duration && duration) score -= Math.min(Math.abs(song.duration - duration), 90) * 0.5;
      if (!best || score > best.score) best = { song, score };
    }
    return best && best.score > 0 ? best.song : null;
  };

  // Prefer a candidate that covers the entire query ("artist + title" as typed). Only if none
  // does, relax to partial coverage — otherwise a same-artist track could win over the song
  // that was actually asked for.
  const strict = words.length >= 2 ? evaluate(words.length) : null;
  if (strict) return strict;
  const minMatches = words.length <= 1 ? words.length : Math.max(2, Math.ceil(words.length * 0.5));
  return evaluate(minMatches);
}

async function searchYouTubeMusicInnerTube(query, duration) {
  const request = params => axios.post('https://music.youtube.com/youtubei/v1/search?prettyPrint=false', {
    context: { client: { clientName: 'WEB_REMIX', clientVersion: YTM_CLIENT_VERSION, hl: 'en', gl: 'US' } },
    query,
    ...(params ? { params } : {}),
  }, {
    timeout: 12000,
    headers: {
      'Content-Type': 'application/json',
      'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36',
      Origin: 'https://music.youtube.com',
      'X-Goog-Api-Format-Version': '2',
    },
  });
  // The "Songs" filter is what surfaces the official track; fall back to an unfiltered search
  // for queries it cannot answer (very new or non-catalogue tracks).
  let hit = await request(YTM_SONGS_FILTER)
    .then(response => pickBestSong(extractYtMusicSongs(response.data), query, duration))
    .catch(() => null);
  if (!hit) {
    hit = await request(null)
      .then(response => pickBestSong(extractYtMusicSongs(response.data), query, duration))
      .catch(() => null);
  }
  if (!hit) return null;
  return {
    url: `https://www.youtube.com/watch?v=${hit.videoId}`,
    id: hit.videoId,
    title: cleanText(hit.title),
    artist: cleanText((hit.artists || []).join(', ')) || 'Unknown artist',
    album: cleanText(hit.album || ''),
    duration: hit.duration || null,
    videoType: hit.videoType,
    thumbnail: youtubeMusicThumbnail(hit.thumbnail),
  };
}

/** Official track lookup via YouTube Music (album art, clean title/artist/album). */
async function searchYouTubeMusic(query, duration) {
  const viaInnerTube = await searchYouTubeMusicInnerTube(query, duration).catch(() => null);
  if (viaInnerTube) return viaInnerTube;
  // Fallback for environments where the InnerTube call is blocked.
  let ytM;
  try {
    const mod = await import('node-youtube-music');
    ytM = mod.default || mod;
  } catch {
    return null;
  }
  if (!ytM || typeof ytM.searchMusics !== 'function') return null;
  let results;
  try {
    results = await ytM.searchMusics(query);
  } catch {
    return null;
  }
  const hit = Array.isArray(results)
    ? results.find(item => item && item.youtubeId && !isUnofficialTitle(item.title))
    : null;
  if (!hit) return null;
  const artist = Array.isArray(hit.artists) ? hit.artists.map(a => a?.name).filter(Boolean).join(', ') : '';
  return {
    url: `https://www.youtube.com/watch?v=${hit.youtubeId}`,
    id: hit.youtubeId,
    title: cleanText(hit.title || ''),
    artist: cleanText(artist) || 'Unknown artist',
    album: cleanText(hit.album || ''),
    thumbnail: youtubeMusicThumbnail(hit.thumbnailUrl),
    duration: hit.duration?.totalSeconds || null,
  };
}

/** Last-resort lookup via youtube-yts, skipping unofficial lyric/karaoke reuploads. */
async function searchYouTube(query) {
  const yts = require('youtube-yts');
  const result = await yts(query);
  const videos = Array.isArray(result?.all)
    ? result.all.filter(item => item?.type === 'video' && (item.url || item.videoId))
    : [];
  const video = videos.find(item => !isUnofficialTitle(item.title || '')) || videos[0];
  if (!video) throw new Error('Lagu/video tidak ditemukan di pencarian YouTube.');
  return video.url || `https://www.youtube.com/watch?v=${video.videoId}`;
}

async function getVideoMetadata(input) {
  const raw = String(input || '').trim();
  let music = null;
  let url;
  if (isYouTubeUrl(raw)) {
    url = raw;
  } else {
    music = await searchYouTubeMusic(raw).catch(() => null);
    url = music?.url || await searchYouTube(raw);
  }

  const { stdout } = await runProcess('yt-dlp', [
    '--dump-single-json', '--skip-download', '--no-playlist', '--no-warnings',
    '--js-runtimes', 'node', '--remote-components', 'ejs:github', url,
  ], { timeoutMs: 90000 });
  let metadata;
  try { metadata = JSON.parse(stdout); }
  catch { throw new Error('Metadata YouTube tidak dapat dibaca. Pastikan yt-dlp versi baru terpasang.'); }
  if (!metadata || !metadata.id) throw new Error('Metadata video YouTube tidak lengkap.');
  const duration = Number(metadata.duration || 0);
  if (!Number.isFinite(duration) || duration <= 0) throw new Error('Durasi lagu tidak valid atau video sedang live.');
  if (duration > MAX_DURATION_SEC) throw new Error('Durasi dibatasi maksimal 8 menit agar proses render dan ukuran video tetap terkendali.');

  // A direct URL skips the initial music search, so try to enrich it by title to
  // still get official album art. Then fall back to the raw YouTube video fields.
  if (!music) {
    const guess = cleanText(metadata.track || metadata.title || '');
    if (guess) music = await searchYouTubeMusic(guess, duration).catch(() => null);
  }
  if (!music) {
    music = {
      title: cleanText(metadata.track || metadata.title || 'Unknown track'),
      artist: cleanText(metadata.artist || metadata.album_artist || metadata.creator || metadata.uploader || metadata.channel || 'Unknown artist'),
      album: cleanText(metadata.album || ''),
      thumbnail: metadata.thumbnail || `https://i.ytimg.com/vi/${metadata.id}/hqdefault.jpg`,
    };
  }

  const title = music.title || 'Unknown track';
  const artist = music.artist || 'Unknown artist';
  const album = music.album || '';

  // Prefer official album art: keep a non-YouTube thumbnail if the music search gave one,
  // otherwise ask Deezer/iTunes, and only then fall back to the video thumbnail.
  const isVideoThumb = /(^|\/\/)i\.ytimg\.com\//i.test(music.thumbnail || '');
  let thumbnail = music.thumbnail && !isVideoThumb ? music.thumbnail : null;
  if (!thumbnail) thumbnail = await fetchOfficialCover({ title, artist, album, duration }).catch(() => null);
  if (!thumbnail) thumbnail = music.thumbnail || metadata.thumbnail || `https://i.ytimg.com/vi/${metadata.id}/hqdefault.jpg`;

  return {
    url,
    id: metadata.id,
    title,
    artist,
    album,
    duration,
    thumbnail,
    webpageUrl: metadata.webpage_url || url,
  };
}

async function downloadAudio(meta, tempDir) {
  const template = path.join(tempDir, 'audio.%(ext)s');
  await runProcess('yt-dlp', [
    '--no-playlist', '--no-warnings', '-x', '--audio-format', 'mp3', '--audio-quality', '128K',
    '--js-runtimes', 'node', '--remote-components', 'ejs:github',
    '-o', template, meta.url,
  ], { cwd: tempDir, timeoutMs: Math.max(180000, meta.duration * 3000) });
  const names = await fsp.readdir(tempDir);
  const audio = names.find(name => /^audio\./i.test(name) && /\.(mp3|m4a|opus|wav|webm)$/i.test(name));
  if (!audio) throw new Error('Audio hasil download tidak ditemukan.');
  return path.join(tempDir, audio);
}

async function downloadCover(meta, tempDir) {
  const coverPath = path.join(tempDir, 'cover.jpg');
  const urls = [meta.thumbnail, `https://i.ytimg.com/vi/${meta.id}/hqdefault.jpg`].filter(Boolean);
  for (const url of [...new Set(urls)]) {
    try {
      const response = await axios.get(url, {
        responseType: 'arraybuffer', timeout: 15000, maxContentLength: 12 * 1024 * 1024,
        headers: { 'User-Agent': 'Mozilla/5.0' },
      });
      await fsp.writeFile(coverPath, response.data);
      await loadImage(coverPath); // Validate that Canvas can decode it.
      if (!(await isUsableCover(coverPath))) continue; // Skip grey placeholders and tiny images.
      return coverPath;
    } catch { /* try the next thumbnail */ }
  }
  // A generated fallback keeps the video pipeline usable if the artwork is unavailable.
  const fallback = createCanvas(600, 600);
  const ctx = fallback.getContext('2d');
  const gradient = ctx.createLinearGradient(0, 0, 600, 600);
  gradient.addColorStop(0, '#164e78'); gradient.addColorStop(1, '#15172d');
  ctx.fillStyle = gradient; ctx.fillRect(0, 0, 600, 600);
  ctx.fillStyle = '#ffffff'; ctx.font = 'bold 150px Arial'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('♫', 300, 280);
  ctx.font = 'bold 30px Arial'; ctx.fillText('LYRIC VIDEO', 300, 410);
  await fsp.writeFile(coverPath, fallback.toBuffer('image/jpeg', { quality: 0.88 }));
  return coverPath;
}

function decodeXml(value = '') {
  return String(value)
    .replace(/<[^>]*>/g, '')
    .replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&apos;/g, "'")
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(Number(n)))
    .replace(/&#x([\da-f]+);/ig, (_, n) => String.fromCodePoint(parseInt(n, 16)));
}

function parseAttrs(raw = '') {
  const attrs = {};
  const re = /([\w:.-]+)\s*=\s*(["'])(.*?)\2/g;
  let m;
  while ((m = re.exec(raw))) attrs[m[1].split(':').pop()] = m[3];
  return attrs;
}

function parseTime(value) {
  if (!value) return null;
  const v = String(value).trim();
  let m = v.match(/^(?:(\d+):)?(\d{1,2}):(\d{1,2})(?:[.,](\d+))?$/);
  if (m) {
    const hours = Number(m[1] || 0), minutes = Number(m[2] || 0), seconds = Number(m[3] || 0);
    const frac = m[4] ? Number(`0.${m[4]}`) : 0;
    return Math.round((hours * 3600 + minutes * 60 + seconds + frac) * 1000);
  }
  m = v.match(/^(\d+(?:\.\d+)?)(ms|s|m|h)?$/i);
  if (!m) return null;
  const number = Number(m[1]);
  const unit = (m[2] || 's').toLowerCase();
  const multiplier = unit === 'ms' ? 1 : unit === 'm' ? 60000 : unit === 'h' ? 3600000 : 1000;
  return Math.round(number * multiplier);
}

/**
 * Parses TTML into timed lines. Words keep the inter-word spacing that lives in the
 * surrounding text nodes, otherwise a whole line collapses into one giant word.
 * `<span ttm:role="x-bg">` becomes its own background line, and a `div`'s agent is carried
 * onto every line it contains, matching the Android TTML parser.
 */
function parseTTML(ttml) {
  const lines = [];
  const pRegex = /<(?:[\w.-]+:)?p\b([^>]*)>([\s\S]*?)<\/(?:[\w.-]+:)?p\s*>/gi;
  // Agents are declared on the enclosing <div>, so scan divs and their p children together.
  const divRegex = /<(?:[\w.-]+:)?div\b([^>]*)>([\s\S]*?)<\/(?:[\w.-]+:)?div\s*>/gi;
  let p;
  const withAgent = [];
  while ((p = pRegex.exec(ttml))) withAgent.push({ attrs: parseAttrs(p[1]), body: p[2], agent: null });
  let d;
  while ((d = divRegex.exec(ttml))) {
    const agent = parseAttrs(d[1]).agent || null;
    if (!agent) continue;
    let inner;
    const innerRegex = /<(?:[\w.-]+:)?p\b([^>]*)>([\s\S]*?)<\/(?:[\w.-]+:)?p\s*>/gi;
    while ((inner = innerRegex.exec(d[2]))) {
      const body = inner[2];
      const match = withAgent.find(entry => entry.body === body);
      if (match) match.agent = agent;
    }
  }

  for (const entry of withAgent) {
    const pAttrs = entry.attrs;
    const body = entry.body;
    // Walk spans with balanced tag matching. The space that separates two words lives in a
    // text node outside the spans, and a `<span role="x-bg">` may *wrap* further timed spans
    // instead of carrying its own timing, so a naive non-greedy regex would swallow the
    // wrapper's closing tag and lose the nested words.
    const spans = [];
    const bgSpans = [];
    const findSpanClose = (source, from) => {
      let depth = 1;
      const re = /<(\/?)(?:[\w.-]+:)?span\b[^>]*>/gi;
      re.lastIndex = from;
      let m;
      while ((m = re.exec(source))) {
        if (m[1] === '/') { depth--; if (depth === 0) return m.index; }
        else depth++;
      }
      return source.length;
    };
    const walk = (source, background) => {
      let index = 0;
      let last = null;
      const openRe = /<(?:[\w.-]+:)?span\b([^>]*)>/gi;
      while (index < source.length) {
        openRe.lastIndex = index;
        const open = openRe.exec(source);
        if (!open) {
          if (/\s/.test(source.slice(index)) && last) last.trailingSpace = true;
          break;
        }
        if (/\s/.test(source.slice(index, open.index)) && last) last.trailingSpace = true;
        const attrs = parseAttrs(open[1]);
        const closeIndex = findSpanClose(source, openRe.lastIndex);
        const inner = source.slice(openRe.lastIndex, closeIndex);
        const role = String(attrs.role || '').toLowerCase();
        if (role === 'translation' || role === 'roman' || role === 'x-translation' || role === 'x-roman') {
          index = closeIndex + 7;
          continue;
        }
        const isBg = background || role === 'x-bg' || role === 'bg';
        const startMs = parseTime(attrs.begin);
        const endMs = parseTime(attrs.end);
        if (startMs != null && endMs != null) {
          const span = { text: decodeXml(inner), startMs, endMs, trailingSpace: /\s$/.test(inner), background: isBg };
          (isBg ? bgSpans : spans).push(span);
          last = span;
          index = closeIndex + 7;
        } else {
          // No timing of its own: descend so the nested timed spans are collected.
          walk(inner, isBg);
          index = closeIndex + 7;
        }
      }
    };
    walk(body, false);

    // Syllables (not words): the space that separates words lives in the surrounding text
    // nodes, so the list is regrouped into words at layout time, exactly like the
    // LyricsPlus path. Keeping the raw syllables here is what lets a word that is split
    // across spans ("fa" + "llin'") stay a single unbroken run on screen.
    const buildSyllables = spanList => {
      const syllables = [];
      for (const span of spanList) {
        if (span.startMs == null || span.endMs == null || span.endMs <= span.startMs) continue;
        const parts = span.text.match(/\S+\s*/gu) || [];
        const pieces = parts.length ? parts : [span.text];
        const total = span.text.length || 1;
        let used = 0;
        pieces.forEach((part, index) => {
          const token = part.trim();
          const startMs = span.startMs + Math.round((span.endMs - span.startMs) * used / total);
          used += part.length;
          const endMs = span.startMs + Math.round((span.endMs - span.startMs) * used / total);
          const trailing = index === pieces.length - 1 ? span.trailingSpace : /\s$/.test(part);
          if (token) syllables.push({ text: token, startMs, endMs, trailingSpace: !!trailing });
        });
      }
      return syllables;
    };

    const bgSyllables = buildSyllables(bgSpans);
    const mainSyllables = buildSyllables(spans);
    // A line's displayed text is the syllable text joined without a space inside a word and
    // with one between words, so it matches what the karaoke wipes across.
    const joinText = syllables => {
      let out = '';
      syllables.forEach((syllable, index) => {
        out += syllable.text;
        if (index < syllables.length - 1 && syllable.trailingSpace) out += ' ';
      });
      return out.trim();
    };
    const bgText = bgSyllables.length ? joinText(bgSyllables) : decodeXml(body).replace(/\s+/g, ' ').trim();
    if (bgSyllables.length) {
      const bgTime = bgSpans.find(span => span.startMs != null)?.startMs ?? bgSyllables[0].startMs;
      if (bgText) lines.push({ timeMs: bgTime, text: bgText, words: bgSyllables, background: true, agent: entry.agent });
    }

    const text = mainSyllables.length ? joinText(mainSyllables) : decodeXml(body).replace(/\s+/g, ' ').trim();
    if (!text) continue;
    const timeMs = parseTime(pAttrs.begin) ?? mainSyllables[0]?.startMs;
    if (timeMs == null) continue;
    lines.push({ timeMs, text, words: mainSyllables, background: false, agent: entry.agent });
  }
  return lines.sort((a, b) => a.timeMs - b.timeMs);
}

/**
 * Parses LRC, including multiple time tags per line and the extended form used by the
 * Android player: `{agent:v1}` / `{bg}` voice tags followed by a
 * `<word:startSec:endSec|...>` word-sync block.
 */
function parseLrc(raw) {
  const lines = [];
  const timeRegex = /\[(\d{1,3}):(\d{1,2})(?:[.:](\d{1,3}))?\]/g;
  const wordBlockRegex = /^<(.+)>$/;
  const voiceTagRegex = /^\{(agent:[\w]+|bg)\}/;
  let lastAdded = 0;
  let agent = null;
  for (const sourceLine of String(raw || '').split(/\r?\n/)) {
    const trimmed = sourceLine.trim();
    const wordBlock = trimmed.match(wordBlockRegex);
    if (wordBlock) {
      // Extended LRC: <word:startSec:endSec|word:startSec:endSec>. The entries are
      // syllables, so they are grouped back into the space-separated words of the line they
      // belong to — otherwise a word split across syllables ("fa" + "llin'") would be drawn
      // as two words with a gap in the middle.
      const syllables = wordBlock[1].split('|').map(part => {
        const pieces = part.split(':');
        const end = Number(pieces[pieces.length - 1]);
        const start = Number(pieces[pieces.length - 2]);
        const text = pieces.slice(0, -2).join(':').trim();
        if (pieces.length < 3 || !Number.isFinite(start) || !Number.isFinite(end) || !text) return null;
        return { text, startMs: Math.round(start * 1000), endMs: Math.round(end * 1000), trailingSpace: /\s$/.test(pieces.slice(0, -2).join(':')) };
      }).filter(Boolean);
      for (let i = lines.length - lastAdded; i < lines.length; i++) lines[i].words = syllables;
      lastAdded = 0;
      continue;
    }
    const stamps = [...sourceLine.matchAll(timeRegex)];
    lastAdded = 0;
    if (!stamps.length) continue;
    const last = stamps[stamps.length - 1];
    let text = sourceLine.slice(last.index + last[0].length).trim();
    const voice = text.match(voiceTagRegex);
    const background = voice ? voice[1] === 'bg' : false;
    if (voice) {
      if (voice[1].startsWith('agent:')) agent = voice[1].slice('agent:'.length);
      text = text.slice(voice[0].length).trim();
    }
    if (!text || /^\w+:/i.test(text) && !/\s/.test(text)) continue;
    for (const stamp of stamps) {
      const fraction = stamp[3] ? (stamp[3].length === 1 ? Number(stamp[3]) * 100 : stamp[3].length === 2 ? Number(stamp[3]) * 10 : Number(stamp[3].slice(0, 3))) : 0;
      lines.push({
        timeMs: Number(stamp[1]) * 60000 + Number(stamp[2]) * 1000 + fraction,
        text,
        words: [],
        background,
        agent,
      });
      lastAdded++;
    }
  }
  return lines.sort((a, b) => a.timeMs - b.timeMs);
}

/** Unescapes XML/HTML entities without stripping tags (QRC embeds its payload this way). */
function unescapeEntities(value = '') {
  return String(value)
    .replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&apos;/g, "'")
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(Number(n)))
    .replace(/&#x([\da-f]+);/ig, (_, n) => String.fromCodePoint(parseInt(n, 16)))
    // `&amp;` is decoded last so an escaped `&amp;lt;` cannot turn into a live `<`.
    .replace(/&amp;/g, '&');
}

// Credit/attribution lines that providers such as QQ Music put at the top of the lyric
// body ("作词 : …", "Lyrics by …"). They are not sung, so they are dropped.
const LYRIC_CREDIT_RE = /(作[词詞]|作曲|编曲|編曲|制作人|製作人|制作|製作|混音|母带|母帶|录音|錄音|监制|監製|出品|和声|和聲|伴唱|[词詞]\s*[:：]|曲\s*[:：]|吉他\s*[:：]|贝斯\s*[:：]|貝斯\s*[:：]|鼓\s*[:：]|键盘\s*[:：]|鍵盤\s*[:：]|弦乐\s*[:：]|弦樂\s*[:：]|人声\s*[:：]|人聲\s*[:：]|统筹\s*[:：]|統籌\s*[:：]|策划\s*[:：]|策劃\s*[:：]|Lyrics?\s+by|Composed\s+by|Written\s+by|Produced\s+by|Arranged\s+by|Mixed\s+by|Mastered\s+by|Music\s+by|Recorded\s+by|Vocals?\s+by|Mixing\s+by|Guitar\s+by|Bass\s+by|Piano\s+by|OP\s*[:：]|SP\s*[:：])/i;

/** Drops header/credit lines that some providers prepend (the song title, "Title - Artist"). */
function filterHeaderLines(lines, meta) {
  const titleKey = normalized(meta?.title || '');
  const artistKey = normalized(meta?.artist || '');
  return lines.filter(line => {
    const norm = normalized(line.text || '');
    if (!norm) return false;
    // Credit/attribution lines ("词：…", "Lyrics by …") are not sung; drop them here too so
    // every provider path (QRC/YRC already drop them in their parsers, LRC does not) is covered.
    if (LYRIC_CREDIT_RE.test(line.text || '')) return false;
    if (titleKey && norm === titleKey) return false;
    if (titleKey && artistKey && norm.includes(titleKey) && norm.includes(artistKey)) return false;
    if (artistKey && norm === artistKey) return false;
    return true;
  });
}

/**
 * Parses QQ Music QRC (word-by-word). Each line is `[lineStart,lineDur]` followed by
 * segments `text(start,dur)`; the segments are syllables, regrouped into words at layout
 * time exactly like the LyricsPlus/TTML paths. Background vocals are wrapped in
 * parentheses by the provider, matching AMLL's `parseQrc`.
 */
function parseQrc(raw) {
  const lines = [];
  const linePattern = /^\[(\d+),(\d+)\]/;
  const wordPattern = /([^()]*)\((\d+),(\d+)\)/g;
  for (const sourceLine of String(raw || '').split(/\r?\n/)) {
    const lineStr = sourceLine.trim();
    const head = lineStr.match(linePattern);
    if (!head) continue; // skips [ti:…] / [ar:…] / [by:…] tags
    const body = lineStr.slice(head[0].length);
    const segments = [];
    wordPattern.lastIndex = 0;
    let m;
    while ((m = wordPattern.exec(body))) {
      const rawText = m[1];
      const startMs = Number(m[2]);
      const duration = Number(m[3]);
      const token = rawText.trim();
      if (!token) {
        // A pure-space run carries no word; it only marks a boundary for the previous one.
        if (segments.length) segments[segments.length - 1].trailingSpace = true;
        continue;
      }
      segments.push({ text: token, startMs, endMs: startMs + Math.max(duration, 1), trailingSpace: /\s$/.test(rawText) });
    }
    const firstWord = segments[0];
    const lastWord = segments[segments.length - 1];
    const background = Boolean(firstWord && lastWord)
      && /^[(（]/.test(firstWord.text) && /[）)]$/.test(lastWord.text);
    if (background) {
      firstWord.text = firstWord.text.replace(/^[(（]/, '');
      lastWord.text = lastWord.text.replace(/[）)]$/, '');
    }
    const text = joinSyllableText(segments);
    if (!text || LYRIC_CREDIT_RE.test(text)) continue;
    lines.push({ timeMs: Number(head[1]), text, words: segments, background, agent: null });
  }
  return lines.sort((a, b) => a.timeMs - b.timeMs);
}

/**
 * Parses NetEase Cloud Music YRC (word-by-word). Each line is `[lineStart,lineDur]`
 * followed by segments `(start,dur,0)text`; the text trails its own timing tuple, so it is
 * read up to the next `(`.
 */
function parseYrc(raw) {
  const lines = [];
  const linePattern = /^\[(\d+),(\d+)\]/;
  const wordPattern = /\((\d+),(\d+),\d+\)([^(]*)/g;
  for (const sourceLine of String(raw || '').split(/\r?\n/)) {
    const lineStr = sourceLine.trim();
    const head = lineStr.match(linePattern);
    if (!head) continue;
    const body = lineStr.slice(head[0].length);
    const segments = [];
    wordPattern.lastIndex = 0;
    let m;
    while ((m = wordPattern.exec(body))) {
      const startMs = Number(m[1]);
      const duration = Number(m[2]);
      const rawText = m[3];
      const token = rawText.trim();
      if (!token) {
        if (segments.length) segments[segments.length - 1].trailingSpace = true;
        continue;
      }
      segments.push({ text: token, startMs, endMs: startMs + Math.max(duration, 1), trailingSpace: /\s$/.test(rawText) });
    }
    const text = joinSyllableText(segments);
    if (!text || LYRIC_CREDIT_RE.test(text)) continue;
    lines.push({ timeMs: Number(head[1]), text, words: segments, background: false, agent: null });
  }
  return lines.sort((a, b) => a.timeMs - b.timeMs);
}

/** Joins timed syllables into a line's text, honouring the inter-word spaces. */
function joinSyllableText(segments) {
  let out = '';
  segments.forEach((s, index) => {
    out += s.text;
    if (index < segments.length - 1 && s.trailingSpace) out += ' ';
  });
  return out.replace(/\s+/g, ' ').trim();
}

/**
 * Groups timed syllables back into the space-separated words of [text] (keeps CJK lines
 * whole). Each group keeps the syllables it was built from so the karaoke wipe can move
 * through a word syllable by syllable without ever breaking it apart.
 */
function groupSyllablesIntoWords(text, syllables) {
  const groups = [];
  let cursor = 0;
  let open = false;
  for (const syl of syllables) {
    const token = syl.text.trim();
    if (!token) continue;
    const entry = { text: token, startMs: syl.startMs, endMs: syl.endMs, syllables: [syl] };
    // Locate the syllable in the line text; when it cannot be found (punctuation variants,
    // provider text that differs from the word block) it still becomes its own word.
    const at = text.indexOf(token, cursor);
    if (at < 0) { groups.push(entry); open = false; continue; }
    if (!open || at !== cursor) {
      groups.push(entry);
    } else {
      const group = groups[groups.length - 1];
      group.text += token;
      group.endMs = Math.max(group.endMs, syl.endMs);
      group.syllables.push(syl);
    }
    cursor = at + token.length;
    // A syllable continues the previous word only when nothing separates them in the text;
    // a trailing space on the syllable also marks a word boundary.
    open = cursor < text.length && !/\s/.test(text[cursor]) && !syl.trailingSpace;
  }
  return groups;
}

function normalized(value = '') {
  return cleanText(value).toLowerCase().replace(/[^\p{L}\p{N}]+/gu, ' ').trim();
}

async function fetchBetterLyrics(meta) {
  try {
    const headers = { 'User-Agent': 'Mozilla/5.0', Accept: 'application/json' };
    if (process.env.BETTERLYRICS_API_KEY) headers['X-API-Key'] = process.env.BETTERLYRICS_API_KEY;
    const response = await axios.get('https://lyrics-api.boidu.dev/getLyrics', {
      params: { s: meta.title, a: meta.artist, d: Math.round(meta.duration), ...(meta.album ? { al: meta.album } : {}) },
      timeout: 15000,
      headers,
      maxContentLength: 5 * 1024 * 1024,
      validateStatus: status => status < 500,
    });
    if (response.status !== 200) return null;
    const ttml = response.data?.ttml;
    if (typeof ttml !== 'string' || !ttml.trim()) return null;
    const lines = parseTTML(ttml);
    if (lines.length < 4) return null;
    return { lines, provider: 'BetterLyrics', wordSynced: lines.some(line => line.words.length > 0), approximate: false };
  } catch {
    return null;
  }
}

/**
 * Converts the LyricsPlus JSON into lines, keeping the duet agent and the background
 * vocals the provider marks on individual syllables. A line whose syllables mix main and
 * background vocals is split in two, exactly like the Android provider does before it
 * hands the lyrics to the renderer.
 */
function parseLyricsPlusLines(data) {
  if (!data || !Array.isArray(data.lyrics)) return [];
  const lines = [];
  const toSyllables = list => list.map(syl => {
    const startMs = Number(syl.time);
    const duration = Number(syl.duration);
    if (!Number.isFinite(startMs) || !Number.isFinite(duration)) return null;
    return { text: String(syl.text || ''), startMs: Math.round(startMs), endMs: Math.round(startMs + duration) };
  }).filter(Boolean);
  for (const item of data.lyrics) {
    const timeMs = Number(item.time);
    const text = String(item.text || '').trim();
    if (!Number.isFinite(timeMs) || !text) continue;
    const singer = String(item.element?.singer || '').toLowerCase();
    const agent = /^(v\d+|v1000)$/.test(singer) ? singer : null;
    const syllabus = Array.isArray(item.syllabus) ? item.syllabus : [];
    const toSyllables = list => list.map(syl => {
      const startMs = Number(syl.time);
      const duration = Number(syl.duration);
      if (!Number.isFinite(startMs) || !Number.isFinite(duration)) return null;
      const raw = String(syl.text || '');
      return { text: raw.trim(), startMs: Math.round(startMs), endMs: Math.round(startMs + duration), trailingSpace: /\s$/.test(raw) };
    }).filter(Boolean);
    const mainSyllables = toSyllables(syllabus.filter(syl => !syl.isBackground));
    const bgSyllables = toSyllables(syllabus.filter(syl => syl.isBackground));
    const joinSyllables = list => list.map(syl => syl.text + (syl.trailingSpace ? ' ' : '')).join('').replace(/\s+/g, ' ').trim();
    if (mainSyllables.length) {
      lines.push({ timeMs: Math.round(timeMs), text, words: mainSyllables, background: false, agent });
    } else if (!bgSyllables.length) {
      lines.push({ timeMs: Math.round(timeMs), text, words: [], background: false, agent });
    }

    if (bgSyllables.length) {
      const bgText = joinSyllables(bgSyllables);
      const bgTime = Math.min(...bgSyllables.map(syl => syl.startMs));
      if (bgText) {
        lines.push({
          timeMs: bgTime,
          text: bgText,
          words: bgSyllables,
          background: true,
          agent,
        });
      }
    }
  }
  return lines.sort((a, b) => a.timeMs - b.timeMs);
}

async function fetchLyricsPlusLyrics(meta) {
  const bases = [
    'https://lyricsplus.binimum.org',
    'https://lyricsplus.atomix.one',
    'https://lyricsplus.prjktla.my.id',
    'https://lyricsplus-seven.vercel.app',
  ];
  for (const base of bases) {
    try {
      const response = await axios.get(`${base}/v2/lyrics/get`, {
        params: { title: meta.title, artist: meta.artist, duration: Math.round(meta.duration), ...(meta.album ? { album: meta.album } : {}) },
        timeout: 15000,
        maxContentLength: 8 * 1024 * 1024,
        headers: { 'User-Agent': 'Mozilla/5.0', Accept: 'application/json' },
        validateStatus: status => status < 500,
      });
      if (response.status !== 200) continue;
      const lines = parseLyricsPlusLines(response.data);
      if (lines.length < 4) continue;
      return { lines, provider: 'LyricsPlus', wordSynced: lines.some(line => line.words.length > 0), approximate: false };
    } catch { /* try the next mirror */ }
  }
  return null;
}

async function fetchLrcLibLyrics(meta) {
  const variants = [
    { track_name: meta.title, artist_name: meta.artist },
    { q: `${meta.artist} ${meta.title}` },
    { track_name: meta.title },
  ];
  let tracks = [];
  for (const params of variants) {
    try {
      const response = await axios.get('https://lrclib.net/api/search', {
        params, timeout: 12000, maxContentLength: 5 * 1024 * 1024,
        headers: { 'User-Agent': 'WhatsApp-lyric-video-bot/1.0 (+https://github.com)' },
      });
      if (Array.isArray(response.data) && response.data.length) { tracks = response.data; break; }
    } catch { /* try the next search form */ }
  }
  const titleKey = normalized(meta.title);
  const artistKey = normalized(meta.artist);
  const ranked = tracks.filter(track => track.syncedLyrics || track.plainLyrics).map(track => {
    const candidateTitle = normalized(track.trackName || '');
    const candidateArtist = normalized(track.artistName || '');
    const durationDelta = Math.abs(Number(track.duration || meta.duration) - meta.duration);
    let score = 0;
    if (candidateTitle === titleKey) score += 100;
    else if (candidateTitle.includes(titleKey) || titleKey.includes(candidateTitle)) score += 55;
    if (candidateArtist === artistKey) score += 45;
    else if (candidateArtist && artistKey && (candidateArtist.includes(artistKey) || artistKey.includes(candidateArtist))) score += 20;
    score -= Math.min(durationDelta, 180) * 0.8;
    if (track.syncedLyrics) score += 15;
    return { track, score, durationDelta };
  }).sort((a, b) => b.score - a.score);

  const best = ranked.find(item => item.durationDelta <= 12) || ranked[0];
  if (!best) return null;
  const { track } = best;
  let lines = track.syncedLyrics ? parseLrc(track.syncedLyrics) : [];
  let approximate = false;
  if (lines.length < 4 && track.plainLyrics) {
    const plain = String(track.plainLyrics).split(/\r?\n/).map(text => text.trim()).filter(Boolean);
    if (plain.length >= 4) {
      const usableDuration = Math.max(1000, meta.duration * 1000 - 8000);
      lines = plain.map((text, index) => ({ timeMs: 4000 + Math.round(usableDuration * index / Math.max(plain.length - 1, 1)), text, words: [], background: false, agent: null }));
      approximate = true;
    }
  }
  if (lines.length < 4) return null;
  return { lines, provider: 'LRCLIB', wordSynced: false, approximate };
}

/**
 * BetterLyrics' QQ provider (`/qq/getLyrics`) returns QQ Music QRC — word-by-word — as an
 * escaped XML document whose `<Lyric_1 LyricContent="…">` attribute holds the payload. It is
 * a different endpoint from `/getLyrics` (which returns line-level TTML), so it is what makes
 * a track the default provider only knows line-by-line still come out word-synced.
 */
async function fetchQqLyrics(meta) {
  try {
    const headers = { 'User-Agent': 'Mozilla/5.0', Accept: 'application/json' };
    if (process.env.BETTERLYRICS_API_KEY) headers['X-API-Key'] = process.env.BETTERLYRICS_API_KEY;
    const response = await axios.get('https://lyrics-api.boidu.dev/qq/getLyrics', {
      params: { s: meta.title, a: meta.artist, d: Math.round(meta.duration), ...(meta.album ? { al: meta.album } : {}) },
      timeout: 20000,
      headers,
      maxContentLength: 8 * 1024 * 1024,
      validateStatus: status => status < 500,
    });
    if (response.status !== 200) return null;
    const xml = String(response.data?.lyrics || '');
    const match = xml.match(/LyricContent="([\s\S]*?)"\s*\/?>/);
    if (!match) return null;
    const lines = filterHeaderLines(parseQrc(unescapeEntities(match[1])), meta);
    if (lines.length < 4) return null;
    return { lines, provider: 'QQ Music (QRC)', wordSynced: lines.some(line => line.words.length > 0), approximate: false };
  } catch {
    return null;
  }
}

/**
 * Resolves a NetEase song id from title/artist, scoring candidates so a loose match cannot win.
 * Shared by the YRC lyric path and the romanization path (they hit the same search API).
 */
/**
 * Resolves a ranked list of NetEase songs for the track.
 *
 * Two problems make a single lookup unreliable. (1) NetEase's search returns several
 * near-identical entries (same title/artist/duration) and only some carry the payload we want
 * (YRC word timing, `romalrc` romanization). (2) YouTube metadata often appends a romanized or
 * English subtitle to the title ("怪獣の花唄 - Kaiju no Hanauta"), and searching that full string
 * makes NetEase rank cover/karaoke entries instead of the original. So we query both the full
 * title and the primary title (the part before a " - " subtitle) and merge the candidates.
 */
async function searchNetEaseSongs(meta) {
  const fullTitle = String(meta.title || '').trim();
  const primaryTitle = fullTitle.split(/\s+[-\u2013\u2014]\s+/)[0].trim() || fullTitle;
  const titleKeys = [...new Set([normalized(fullTitle), normalized(primaryTitle)].filter(Boolean))];
  const artistKey = normalized(meta.artist);

  const queries = [...new Set([
    `${fullTitle} ${meta.artist}`.trim(),
    `${primaryTitle} ${meta.artist}`.trim(),
  ].filter(Boolean))];

  const seen = new Set();
  const songs = [];
  for (const query of queries) {
    try {
      const search = await axios.get('https://music.163.com/api/search/get', {
        params: { s: query, type: 1, limit: 8, offset: 0 },
        timeout: 15000,
        headers: { 'User-Agent': 'Mozilla/5.0', Referer: 'https://music.163.com/' },
        maxContentLength: 5 * 1024 * 1024,
        validateStatus: status => status < 500,
      });
      if (search.status !== 200) continue;
      const found = search.data?.result?.songs;
      if (!Array.isArray(found)) continue;
      for (const song of found) {
        if (!song?.id || seen.has(song.id)) continue;
        seen.add(song.id);
        songs.push(song);
      }
    } catch {
      // One failed query should not sink the lookup; try the next one.
    }
  }
  if (!songs.length) return null;

  const ranked = songs.map(song => {
    const name = normalized(song.name || '');
    const artist = normalized((song.artists || song.ar || []).map(a => a.name).join(' '));
    const rawDuration = Number(song.duration || song.dt || 0);
    const duration = rawDuration > 1000 ? rawDuration / 1000 : rawDuration;
    const delta = Math.abs(duration - meta.duration);
    let score = 0;
    for (const key of titleKeys) {
      if (name === key) score = Math.max(score, 100);
      else if (name.includes(key) || key.includes(name)) score = Math.max(score, 55);
    }
    if (artist === artistKey) score += 45;
    else if (artist && artistKey && (artist.includes(artistKey) || artistKey.includes(artist))) score += 20;
    score -= Math.min(delta, 180) * 0.8;
    return { song, score };
  }).sort((a, b) => b.score - a.score);
  // Return the whole ranked list: the caller walks it until it finds an entry that actually has
  // the payload it needs (YRC word timing / romalrc romanization).
  return ranked.map(entry => entry.song);
}

/** Fetches a NetEase song's lyric payload (LRC/YRC/translation/romanization), or null. */
async function fetchNetEaseLyricPayload(songId) {
  const lyric = await axios.get('https://music.163.com/api/song/lyric', {
    params: { id: songId, lv: -1, kv: -1, tv: -1, yv: -1, rv: -1 },
    timeout: 15000,
    headers: { 'User-Agent': 'Mozilla/5.0', Referer: 'https://music.163.com/' },
    maxContentLength: 5 * 1024 * 1024,
    validateStatus: status => status < 500,
  });
  if (lyric.status !== 200) return null;
  return lyric.data || null;
}

/**
 * NetEase Cloud Music YRC — word-by-word. The song id is resolved through the public search
 * API first; `yv=-1` then asks the lyric API for the YRC payload (`yrc.lyric`). NetEase has
 * no API-key gate, so this is the free word-sync fallback when BetterLyrics' QQ provider is
 * rate-limited.
 */
async function fetchNetEaseLyrics(meta) {
  try {
    const songs = await searchNetEaseSongs(meta);
    if (!Array.isArray(songs) || !songs.length) return null;
    // Walk the ranked candidates: several NetEase entries can share the same title/artist/duration
    // while only some carry YRC (word timing). Try each until one yields a usable payload.
    let lrcFallback = null;
    for (const song of songs.slice(0, 5)) {
      if (!song?.id) continue;
      const data = await fetchNetEaseLyricPayload(song.id);
      if (!data) continue;
      const yrc = data?.yrc?.lyric;
      if (typeof yrc === 'string' && yrc.trim()) {
        const lines = filterHeaderLines(parseYrc(yrc), meta);
        if (lines.length >= 4) {
          return { lines, provider: 'NetEase (YRC)', wordSynced: lines.some(line => line.words.length > 0), approximate: false };
        }
      }
      // No YRC for this candidate: remember its line-level LRC, but keep looking for a word-synced one.
      if (!lrcFallback) {
        const lrc = data?.lrc?.lyric;
        if (typeof lrc === 'string' && lrc.trim()) {
          const lines = filterHeaderLines(parseLrc(lrc), meta);
          if (lines.length >= 4) lrcFallback = { lines, provider: 'NetEase (LRC)', wordSynced: false, approximate: false };
        }
      }
    }
    return lrcFallback;
  } catch {
    return null;
  }
}

/**
 * Line-level romanization of a track, from NetEase's `romalrc` payload (the only free provider
 * that romanizes; BetterLyrics/QQ/LyricsPlus do not). It is a plain LRC document, so it is
 * parsed with the LRC parser and rendered as a line-level sweep — there is no word timing.
 *
 * Only attempted for tracks whose original lyrics are in a non-Latin script: romanizing an
 * already-Latin song is pointless, and the extra lookup would be wasted.
 */
async function fetchRomanizedLyrics(meta) {
  try {
    const songs = await searchNetEaseSongs(meta);
    if (!Array.isArray(songs) || !songs.length) return null;
    // Walk the ranked candidates: identical-looking entries may differ in whether they carry the
    // `romalrc` romanization payload. Try each until one actually has romanized lines.
    for (const song of songs.slice(0, 5)) {
      if (!song?.id) continue;
      const data = await fetchNetEaseLyricPayload(song.id);
      const roma = data?.romalrc?.lyric;
      if (typeof roma !== 'string' || !roma.trim()) continue;
      const lines = filterHeaderLines(parseLrc(roma), meta);
      if (lines.length < 4) continue;
      return { lines, provider: 'NetEase (romaji/romanized)', wordSynced: false, romanized: true, approximate: false };
    }
    return null;
  } catch {
    return null;
  }
}

/** True when any line's text is written in a script that benefits from romanization. */
function needsRomanization(lines) {
  return Array.isArray(lines) && lines.some(line => NON_LATIN_SCRIPT_RE.test(line.text || ''));
}

async function getLyrics(meta) {
  // Word-sync first. Each provider is tried in turn and the first word-synced result wins;
  // a line-level result is only kept as a fallback so the word-sync providers still get a
  // chance when the default endpoint answers with line-level TTML (which it often does).
  const lineLevel = [];
  const consider = result => {
    if (!result) return null;
    if (result.wordSynced) return result;
    lineLevel.push(result);
    return null;
  };

  const providers = [
    fetchBetterLyrics,   // BetterLyrics TTML (word-sync when it carries spans)
    fetchQqLyrics,       // BetterLyrics QQ provider (QRC word-sync)
    fetchLyricsPlusLyrics, // LyricsPlus JSON (word-sync when it carries a syllabus)
    fetchNetEaseLyrics,  // NetEase YRC (free word-sync), LRC as its own fallback
    fetchLrcLibLyrics,   // LRCLIB (line-level)
  ];
  for (const provider of providers) {
    const hit = consider(await provider(meta));
    if (hit) return hit;
  }
  if (lineLevel.length) return lineLevel[0];
  throw new Error('Lirik tersinkronisasi tidak ditemukan. Coba judul + nama artis yang lebih spesifik.');
}

/**
 * Resolves the lyrics to render, romanization-as-a-secondary-line.
 *
 * The original lyrics are always kept — including their word timing — and romanization is
 * attached as a parallel `romanizedLines` array (same length/index as `lyrics.lines`) so the
 * renderer can draw it as a small secondary line under each lyric while the karaoke per-word
 * wipe keeps running on the original. Romanization is generated offline first; NetEase's
 * `romalrc` is used only as a fallback for scripts the offline engine does not cover (Arabic,
 * Thai, Hebrew…). `warnings` records why the caller may want to confirm before rendering.
 *
 * Returns `{ lyrics, romanizedLines, romanizedSource, warnings, romanized }`, where `lyrics` is
 * a getLyrics-shaped result (the original, untouched).
 */
async function resolveLyrics(meta) {
  const original = await getLyrics(meta);
  const warnings = [];

  // Romanization is strictly restricted to Japanese, Korean, and Chinese (CJK).
  // For all other languages, romanizedLines remains null so no romanization is displayed.
  const isCJK = needsRomanization(original.lines);
  let romanizedLines = null;
  let romanizedSource = null;

  if (isCJK) {
    // 1) Offline romanization (primary: Kuromoji for Japanese, Hangul romanizer for Korean, Pinyin for Chinese).
    romanizedLines = await romanizeLyrics(original.lines).catch(() => null);
    if (romanizedLines) romanizedSource = 'offline';

    // 2) NetEase `romalrc` fallback (only for CJK when offline engine found nothing).
    if (!romanizedLines) {
      const netease = await fetchRomanizedLyrics(meta).catch(() => null);
      if (netease) {
        romanizedLines = alignRomanizedToLines(original.lines, netease.lines);
        if (romanizedLines) romanizedSource = 'netease';
      }
    }
  }

  const romanized = Boolean(romanizedLines);
  if (!original.wordSynced) {
    warnings.push({
      code: 'no-wordsync',
      message: 'Lirik lagu ini tidak word-sync (highlight per kata tidak tersedia).',
    });
  }

  return { lyrics: original, romanizedLines, romanizedSource, warnings, romanized };
}

/**
 * Maps each original line to the closest NetEase `romalrc` line by timestamp (tolerance ±2.5 s),
 * producing a `string|null` array aligned with `lines` (the shape `romanizeLyrics` returns). A
 * line with no romanized counterpart becomes `null`. Returns `null` when fewer than half of the
 * original lines could be matched, so a poorly-aligned payload is discarded rather than shown.
 */
function alignRomanizedToLines(lines, romanLines) {
  if (!Array.isArray(lines) || !lines.length || !Array.isArray(romanLines) || !romanLines.length) return null;
  const TOLERANCE_MS = 2500;
  const used = new Set();
  const out = lines.map(line => {
    let best = -1;
    let bestDelta = Infinity;
    for (let i = 0; i < romanLines.length; i++) {
      if (used.has(i)) continue;
      const delta = Math.abs((romanLines[i].timeMs ?? 0) - (line.timeMs ?? 0));
      if (delta <= TOLERANCE_MS && delta < bestDelta) { best = i; bestDelta = delta; }
    }
    if (best === -1) return null;
    used.add(best);
    const text = (romanLines[best].text || '').trim();
    return text ? text : null;
  });
  const filled = out.filter(Boolean).length;
  return filled >= lines.length / 2 ? out : null;
}

function wrapPlainText(ctx, text, maxWidth, font) {
  ctx.font = font;
  const words = String(text).split(/\s+/).filter(Boolean);
  const rows = [];
  let current = '';
  for (const word of words) {
    const candidate = current ? `${current} ${word}` : word;
    if (current && ctx.measureText(candidate).width > maxWidth) { rows.push(current); current = word; }
    else current = candidate;
  }
  if (current) rows.push(current);
  return rows.length ? rows : [''];
}

/**
 * The time window a line-level lyric (no word timing) is swept across.
 *
 * AMLL renders such a line as a single word spanning the whole line and lets its mask
 * animator run one linear sweep across it, which is what gives Spotify's per-line fill.
 * The sweep runs from the line's start to the next line's start so it finishes exactly as
 * the next line takes over; when there is no next line (or the pause is long) a
 * length-based guess is used so a long interlude does not make the fill crawl.
 */
function lineSweepWindow(line, nextLine, durationMs) {
  const start = line.timeMs;
  const nextStart = nextLine?.timeMs;
  const guess = start + Math.min(
    LINE_LEVEL_MAX_MS,
    Math.max(LINE_LEVEL_MIN_MS, (line.text || '').length * LINE_LEVEL_PER_CHAR_MS),
  );
  let end = guess;
  if (nextStart != null && nextStart > start) {
    end = Math.min(nextStart, start + LINE_LEVEL_MAX_MS);
  } else if (durationMs) {
    end = Math.min(end, durationMs);
  }
  if (end - start < LINE_LEVEL_MIN_MS) end = start + LINE_LEVEL_MIN_MS;
  return { startMs: start, endMs: end };
}

/**
 * Lays a line out into rows of word groups. Each group is the concatenated syllables of
 * one word, so a word split across syllables ("fa" + "llin'") is drawn as a single
 * unbroken run — that is what keeps the karaoke wipe from opening a gap inside a word.
 *
 * Each group also carries `segments`: the character spans of its individual syllables with
 * their own times, so a word sung in more than one syllable ("fa" then "llin'") can lift each
 * syllable on its own instead of the whole word rising at once.
 *
 * `romanText` (optional) is the line's romanization; it is laid out as a smaller secondary
 * block under the main rows. `rowCount` stays the count of the *main* rows (the karaoke and
 * active-line logic key off it); the romanization adds its own `romanRows`/`romanRowCount`
 * and is folded into `blockHeight`, which the stack layout uses for spacing.
 */
function layoutLine(ctx, text, syllables, romanText = null) {
  ctx.font = resolveFont(text, LYRIC_FONT_SIZE, LYRIC_FONT_WEIGHT);
  const font = ctx.font;
  const groups = syllables?.length
    ? groupSyllablesIntoWords(text, syllables)
    : (text.match(/\S+/gu) || []).map(word => ({ text: word, startMs: null, endMs: null, syllables: null }));
  const space = ctx.measureText(' ').width;
  const rows = [];
  let row = [];
  let width = 0;
  for (const group of groups) {
    const groupWidth = ctx.measureText(group.text).width;
    const gap = row.length ? space : 0;
    if (row.length && width + gap + groupWidth > LYRIC_MAX_WIDTH) { rows.push(row); row = []; width = 0; }
    const actualGap = row.length ? space : 0;
    const x = width + actualGap;
    row.push({
      text: group.text,
      syllables: group.syllables,
      segments: buildSegments(ctx, group, x, groupWidth),
      startMs: group.startMs,
      endMs: group.endMs,
      x,
      width: groupWidth,
    });
    width += actualGap + groupWidth;
  }
  if (row.length) rows.push(row);
  // Each row also keeps its words joined by a space so an inactive line can be drawn with a
  // single fillText; node-canvas' fillText is the dominant per-frame cost.
  for (const row of rows) row.text = row.map(item => item.text).join(' ');
  const mainRows = rows.length ? rows : [[]];

  const roman = romanText ? layoutRomanRows(ctx, romanText) : { font: null, rows: [] };
  const blockHeight = mainRows.length * LYRIC_ROW_HEIGHT
    + (roman.rows.length ? LYRIC_ROMAN_GAP + roman.rows.length * LYRIC_ROMAN_ROW_HEIGHT : 0);
  return {
    font,
    rows: mainRows,
    rowCount: Math.max(rows.length, 1),
    romanFont: roman.font,
    romanRows: roman.rows,
    romanRowCount: roman.rows.length,
    blockHeight,
  };
}

/**
 * Wraps a romanized line into left-aligned rows at the smaller romanization size. It carries no
 * syllable timing (romanization is never karaoke'd) — only `text`/`x`/`width`, which is what the
 * strip pre-render and the static secondary-line draw need.
 */
function layoutRomanRows(ctx, text) {
  const font = resolveFont(text, LYRIC_ROMAN_FONT_SIZE, 'normal');
  ctx.font = font;
  const words = String(text).split(/\s+/).filter(Boolean);
  const space = ctx.measureText(' ').width;
  const rows = [];
  let row = [];
  let width = 0;
  for (const word of words) {
    const wordWidth = ctx.measureText(word).width;
    const gap = row.length ? space : 0;
    if (row.length && width + gap + wordWidth > LYRIC_MAX_WIDTH) { rows.push(row); row = []; width = 0; }
    const actualGap = row.length ? space : 0;
    const x = width + actualGap;
    row.push({ text: word, x, width: wordWidth });
    width += actualGap + wordWidth;
  }
  if (row.length) rows.push(row);
  for (const r of rows) r.text = r.map(item => item.text).join(' ');
  return { font, rows };
}

/**
 * Splits a word group into the character spans its syllables occupy, measured in pixels, so the
 * lift can be applied per syllable. A single-syllable word yields one span covering the word.
 */
function buildSegments(ctx, group, x, groupWidth) {
  const syllables = (group.syllables || []).filter(s => s.text && s.text.trim());
  if (syllables.length <= 1) {
    const only = syllables[0] || { startMs: group.startMs, endMs: group.endMs };
    return [{ startMs: only.startMs, endMs: only.endMs, x, width: groupWidth }];
  }
  const totalChars = syllables.reduce((sum, s) => sum + s.text.trim().length, 0) || 1;
  // Prefix widths of the partial text, so each syllable's span is measured rather than guessed.
  const prefixes = [''];
  for (const s of syllables) prefixes.push(prefixes[prefixes.length - 1] + s.text.trim());
  const charWidth = prefixes.map(p => ctx.measureText(p).width);
  const scale = groupWidth / Math.max(1, charWidth[charWidth.length - 1]);
  const segments = [];
  for (let i = 0; i < syllables.length; i++) {
    const left = charWidth[i] * scale;
    const right = charWidth[i + 1] * scale;
    segments.push({
      startMs: syllables[i].startMs,
      endMs: syllables[i].endMs,
      x: x + left,
      width: Math.max(1, right - left),
    });
  }
  return segments;
}

/**
 * The line's rows rendered as a soft white glow, pre-blurred once so the per-frame karaoke
 * never pays for a blur. The blur radius doubles as the "distance" blur for inactive lines,
 * so a single pre-render serves both the karaoke glow and the depth blur.
 *
 * `ops` are absolute draw operations `{ text, x, font, baseline, alpha? }` whose `baseline` is
 * relative to the line's ink top (row 0's ink top = 0). Baking the romanization into the same
 * strip is what lets an inactive line keep its small secondary line through the blur.
 *
 * `opacity` bakes the line's own alpha in, which is what lets a background vocal be drawn as a
 * pre-blurred strip while still carrying its dimmer opacity (the Android player renders
 * background lines at 0.4, not 1.0).
 */
async function renderStrip(ops, contentHeight, blurRadius = 4, opacity = 1) {
  const margin = 12;
  const height = contentHeight + margin * 2;
  const canvas = createCanvas(WIDTH, height);
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, WIDTH, height);
  ctx.textBaseline = 'alphabetic';
  ctx.textAlign = 'left';
  for (const op of ops) {
    const alpha = opacity * (op.alpha ?? 1);
    if (alpha <= 0) continue;
    ctx.font = op.font;
    ctx.fillStyle = alpha >= 1 ? '#ffffff' : `rgba(255,255,255,${alpha})`;
    ctx.fillText(op.text, LYRIC_LEFT + op.x, margin + op.baseline);
  }
  const blurred = blurRadius >= 0.3
    ? await sharp(canvas.toBuffer('image/png')).blur(blurRadius).png().toBuffer()
    : canvas.toBuffer('image/png');
  return { image: await loadImage(blurred), margin, height };
}

/** Every draw op for a laid-out line: the main rows plus its romanization secondary rows. */
function lineDrawOps(laid) {
  const ascent = LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const ops = [];
  laid.rows.forEach((row, rowIndex) => {
    const baseline = ascent + rowIndex * LYRIC_ROW_HEIGHT;
    for (const item of row) ops.push({ text: item.text, x: item.x, font: laid.font, baseline });
  });
  const romanTop = laid.rows.length * LYRIC_ROW_HEIGHT + LYRIC_ROMAN_GAP;
  const romanAscent = LYRIC_ROMAN_FONT_SIZE * LYRIC_ASCENT_RATIO;
  laid.romanRows.forEach((row, rowIndex) => {
    const baseline = romanTop + romanAscent + rowIndex * LYRIC_ROMAN_ROW_HEIGHT;
    for (const item of row) ops.push({ text: item.text, x: item.x, font: laid.romanFont, baseline, alpha: LYRIC_ROMAN_ALPHA });
  });
  return ops;
}

/** Only the main rows, for the karaoke glow (the romanization never glows). */
function mainRowOps(laid) {
  const ascent = LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const ops = [];
  laid.rows.forEach((row, rowIndex) => {
    const baseline = ascent + rowIndex * LYRIC_ROW_HEIGHT;
    for (const item of row) ops.push({ text: item.text, x: item.x, font: laid.font, baseline });
  });
  return ops;
}

/** Only the romanization rows, for the secondary line's held-syllable glow strip. */
function romanRowOps(laid) {
  if (!laid.romanRows?.length || !laid.romanFont) return [];
  const romanTop = laid.rows.length * LYRIC_ROW_HEIGHT + LYRIC_ROMAN_GAP;
  const romanAscent = LYRIC_ROMAN_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const ops = [];
  laid.romanRows.forEach((row, rowIndex) => {
    const baseline = romanTop + romanAscent + rowIndex * LYRIC_ROMAN_ROW_HEIGHT;
    for (const item of row) ops.push({ text: item.text, x: item.x, font: laid.romanFont, baseline });
  });
  return ops;
}

function formatTime(ms) {
  const total = Math.max(0, Math.floor(ms / 1000));
  return `${Math.floor(total / 60)}:${String(total % 60).padStart(2, '0')}`;
}

// The reference player eases its scroll with FastOutSlowIn (Material motion); a cubic
// Bezier with the same control points reproduces the slow start and long settle.
function fastOutSlowIn(t) {
  const x1 = 0.4, y1 = 0.0, x2 = 0.2, y2 = 1.0;
  const sample = (a, b, u) => {
    const v = 1 - u;
    return 3 * v * v * u * a + 3 * v * u * u * b + u * u * u;
  };
  let lo = 0, hi = 1, u = t;
  for (let i = 0; i < 24; i++) {
    const x = sample(x1, x2, u);
    if (Math.abs(x - t) < 1e-4) break;
    if (x < t) lo = u; else hi = u;
    u = (lo + hi) / 2;
  }
  return sample(y1, y2, u);
}

function easeOutCubic(t) {
  return 1 - Math.pow(1 - Math.max(0, Math.min(1, t)), 3);
}

/**
 * Three dots that fill one by one and breathe, shown during an instrumental gap the way the
 * reference player does, so a long pause takes focus instead of leaving a stale line lit.
 */
function drawInterludeDots(ctx, y, progress, elapsedMs, alpha) {
  const breathe = 1 + 0.12 * Math.sin(elapsedMs / 250);
  const fade = Math.max(0, Math.min(1, Math.min(progress, 1 - progress) * 8));
  for (let k = 0; k < 3; k++) {
    const fill = Math.max(0, Math.min(1, progress * 3 - k));
    ctx.save();
    ctx.globalAlpha = alpha * (0.3 + 0.7 * fill) * fade;
    ctx.fillStyle = '#FFFFFF';
    ctx.beginPath();
    ctx.arc(INTERLUDE_DOT_X + INTERLUDE_DOT_RADIUS + k * INTERLUDE_DOT_STEP, y, INTERLUDE_DOT_RADIUS * breathe, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
  }
}

function roundedRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y); ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r); ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
  ctx.lineTo(x + r, y + h); ctx.quadraticCurveTo(x, y + h, x, y + h - r);
  ctx.lineTo(x, y + r); ctx.quadraticCurveTo(x, y, x + r, y); ctx.closePath();
}

/**
 * Pre-renders the static header (artwork thumbnail + title + artist) once. Drawing a
 * 600px cover through a clip and a text shadow every frame costs ~35ms, so it is baked
 * into a small canvas the render loop only has to blit.
 */
function buildHeader(cover, meta) {
  const canvas = createCanvas(WIDTH, 160);
  const ctx = canvas.getContext('2d');
  ctx.save();
  roundedRect(ctx, 52, 72, 82, 82, 12); ctx.clip();
  const scale = Math.max(82 / cover.width, 82 / cover.height);
  const w = cover.width * scale, h = cover.height * scale;
  ctx.drawImage(cover, 52 + (82 - w) / 2, 72 + (82 - h) / 2, w, h);
  ctx.restore();
  // Title / artist sizes measured against the reference video (≈20px title, ≈18px artist).
  ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
  ctx.fillStyle = '#FFFFFF'; ctx.font = resolveFont(meta.title, 20, 'bold'); ctx.shadowColor = 'rgba(0,0,0,.18)'; ctx.shadowBlur = 5;
  ctx.fillText(meta.title.slice(0, 46), 154, 103, 500);
  ctx.shadowBlur = 0; ctx.fillStyle = 'rgba(255,255,255,.78)'; ctx.font = resolveFont(meta.artist, 18, 'normal');
  ctx.fillText(meta.artist.slice(0, 48), 154, 128, 500);
  return canvas;
}

/**
 * Builds the ordered list the renderer walks: one item per lyric line plus an interlude
 * item for every gap worth focusing on (the intro, a blank LRC line, or a pause of 4.5s+
 * after a word-synced line). Mirrors the Android `lyricItems`.
 */
function buildItems(lines) {
  const items = [];
  const nextMain = index => {
    for (let i = index + 1; i < lines.length; i++) if (!lines[i].background) return lines[i].timeMs;
    return null;
  };
  const intro = nextMain(-1);
  if (intro != null && intro >= GAP_MIN_MS) items.push({ gap: true, startMs: GAP_LEAD_MS, endMs: intro - GAP_LEAD_MS });
  lines.forEach((line, index) => {
    const next = line.background ? null : nextMain(index);
    if (!line.text || !line.text.trim()) {
      if (next != null && next - line.timeMs >= BLANK_GAP_MIN_MS) items.push({ gap: true, startMs: line.timeMs, endMs: next - GAP_LEAD_MS });
      return;
    }
    items.push({ gap: false, line: index, startMs: line.timeMs });
    const wordEnd = line.words?.length ? line.words[line.words.length - 1].endMs : null;
    if (wordEnd != null && next != null && next - wordEnd >= GAP_MIN_MS) {
      items.push({ gap: true, startMs: wordEnd + GAP_LEAD_MS, endMs: next - GAP_LEAD_MS });
    }
  });
  return items;
}

/**
 * Lines being sung at [elapsedMs]: a line lights from its start until its last word ends
 * (or the next line starts when it has no word timing), so a finished line dims and duet
 * lines can light together. An active background line also lights the main line it belongs
 * to. Mirrors the Android `activeLines`.
 */
function activeLines(lines, elapsedMs) {
  const active = new Set();
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.timeMs > elapsedMs) break;
    const end = line.words?.length ? line.words[line.words.length - 1].endMs : (lines[i + 1]?.timeMs ?? Number.MAX_SAFE_INTEGER);
    if (elapsedMs <= end && line.text.trim()) active.add(i);
  }
  const hasWordTimings = lines.some(line => line.words?.length);
  if (!hasWordTimings && active.size > 1) {
    const mains = [...active].filter(i => !lines[i].background);
    if (mains.length > 1) {
      const latest = Math.max(...mains.map(i => lines[i].timeMs));
      for (const i of mains) if (lines[i].timeMs < latest) active.delete(i);
    }
  }
  for (const i of [...active]) {
    if (!lines[i].background) continue;
    for (let j = i - 1; j >= 0; j--) if (!lines[j].background) { active.add(j); break; }
  }
  return active;
}

/** The main line a background line belongs to, if any. */
function mainLineOf(lines, index) {
  for (let i = index - 1; i >= 0; i--) if (!lines[i].background) return i;
  return null;
}

/**
 * Draws the karaoke wipe for one word group.
 *
 * The wipe itself is word-global (the white front sweeps across the whole word), but the lift is
 * applied **per syllable**: a word sung in two syllables ("fa" then "llin'") raises its first
 * half while the second is still being sung, and only then raises the second half. That mirrors
 * the Android player, whose `words` list is syllable-level and lifts each entry on its own.
 *
 * The word's pending copy is erased first, exactly like the Android player does with
 * `BlendMode.Clear` inside `clipRect(wordBox)` before it redraws the word lifted and lit.
 * Without that erase two artefacts appear: the wipe composites on top of the pending text (so a
 * started word lands at ≈0.62 alpha while its neighbours sit at 0.38 and the word looks like it
 * "went white"), and the lifted copy is drawn over the un-erased one, which makes the front look
 * doubled.
 *
 * The gradient edge is a fixed width in em (`LYRIC_WIPE_EM`), not a fraction of the word, so the
 * front sweeps letter by letter instead of fading the whole word at once.
 *
 * The held-syllable glow is applied **per syllable** and clipped to the wipe front, so only the
 * part of a syllable that has actually been sung glows: a long note lights up as it is held
 * without lighting the letters still to come, and a held syllable cannot light the syllables
 * beside it in the same word.
 */
function drawWordWipe(ctx, item, top, baselineY, lit, glow, elapsedMs, lineAlpha = 1) {
  if (lit <= 0) return;
  const x = LYRIC_LEFT + item.x;
  const width = Math.max(1, item.width);
  const edge = Math.max(1, LYRIC_WIPE_EM * LYRIC_FONT_SIZE);
  const pendingAlpha = lineAlpha * LYRIC_PENDING_ALPHA;
  const segments = item.segments?.length
    ? item.segments
    : [{ x: item.x, width, startMs: item.startMs, endMs: item.endMs }];
  // Absolute x of the wipe front for the whole word. It is reused both for the fill gradient
  // and to clip the glow, so the lit front and the glow front can never disagree.
  const front = x - edge + lit * (width + 2 * edge);

  // Word-level gradient: the character positions are absolute, so each syllable clip can reuse
  // it and the lit front stays continuous across the syllable boundary. The lit end is the line's
  // own alpha (1 for a main line, 0.4 for a background vocal) and the trailing end is the pending
  // level, so the wipe reads as "filling in" the word.
  let fill = `rgba(255,255,255,${lineAlpha})`;
  if (lit < 1) {
    fill = ctx.createLinearGradient(front - edge, baselineY, front + edge, baselineY);
    fill.addColorStop(0, `rgba(255,255,255,${lineAlpha})`);
    fill.addColorStop(1, `rgba(255,255,255,${pendingAlpha})`);
  }

  for (const segment of segments) {
    const segX = LYRIC_LEFT + segment.x;
    const segWidth = Math.max(1, segment.width);
    const start = segment.startMs ?? item.startMs;
    const end = Math.max((start ?? 0) + 1, segment.endMs ?? item.endMs);
    // Eased out over max(250ms, the syllable's own duration), like the Android lift.
    const liftT = start == null ? 1 : Math.max(0, Math.min(1, (elapsedMs - start) / Math.max(250, end - start)));
    const lift = -LYRIC_WORD_LIFT * easeOutCubic(liftT);
    // The glyph box of this row: ink top is `ascent` above the baseline, ink bottom ~12px below.
    const inkTop = baselineY - LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
    const inkBottom = baselineY + LYRIC_FONT_SIZE * 0.3;
    // Held-syllable glow: only a syllable sung for over a second glows, peaking mid-syllable.
    // Computed from this syllable's own timing so a held syllable lights only itself.
    const duration = end - (start ?? 0);
    const fraction = start == null ? 1 : Math.max(0, Math.min(1, (elapsedMs - start) / (end - start)));
    const glowAlpha = duration > 1000 && fraction > 0 && fraction < 1
      ? Math.sin(fraction * Math.PI) * LYRIC_HELD_GLOW_SCALE
      : 0;

    ctx.save();
    // Erase this syllable's pending copy, with headroom above the ink for the lift. The box is
    // capped to this row's ink (plus clearance) so it can never bite into the row above/below.
    ctx.clearRect(segX - 1, inkTop - LYRIC_LIFT_CLEARANCE, segWidth + 2, (inkBottom - inkTop) + LYRIC_LIFT_CLEARANCE + 2);
    // Clip to the syllable so the gradient cannot tint the neighbouring syllable.
    ctx.beginPath();
    ctx.rect(segX - 1, inkTop - LYRIC_LIFT_CLEARANCE, segWidth + 2, (inkBottom - inkTop) + LYRIC_LIFT_CLEARANCE + 2);
    ctx.clip();
    if (lift) ctx.translate(0, lift);

    if (glow && glowAlpha > 0.01) {
      // The glow is clipped to this row's ink band with only a small pad, and horizontally to
      // the wipe front: the letters before the front glow, the letters after it do not. A taller
      // clip would spill the glow onto the neighbouring lyric row, which reads as a reflection.
      const glowLeft = segX - 3;
      const glowRight = Math.min(segX + segWidth, front) + 3;
      if (glowRight > glowLeft) {
        ctx.save();
        ctx.beginPath();
        ctx.rect(glowLeft, inkTop - LYRIC_GLOW_PAD, glowRight - glowLeft, (inkBottom - inkTop) + LYRIC_GLOW_PAD * 2);
        ctx.clip();
        ctx.globalAlpha = glowAlpha;
        ctx.drawImage(glow.image, 0, top - glow.margin);
        ctx.restore();
      }
    }

    ctx.fillStyle = fill;
    ctx.fillText(item.text, x, baselineY);
    ctx.restore();
  }
}

/**
 * Draws the Spotify-style per-line fill for a line that has no word timing.
 *
 * The whole line is treated as one continuous sweep: rows are concatenated in reading order
 * and a single front moves left-to-right across them over the line's window, so a wrapped
 * line fills across its first row and then its second, exactly like one long word. A soft
 * gradient edge of the same fixed width as the karaoke wipe leads the front, and the pending
 * copy underneath keeps the unsung text readable.
 */
function drawLineSweep(ctx, laid, top, progress, glow, lineAlpha = 1) {
  if (progress <= 0) return;
  const ascent = LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const edge = Math.max(1, LYRIC_WIPE_EM * LYRIC_FONT_SIZE);
  const pendingAlpha = lineAlpha * LYRIC_PENDING_ALPHA;

  // Total ink width of the line in reading order, so the front's position is continuous
  // across a row break.
  const rowWidths = laid.rows.map(row => row.reduce((sum, item) => sum + item.width, 0));
  const totalWidth = rowWidths.reduce((sum, width) => sum + width, 0);
  if (totalWidth <= 0) return;
  const front = progress * totalWidth;

  let cursor = 0;
  laid.rows.forEach((row, rowIndex) => {
    const rowWidth = rowWidths[rowIndex];
    const rowStart = cursor;
    cursor += rowWidth;
    if (rowWidth <= 0) return;
    // How much of this row the front has covered.
    const covered = Math.max(0, Math.min(1, (front - rowStart) / rowWidth));
    if (covered <= 0) return;
    const baseline = top + ascent + rowIndex * LYRIC_ROW_HEIGHT;
    const inkTop = baseline - LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
    const inkBottom = baseline + LYRIC_FONT_SIZE * 0.3;

    ctx.save();
    // Clip to this row's ink band so the wipe cannot tint the row above/below.
    ctx.beginPath();
    ctx.rect(LYRIC_LEFT - 2, inkTop - LYRIC_GLOW_PAD, rowWidth + 4, (inkBottom - inkTop) + LYRIC_GLOW_PAD * 2);
    ctx.clip();

    if (glow && covered > 0.01) {
      // The glow follows the front: only the swept part of the row glows, matching the
      // per-word karaoke where a word's glow appears as it is sung.
      const localFront = LYRIC_LEFT + covered * rowWidth;
      ctx.save();
      ctx.beginPath();
      ctx.rect(LYRIC_LEFT - LYRIC_GLOW_PAD, inkTop - LYRIC_GLOW_PAD, (localFront - LYRIC_LEFT) + LYRIC_GLOW_PAD * 2, (inkBottom - inkTop) + LYRIC_GLOW_PAD * 2);
      ctx.clip();
      ctx.globalAlpha = 0.5;
      ctx.drawImage(glow.image, 0, top - glow.margin);
      ctx.restore();
    }

    // Same gradient convention as the karaoke wipe: fully lit left of (front - edge),
    // fading to the pending level at (front + edge), clamped outside by the canvas.
    const localFront = LYRIC_LEFT + covered * rowWidth;
    let fill = `rgba(255,255,255,${lineAlpha})`;
    if (covered < 1) {
      fill = ctx.createLinearGradient(localFront - edge, baseline, localFront + edge, baseline);
      fill.addColorStop(0, `rgba(255,255,255,${lineAlpha})`);
      fill.addColorStop(1, `rgba(255,255,255,${pendingAlpha})`);
    }
    ctx.fillStyle = fill;
    ctx.fillText(row.text, LYRIC_LEFT, baseline);
    ctx.restore();
  });
}

/**
 * Distributes the line's sung window across its romanized words, proportionally to each word's
 * character length, and stores `startMs`/`endMs` on every roman item. This lets the romanization
 * run its own per-word karaoke wipe in step with the line, even when the romanized word count
 * differs from the original's (kuromoji tokens, pinyin syllables, a single Hangul run, …).
 */
function assignRomanTiming(romanRows, window) {
  if (!romanRows?.length || !window || window.startMs == null || window.endMs == null) return;
  const items = [];
  for (const row of romanRows) for (const item of row) items.push(item);
  const totalChars = items.reduce((sum, item) => sum + item.text.length, 0) || 1;
  const span = Math.max(1, window.endMs - window.startMs);
  let cursor = window.startMs;
  for (const item of items) {
    const duration = span * (item.text.length / totalChars);
    item.startMs = cursor;
    item.endMs = cursor + duration;
    cursor += duration;
  }
}

/**
 * Romanizes each of a group's syllables on its own, keeping the syllable's own [startMs, endMs].
 * This is the timing ground truth the group's whole-line romanization is anchored to: a syllable
 * held for seconds (a long く, a melisma) stretches its romaji instead of the whole line being
 * split character-proportionally, which is what used to push a held tail seconds behind the vocal.
 *
 * Returns [{ str, startMs, endMs }] | null. Returns null when a syllable cannot be romanized, so
 * the caller can fall back to the flat spread rather than anchor to a partial reading.
 */
async function romanizeSyllableParts(group, ctx) {
  const syllables = (group.syllables || []).filter(s => s.startMs != null && s.endMs != null && s.text && s.text.trim());
  if (!syllables.length) return null;
  const parts = [];
  for (const syllable of syllables) {
    const raw = syllable.text.trim();
    let roman = null;
    try { roman = await romanizeLine({ text: raw }, ctx); } catch { roman = null; }
    // Pass through already-Latin text, numbers, or punctuation rather than dropping the syllable
    const effective = (roman != null && roman.trim()) ? roman : raw;
    const str = effective.replace(/\s+/g, '');
    if (!str) continue;
    parts.push({ str, startMs: syllable.startMs, endMs: syllable.endMs });
  }
  return parts.length ? parts : null;
}

/**
 * Synchronizes Korean word groups with exact syllable-by-syllable Romaja timing.
 * 1 Hangul character block = 1 sung syllable, so each Romaja slice is mapped 1:1
 * to the group's syllable timings and character times (including batchim assimilation).
 */
function timeKoreanGroup(group) {
  const syllables = (group.syllables || []).filter(s => s.startMs != null && s.endMs != null && s.text && s.text.trim());
  if (!syllables.length) return null;
  const { fullStr, charSlices } = romanizeKoreanWithSlices(group.text);
  if (!charSlices.length) return null;

  const charTimes = [];
  let cursor = 0;
  for (const syl of syllables) {
    const token = syl.text.trim();
    if (!token) continue;
    const at = group.text.indexOf(token, cursor);
    if (at < 0) continue;
    const span = Math.max(1, syl.endMs - syl.startMs);

    for (let i = cursor; i < at; i++) {
      const rom = charSlices[i] || '';
      for (let k = 0; k < rom.length; k++) {
        charTimes.push({ startMs: syl.startMs, endMs: syl.startMs });
      }
    }

    for (let i = 0; i < token.length; i++) {
      const rom = charSlices[at + i] || '';
      const cSpan = span / token.length;
      const cs = syl.startMs + i * cSpan;
      const ce = cs + cSpan;
      for (let k = 0; k < rom.length; k++) {
        const lSpan = cSpan / Math.max(1, rom.length);
        charTimes.push({
          startMs: cs + k * lSpan,
          endMs: cs + (k + 1) * lSpan,
        });
      }
    }
    cursor = at + token.length;
  }
  const lastSyl = syllables[syllables.length - 1];
  for (let i = cursor; i < group.text.length; i++) {
    const rom = charSlices[i] || '';
    for (let k = 0; k < rom.length; k++) {
      charTimes.push({ startMs: lastSyl.endMs, endMs: lastSyl.endMs });
    }
  }

  const tokens = fullStr.split(/\s+/).filter(Boolean);
  if (!tokens.length) return null;

  const nonWsCharTimes = [];
  let romCursor = 0;
  for (let i = 0; i < group.text.length; i++) {
    const rom = charSlices[i] || '';
    for (let k = 0; k < rom.length; k++) {
      if (!/\s/.test(rom[k])) {
        if (romCursor < charTimes.length) nonWsCharTimes.push(charTimes[romCursor]);
      }
      romCursor++;
    }
  }

  const words = [];
  let idx = 0;
  for (const token of tokens) {
    const tokenCharTimes = nonWsCharTimes.slice(idx, idx + token.length);
    if (!tokenCharTimes.length) {
      words.push({ text: token, startMs: group.startMs, endMs: group.endMs });
      idx += token.length;
      continue;
    }
    const startMs = tokenCharTimes[0].startMs;
    const endMs = Math.max(startMs + 1, tokenCharTimes[tokenCharTimes.length - 1].endMs);
    words.push({ text: token, startMs, endMs, charTimes: tokenCharTimes });
    idx += token.length;
  }

  return words.length ? { words, text: words.map(w => w.text).join(' ') } : null;
}

/**
 * Synchronizes Chinese word groups with exact character-to-Pinyin syllable timing.
 * 1 Hanzi character = 1 Pinyin syllable.
 */
function timeChineseGroup(group) {
  const syllables = (group.syllables || []).filter(s => s.startMs != null && s.endMs != null && s.text && s.text.trim());
  if (!syllables.length) return null;
  const { charSlices } = romanizeChineseWithSlices(group.text);
  if (!charSlices.length) return null;

  const words = [];
  let cursor = 0;

  for (const syl of syllables) {
    const token = syl.text.trim();
    if (!token) continue;
    const at = group.text.indexOf(token, cursor);
    if (at < 0) continue;
    const span = Math.max(1, syl.endMs - syl.startMs);

    const pinyinTokens = [];
    for (let i = 0; i < token.length; i++) {
      const slice = (charSlices[at + i] || '').trim();
      if (slice && /\p{L}|\p{N}/u.test(slice)) {
        pinyinTokens.push(slice);
      }
    }
    if (!pinyinTokens.length) {
      cursor = at + token.length;
      continue;
    }

    const totalSub = pinyinTokens.length;
    pinyinTokens.forEach((pt, pIdx) => {
      const sStart = syl.startMs + (span * pIdx) / totalSub;
      const sEnd = Math.max(sStart + 1, syl.startMs + (span * (pIdx + 1)) / totalSub);
      const sSpan = Math.max(1, sEnd - sStart);
      const charTimes = [];
      for (let k = 0; k < pt.length; k++) {
        charTimes.push({
          startMs: sStart + (sSpan * k) / pt.length,
          endMs: sStart + (sSpan * (k + 1)) / pt.length,
        });
      }
      words.push({ text: pt, startMs: sStart, endMs: sEnd, charTimes });
    });
    cursor = at + token.length;
  }

  return words.length ? { words, text: words.map(w => w.text).join(' ') } : null;
}

/** Every romanization character of `parts`, spread evenly across the syllable it came from. */
function syllableCharTimes(parts) {
  const chars = [];
  for (const part of parts) {
    const span = part.endMs - part.startMs;
    for (let i = 0; i < part.str.length; i++) {
      chars.push({
        char: part.str[i],
        startMs: part.startMs + (span * i) / part.str.length,
        endMs: part.startMs + (span * (i + 1)) / part.str.length,
      });
    }
  }
  return chars;
}

/**
 * Aligns the whole-line romanization (character by character) to the per-syllable romanization
 * with a longest-common-subsequence walk, so the two line up even when they segment differently
 * ("hanasa zu" from the whole line vs "hanare sazu" from the syllables). Characters with no
 * counterpart interpolate between their matched neighbours. Returns { times, matched }, where
 * `times[i]` is the time window of the whole-line romanization's i-th character.
 */
function alignRomanToSyllables(wholeChars, charTimes) {
  const n = wholeChars.length;
  const m = charTimes.length;
  const dp = Array.from({ length: n + 1 }, () => new Int32Array(m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = wholeChars[i] === charTimes[j].char
        ? dp[i + 1][j + 1] + 1
        : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const times = new Array(n).fill(null);
  let i = 0, j = 0, matched = 0;
  while (i < n && j < m) {
    if (wholeChars[i] === charTimes[j].char) {
      times[i] = { startMs: charTimes[j].startMs, endMs: charTimes[j].endMs };
      i++; j++; matched++;
    } else if (dp[i + 1][j] >= dp[i][j + 1]) i++;
    else j++;
  }
  const matchedIndexes = [];
  for (let k = 0; k < n; k++) if (times[k]) matchedIndexes.push(k);
  if (!matchedIndexes.length) return { times: null, matched };
  for (let k = 0; k < n; k++) {
    if (times[k]) continue;
    let prev = -1, next = -1;
    for (const index of matchedIndexes) { if (index < k) prev = index; if (index > k && next === -1) next = index; }
    if (prev >= 0 && next >= 0) {
      const t = (k - prev) / (next - prev);
      times[k] = {
        startMs: times[prev].startMs + (times[next].startMs - times[prev].startMs) * t,
        endMs: times[prev].endMs + (times[next].endMs - times[prev].endMs) * t,
      };
    } else if (prev >= 0) {
      times[k] = { ...times[prev] };
    } else {
      times[k] = { ...times[next] };
    }
  }
  return { times, matched };
}

/** Cuts the romanization tokens into timed words from a per-character time table (spaces dropped). */
function timeTokensFromChars(tokens, times) {
  const words = [];
  let index = 0;
  let prevEnd = -Infinity;
  for (const token of tokens) {
    const first = times[index];
    const last = times[index + token.length - 1];
    if (!first || !last) return null;
    let startMs = Math.max(first.startMs, prevEnd); // never let a token start before the previous one ends
    let endMs = Math.max(last.endMs, startMs);
    // Per-character times inside the token, so a held syllable buried in a multi-character token
    // ("yuku" where the く is held for seconds) wipes fast over "yu" and slow over "ku" instead of
    // the whole token being split evenly — the romanization's own version of the main line's
    // per-syllable wipe. Kept monotonic and clamped inside the token window.
    const charTimes = [];
    let charPrev = startMs;
    for (let k = 0; k < token.length; k++) {
      const slot = times[index + k] || last;
      const cs = Math.max(slot.startMs, charPrev, startMs);
      const ce = Math.max(slot.endMs, cs);
      charTimes.push({ startMs: cs, endMs: ce });
      charPrev = ce;
    }
    // Pin the last character to the token end so the wipe finishes exactly with the token.
    if (charTimes.length) charTimes[charTimes.length - 1].endMs = Math.max(charTimes[charTimes.length - 1].startMs, endMs);
    words.push({ text: token, startMs, endMs, charTimes });
    prevEnd = endMs;
    index += token.length;
  }
  return words;
}

/**
 * Fallback when the alignment is not trustworthy: spreads the tokens across the group's syllables
 * weighted by each syllable's romanization length, which is always monotonic and still follows the
 * singing. A syllable romanized as "hanare" (6) contributes more of the timeline than one read as
 * "zu" (2), so the highlight stays in step even without a character-level match.
 */
function spreadTokensOverParts(tokens, parts) {
  const total = parts.reduce((sum, part) => sum + Math.max(1, part.str.length), 0) || 1;
  const timeAt = fraction => {
    let pos = Math.max(0, Math.min(1, fraction)) * total;
    for (const part of parts) {
      const weight = Math.max(1, part.str.length);
      if (pos <= weight) {
        const local = weight ? pos / weight : 0;
        return part.startMs + local * (part.endMs - part.startMs);
      }
      pos -= weight;
    }
    return parts[parts.length - 1].endMs;
  };
  const totalChars = tokens.reduce((sum, t) => sum + t.length, 0) || 1;
  const words = [];
  let acc = 0;
  for (const token of tokens) {
    const a = acc / totalChars;
    acc += token.length;
    const b = acc / totalChars;
    // Per-character times from the same syllable-weighted mapping, so even the fallback wipes
    // each letter in step with the singing rather than splitting the token evenly.
    const charTimes = [];
    for (let k = 0; k < token.length; k++) {
      const ca = (acc - token.length + k) / totalChars;
      const cb = (acc - token.length + k + 1) / totalChars;
      charTimes.push({ startMs: timeAt(ca), endMs: timeAt(cb) });
    }
    words.push({ text: token, startMs: timeAt(a), endMs: timeAt(b), charTimes });
  }
  return words;
}

/**
 * Romanizes one word-synced line as a list of timed words. Each drawn word group is romanized as
 * a whole (so kuromoji keeps the inter-word context), then its tokens are timed against the
 * group's *syllables* — the character-level alignment when the two romanizations line up, the
 * syllable-length spread otherwise. This is what makes the secondary line's highlight track the
 * original word highlight, holds included, instead of drifting by the length of a held syllable.
 *
 * Returns { text, words: [{ text, startMs, endMs }] } | null. Returns null when the line has no
 * usable word timing or nothing could be romanized.
 */
async function buildRomanSegments(line, ctx) {
  const groups = groupSyllablesIntoWords(line.text, line.words || []);
  if (!groups.length) return null;
  const words = [];
  for (const group of groups) {
    if (group.startMs == null || group.endMs == null) return null; // need per-word timing

    // 1) Direct Korean character-to-syllable timing
    if (/[\uac00-\ud7a3]/.test(group.text)) {
      const timedKo = timeKoreanGroup(group);
      if (timedKo?.words?.length) {
        for (const w of timedKo.words) words.push(w);
        continue;
      }
    }

    // 2) Direct Chinese character-to-syllable timing
    if (/[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]/.test(group.text) && !ctx?.hasKana) {
      const timedCn = timeChineseGroup(group);
      if (timedCn?.words?.length) {
        for (const w of timedCn.words) words.push(w);
        continue;
      }
    }

    // 3) General / Japanese path (Kuromoji, LCS alignment)
    let roman = null;
    try { roman = await romanizeLine({ text: group.text }, ctx); } catch { roman = null; }
    // If romanizeLine returned null because the token is already Latin / digits, preserve it
    if (!roman && /\p{L}|\p{N}/u.test(group.text)) roman = group.text;
    if (!roman) continue;
    const tokens = roman.split(/\s+/).filter(Boolean);
    if (!tokens.length) continue;

    const parts = await romanizeSyllableParts(group, ctx).catch(() => null);
    let timed = null;
    if (parts) {
      const wholeChars = tokens.join('').split('');
      const { times, matched } = alignRomanToSyllables(wholeChars, syllableCharTimes(parts));
      if (times && matched / Math.max(1, wholeChars.length) >= LYRIC_ROMAN_ALIGN_MIN) {
        timed = timeTokensFromChars(tokens, times);
      }
      if (!timed) timed = spreadTokensOverParts(tokens, parts);
    }
    if (timed) {
      for (const word of timed) words.push(word);
      continue;
    }

    // Last resort (no per-syllable romanization): even character-proportional spread over the group.
    const totalChars = tokens.reduce((sum, t) => sum + t.length, 0) || 1;
    const span = Math.max(1, group.endMs - group.startMs);
    let cursor = group.startMs;
    for (const token of tokens) {
      const duration = span * (token.length / totalChars);
      words.push({ text: token, startMs: cursor, endMs: cursor + duration });
      cursor += duration;
    }
  }
  return words.length ? { text: words.map(w => w.text).join(' '), words } : null;
}

/** Copies per-word timings onto the laid-out roman rows (same order, same count). */
function attachRomanTiming(romanRows, words) {
  if (!romanRows?.length || !words?.length) return;
  const items = [];
  for (const row of romanRows) for (const item of row) items.push(item);
  if (items.length !== words.length) return; // shape mismatch → leave timings untouched
  for (let i = 0; i < items.length; i++) {
    items[i].startMs = words[i].startMs;
    items[i].endMs = words[i].endMs;
    // Carry the per-character table too, so the wipe can advance letter by letter (a held
    // syllable inside the token holds only its own letters). Absent → the draw falls back to a
    // linear sweep across the token, exactly as before.
    if (words[i].charTimes?.length === items[i].text.length) items[i].charTimes = words[i].charTimes;
  }
}

/**
 * Fallback timing for a word-synced line: keeps the whole-line romanization text but maps each
 * romanized word through the ORIGINAL words' timing curve by character proportion, so the
 * secondary line pauses where the original pauses instead of drifting linearly.
 */
function assignRomanTimingCurve(romanRows, groups) {
  if (!romanRows?.length || !groups?.length) return;
  const items = [];
  for (const row of romanRows) for (const item of row) items.push(item);
  if (!items.length) return;
  const timed = groups.filter(g => g.startMs != null && g.endMs != null && g.text && g.text.length);
  if (!timed.length) return;
  const totalOriginal = timed.reduce((sum, g) => sum + g.text.length, 0) || 1;
  const timeAt = fraction => {
    let pos = Math.max(0, Math.min(1, fraction)) * totalOriginal;
    for (const g of timed) {
      if (pos <= g.text.length) {
        const local = g.text.length ? pos / g.text.length : 0;
        return g.startMs + local * (g.endMs - g.startMs);
      }
      pos -= g.text.length;
    }
    return timed[timed.length - 1].endMs;
  };
  const totalRoman = items.reduce((sum, it) => sum + it.text.length, 0) || 1;
  let acc = 0;
  for (const item of items) {
    const a = acc / totalRoman;
    acc += item.text.length;
    const b = acc / totalRoman;
    item.startMs = timeAt(a);
    item.endMs = timeAt(b);
  }
}

/** Normalized comparison for the whole-line vs per-word guard. */
function sameRomanization(a, b) {
  const norm = s => String(s || '').toLowerCase().replace(/[^\p{L}\p{N}]+/gu, ' ').trim();
  return norm(a) === norm(b);
}

/**
 * Draws a line's romanization as a small secondary block under the main rows, running the same
 * per-word karaoke effects as the main line — the left-to-right wipe, the word lift while it is
 * being sung, and the held-syllable glow — scaled to the smaller font so the two lines read as one
 * unit. The caller owns the save/restore around the whole line, so this only sets the roman font.
 */
function drawRomanRows(ctx, laid, top, alpha, elapsedMs, glow) {
  if (!laid.romanRows?.length || !laid.romanFont) return;
  const romanTop = top + laid.rows.length * LYRIC_ROW_HEIGHT + LYRIC_ROMAN_GAP;
  const romanAscent = LYRIC_ROMAN_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const edge = Math.max(1, LYRIC_WIPE_EM * LYRIC_ROMAN_FONT_SIZE);
  const pendingAlpha = alpha * LYRIC_ROMAN_PENDING_ALPHA;
  const pendingFill = `rgba(255,255,255,${pendingAlpha})`;
  const inkTopOffset = LYRIC_ROMAN_FONT_SIZE * LYRIC_ASCENT_RATIO;
  const inkBottomOffset = LYRIC_ROMAN_FONT_SIZE * 0.3;
  ctx.save();
  ctx.font = laid.romanFont;
  laid.romanRows.forEach((row, rowIndex) => {
    const baseline = romanTop + romanAscent + rowIndex * LYRIC_ROMAN_ROW_HEIGHT;
    for (const item of row) {
      const x = LYRIC_LEFT + item.x;
      const width = Math.max(1, item.width);
      const start = item.startMs;
      const end = Math.max((start ?? 0) + 1, item.endMs);
      const inkTop = baseline - inkTopOffset;
      const inkBottom = baseline + inkBottomOffset;

      // Per-character wipe: when the token carries a per-character table (a held syllable buried
      // inside it), the wipe front is the mean of each letter's own progress — so "yuku" races
      // over "yu" and crawls over a held "ku", exactly like the main line's per-syllable wipe.
      // Without the table it degrades to the old linear sweep across the token.
      const charTimes = item.charTimes?.length === item.text.length ? item.charTimes : null;
      let lit;
      if (charTimes) {
        let sum = 0;
        for (const slot of charTimes) {
          const cs = slot.startMs;
          const ce = Math.max(cs + 1, slot.endMs);
          sum += Math.max(0, Math.min(1, (elapsedMs - cs) / (ce - cs)));
        }
        lit = sum / charTimes.length;
      } else {
        lit = start == null ? 0 : Math.max(0, Math.min(1, (elapsedMs - start) / (end - start)));
      }

      // Eased-out lift over max(250ms, the word's own duration), like the main karaoke.
      const liftT = start == null ? 1 : Math.max(0, Math.min(1, (elapsedMs - start) / Math.max(250, end - start)));
      const lift = -LYRIC_ROMAN_WORD_LIFT * easeOutCubic(liftT);

      // Held-syllable glow: only a character sung for over a second glows, peaking mid-character.
      // With a per-character table the glow is driven by whichever character is currently held, so
      // a held syllable lights only itself (matching the main line); otherwise the whole token.
      let glowAlpha = 0;
      if (charTimes) {
        for (const slot of charTimes) {
          const cs = slot.startMs;
          const ce = Math.max(cs + 1, slot.endMs);
          if (ce - cs > 1000 && elapsedMs > cs && elapsedMs < ce) {
            glowAlpha = Math.max(glowAlpha, Math.sin(((elapsedMs - cs) / (ce - cs)) * Math.PI) * LYRIC_ROMAN_HELD_GLOW_SCALE);
          }
        }
      } else {
        const duration = end - (start ?? 0);
        const fraction = start == null ? 1 : Math.max(0, Math.min(1, (elapsedMs - start) / (end - start)));
        glowAlpha = duration > 1000 && fraction > 0 && fraction < 1
          ? Math.sin(fraction * Math.PI) * LYRIC_ROMAN_HELD_GLOW_SCALE
          : 0;
      }

      ctx.save();
      // Erase this word's pending copy (with headroom for the lift) and clip to the word's box so
      // the gradient and glow cannot tint the neighbouring word.
      ctx.clearRect(x - 1, inkTop - LYRIC_ROMAN_LIFT_CLEARANCE, width + 2, (inkBottom - inkTop) + LYRIC_ROMAN_LIFT_CLEARANCE + 2);
      ctx.beginPath();
      ctx.rect(x - 1, inkTop - LYRIC_ROMAN_LIFT_CLEARANCE, width + 2, (inkBottom - inkTop) + LYRIC_ROMAN_LIFT_CLEARANCE + 2);
      ctx.clip();
      if (lift) ctx.translate(0, lift);

      const front = x - edge + lit * (width + 2 * edge);

      if (glow && glowAlpha > 0.01) {
        // Glow clipped to the word's ink band and horizontally to the wipe front, matching the
        // main line's held-syllable glow.
        const glowLeft = x - 2;
        const glowRight = Math.min(x + width, front) + 2;
        if (glowRight > glowLeft) {
          ctx.save();
          ctx.beginPath();
          ctx.rect(glowLeft, inkTop - LYRIC_ROMAN_GLOW_PAD, glowRight - glowLeft, (inkBottom - inkTop) + LYRIC_ROMAN_GLOW_PAD * 2);
          ctx.clip();
          ctx.globalAlpha = glowAlpha;
          ctx.drawImage(glow.image, 0, top - glow.margin);
          ctx.restore();
        }
      }

      // A single draw, like the main line's `drawWordWipe`: the pending copy while the word is
      // still unsung, otherwise the gradient wipe. Drawing the pending copy first and compositing
      // the gradient over it (the old code) accumulated alpha in the unsung tail — `pendingFill` is
      // opaque-ish, not transparent — so the whole word jumped to ~0.53 alpha the moment its first
      // letter was sung instead of staying dim until the front reached each letter.
      if (lit <= 0) {
        ctx.fillStyle = pendingFill;
        ctx.fillText(item.text, x, baseline);
      } else {
        let fill = `rgba(255,255,255,${alpha})`;
        if (lit < 1) {
          fill = ctx.createLinearGradient(front - edge, baseline, front + edge, baseline);
          fill.addColorStop(0, `rgba(255,255,255,${alpha})`);
          fill.addColorStop(1, pendingFill);
        }
        ctx.fillStyle = fill;
        ctx.fillText(item.text, x, baseline);
      }
      ctx.restore();
    }
  });
  ctx.restore();
}

function drawLyricsFrame(ctx, prepared, elapsedMs, durationMs) {
  ctx.clearRect(0, 0, WIDTH, HEIGHT);

  const items = prepared.items;
  const lines = prepared.lines;
  // The focus item is the latest one that started; background vocals never take focus.
  let focus = -1;
  for (let i = 0; i < items.length; i++) {
    const item = items[i];
    const eligible = item.gap || !lines[item.line].background;
    if (eligible && item.startMs <= elapsedMs + 300) focus = i;
    else if (eligible) break;
  }
  focus = Math.max(0, Math.min(focus, items.length - 1));
  const anchor = focus;
  const sung = activeLines(lines, elapsedMs);

  // The stack is laid out once for the anchor that was current before this change and once
  // for the anchor that is current now; each item eases from the first layout to the second
  // with a per-item delay, so the stack chases the singer instead of sliding as one block.
  const layoutFor = anchorIndex => {
    const out = new Array(items.length);
    const heightOf = index => {
      const item = items[index];
      return item.gap ? LYRIC_ITEM_HEIGHT : prepared.lines[item.line].blockHeight;
    };
    const gapAfter = index => {
      const next = items[index + 1];
      if (!next) return 0;
      return (next.gap || lines[next.line]?.background) ? 0 : LYRIC_LINE_GAP;
    };
    out[anchorIndex] = LYRIC_ANCHOR_BASELINE - LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;
    for (let i = anchorIndex + 1; i < items.length; i++) out[i] = out[i - 1] + heightOf(i - 1) + gapAfter(i - 1);
    for (let i = anchorIndex - 1; i >= 0; i--) out[i] = out[i + 1] - (heightOf(i) + gapAfter(i));
    return out;
  };

  // The anchor order is the list of items that can take focus (gaps and main lines), so the
  // "previous anchor" is the one before the current one.
  const anchorOrder = items.map((item, index) => ({ item, index })).filter(entry => entry.item.gap || !lines[entry.item.line].background);
  const posInOrder = anchorOrder.findIndex(entry => entry.index === anchor);
  const prevAnchor = posInOrder > 0 ? anchorOrder[posInOrder - 1].index : anchor;
  const target = layoutFor(anchor);
  const from = layoutFor(prevAnchor);
  const changeMs = anchor !== prevAnchor ? items[anchor].startMs : -Infinity;

  const easeFor = index => {
    if (anchor === prevAnchor) return 1;
    const delay = Math.min(Math.abs(index - anchor) * LYRIC_STAGGER_MS, LYRIC_STAGGER_MAX_MS);
    return fastOutSlowIn(Math.max(0, Math.min(1, (elapsedMs - changeMs - delay) / LYRIC_SCROLL_MS)));
  };

  const first = Math.max(0, anchor - 4);
  const last = Math.min(items.length - 1, anchor + 8);
  for (let index = first; index <= last; index++) {
    const item = items[index];
    const p = easeFor(index);
    const top = from[index] + (target[index] - from[index]) * p;

    if (item.gap) {
      const gapProgress = Math.max(0, Math.min(1, (elapsedMs - item.startMs) / Math.max(1, item.endMs - item.startMs)));
      const within = elapsedMs >= item.startMs && elapsedMs <= item.endMs;
      const alpha = within ? 1 : 0;
      if (alpha > 0) drawInterludeDots(ctx, top + LYRIC_ITEM_HEIGHT, gapProgress, elapsedMs, alpha);
      continue;
    }

    const line = lines[item.line];
    const blockHeight = prepared.lines[item.line].blockHeight;
    if (top > LYRIC_BAND_BOTTOM + 80 || top + blockHeight < LYRIC_BAND_TOP - 80) continue;

    // Background vocals appear once the line they answer is being sung, but they stay DIM until
    // their own syllables start. The Android player does the same: `bgVisible` makes the entry
    // exist, while its karaoke state decides whether it is lit, so an un-started background line
    // reads at the pending level rather than as a finished, full-brightness line.
    if (line.background) {
      const main = mainLineOf(lines, item.line);
      const visible = sung.has(item.line) || (main != null && sung.has(main)) || (main != null && elapsedMs >= lines[main].timeMs && elapsedMs <= line.timeMs);
      if (!visible) continue;
    }

    // Background vocals get the same karaoke wipe as a main line (the Android player runs one
    // LyricsLine per entry, background or not); they are only dimmer. So the strip shortcut must
    // be skipped for them — otherwise the line would sit still while it is being sung.
    const isBackground = Boolean(line.background);
    const isActive = !isBackground && sung.has(item.line);
    const isPlaying = isBackground && sung.has(item.line);
    const distance = Math.abs(index - anchor);
    // A background vocal that has appeared but whose syllables have not started yet is not a
    // finished line: it reads at the pending level. Only a sung background line sits at the
    // background line's resting alpha, and only a sung main line sits at full white.
    const bgStarted = isBackground && elapsedMs >= (line.words?.[0]?.startMs ?? line.timeMs);
    // The background line's 0.4 resting alpha is baked into its pre-rendered strips, and the
    // wipe paints it via `lineAlpha`, so the wrapper must not apply it a second time (that would
    // double-dim the line to 0.16). A background vocal that has appeared but not started yet
    // reads at the pending level.
    const baseAlpha = isActive ? 1
      : isBackground ? (bgStarted ? 1 : LYRIC_PENDING_ALPHA)
        : LYRIC_DIM_ALPHA;
    const edgeFade = Math.max(0, Math.min(1, Math.min(top - LYRIC_BAND_TOP + LYRIC_FADE_TOP, LYRIC_BAND_BOTTOM - top - blockHeight + LYRIC_FADE_BOTTOM) / LYRIC_FADE_TOP));
    const alpha = baseAlpha * edgeFade;
    if (alpha <= 0.01) continue;

    const laid = prepared.lines[item.line];
    // Depth blur: inactive lines are blurred by distance. The blurred copy is pre-rendered,
    // so this costs a single drawImage per line instead of a per-frame blur pass.
    const blurIndex = (isActive || isPlaying) ? 0 : Math.max(0, Math.min(distance - 1, LYRIC_BLUR_RADII.length - 1));
    const drawSource = prepared.lines[item.line].blurs?.[blurIndex] || null;

    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.font = laid.font;
    ctx.textBaseline = 'alphabetic';
    ctx.textAlign = 'left';
    const ascent = LYRIC_FONT_SIZE * LYRIC_ASCENT_RATIO;

    if (!isActive && !isPlaying && drawSource) {
      // A blurred line is drawn from its pre-rendered strip, positioned by its ink top so the
      // blur cannot push the text out of place.
      const stripTop = top - drawSource.margin;
      ctx.drawImage(drawSource.image, 0, stripTop);
      ctx.restore();
      continue;
    }

    if (isActive || isPlaying) {
      // Unsung text first, then the glow and the wipes on top of it. A background vocal is drawn
      // at its own dimmer alpha (its glow strip already has that opacity baked in).
      const lineAlpha = isPlaying ? LYRIC_BG_ALPHA : 1;
      ctx.fillStyle = `rgba(255,255,255,${lineAlpha * LYRIC_PENDING_ALPHA})`;
      laid.rows.forEach((row, rowIndex) => {
        ctx.fillText(row.text, LYRIC_LEFT, top + ascent + rowIndex * LYRIC_ROW_HEIGHT);
      });
      if (laid.lineLevel) {
        // No word timing: fill the whole line as one sweep (Spotify-style) over its window,
        // instead of a per-word wipe built from estimated timings.
        const sweep = laid.sweep;
        const progress = Math.max(0, Math.min(1, (elapsedMs - sweep.startMs) / Math.max(1, sweep.endMs - sweep.startMs)));
        drawLineSweep(ctx, laid, top, progress, laid.glow, lineAlpha);
      } else {
        // The glow only lights the words that are being sung, so it is drawn per word. A word
        // that has not started yet is skipped entirely: `drawWordWipe` also paints the pending
        // copy of its own slice, and doing that twice would double the alpha of that slice.
        // The held-syllable glow is derived inside `drawWordWipe` from each syllable's own
        // timing, so a held syllable lights only itself and only up to the wipe front.
        laid.rows.forEach((row, rowIndex) => {
          const baseline = top + ascent + rowIndex * LYRIC_ROW_HEIGHT;
          for (const entry of row) {
            const syllables = entry.syllables?.length ? entry.syllables : [{ text: entry.text, startMs: entry.startMs, endMs: entry.endMs }];
            if (syllables[0]?.startMs == null) continue;
            const totalChars = entry.text.length || 1;
            let lit = 0;
            for (const syllable of syllables) {
              const start = syllable.startMs;
              const end = Math.max(start + 1, syllable.endMs);
              const fraction = Math.max(0, Math.min(1, (elapsedMs - start) / (end - start)));
              lit += fraction * syllable.text.trim().length;
            }
            const progress = lit / totalChars;
            if (progress <= 0) continue;
            drawWordWipe(ctx, entry, top, baseline, progress, laid.glow, elapsedMs, lineAlpha);
          }
        });
      }
      // The romanization is a secondary line: same wipe/lift/glow, but scaled to its smaller font.
      drawRomanRows(ctx, laid, top, LYRIC_ROMAN_ALPHA * lineAlpha, elapsedMs, laid.romanGlow);
    } else {
      ctx.fillStyle = '#FFFFFF';
      laid.rows.forEach((row, rowIndex) => {
        const baseline = top + ascent + rowIndex * LYRIC_ROW_HEIGHT;
        ctx.fillText(row.text, LYRIC_LEFT, baseline);
      });
      // No pre-rendered strip for this line: draw its romanization by hand too.
      drawRomanRows(ctx, laid, top, LYRIC_ROMAN_ALPHA, elapsedMs, laid.romanGlow);
    }
    ctx.restore();
  }

  // The lyric layer dissolves at the top and bottom edges instead of being clipped.
  ctx.save();
  ctx.globalCompositeOperation = 'destination-in';
  const fade = ctx.createLinearGradient(0, LYRIC_BAND_TOP, 0, LYRIC_BAND_BOTTOM);
  fade.addColorStop(0, 'rgba(0,0,0,0)');
  fade.addColorStop(LYRIC_FADE_TOP / (LYRIC_BAND_BOTTOM - LYRIC_BAND_TOP), 'rgba(0,0,0,1)');
  fade.addColorStop(1 - LYRIC_FADE_BOTTOM / (LYRIC_BAND_BOTTOM - LYRIC_BAND_TOP), 'rgba(0,0,0,1)');
  fade.addColorStop(1, 'rgba(0,0,0,0)');
  ctx.fillStyle = fade;
  ctx.fillRect(0, LYRIC_BAND_TOP, WIDTH, LYRIC_BAND_BOTTOM - LYRIC_BAND_TOP);
  ctx.restore();

  drawHeaderImage(ctx, prepared.header);

  // Playback progress line and elapsed / remaining time, matching the mobile reference.
  const x0 = 54, x1 = WIDTH - 54, py = 1172;
  const progress = Math.max(0, Math.min(1, elapsedMs / Math.max(durationMs, 1)));
  ctx.save();
  ctx.lineCap = 'round';
  ctx.strokeStyle = 'rgba(255,255,255,.44)'; ctx.lineWidth = 4;
  ctx.beginPath(); ctx.moveTo(x0, py); ctx.lineTo(x1, py); ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,.98)'; ctx.lineWidth = 5;
  ctx.beginPath(); ctx.moveTo(x0, py); ctx.lineTo(x0 + (x1 - x0) * progress, py); ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,.88)'; ctx.font = resolveFont('0:00', 18, 'normal'); ctx.textBaseline = 'alphabetic';
  ctx.textAlign = 'left'; ctx.fillText(formatTime(elapsedMs), x0, py + 30);
  ctx.textAlign = 'right'; ctx.fillText(`-${formatTime(Math.max(0, durationMs - elapsedMs))}`, x1, py + 30);
  ctx.restore();
}

/** Blits the pre-rendered header so the render loop never pays for the shadow/clip work. */
function drawHeaderImage(ctx, header) {
  ctx.save();
  ctx.textAlign = 'left';
  ctx.drawImage(header, 0, 0);
  ctx.restore();
}

/**
 * AMLL's `blurImage` (`packages/core/src/bg-render/img.ts`): a separable, edge-clamped box
 * blur of radius `r` (window 2r+1) applied `passes` times. Ported verbatim so the 32px
 * texture ends up exactly as soft as the WebGL renderer's.
 */
function boxBlurRgba(data, width, height, radius, passes) {
  const rad1 = radius + 1;
  const div = radius + rad1;
  const div2 = 1 / (div * div);
  const wm = width - 1;
  const hm = height - 1;
  const vmin = new Int32Array(Math.max(width, height));
  const vmax = new Int32Array(Math.max(width, height));
  for (let pass = 0; pass < passes; pass++) {
    // Horizontal pass into accumulators, then vertical pass straight back into `data`.
    const acc = new Float32Array(width * height * 4);
    for (let y = 0; y < height; y++) {
      const row = y * width * 4;
      let rsum = data[row] * rad1;
      let gsum = data[row + 1] * rad1;
      let bsum = data[row + 2] * rad1;
      let asum = data[row + 3] * rad1;
      for (let i = 1; i <= radius; i++) {
        const p = row + Math.min(i, wm) * 4;
        rsum += data[p]; gsum += data[p + 1]; bsum += data[p + 2]; asum += data[p + 3];
      }
      for (let x = 0; x < width; x++) {
        const o = row + x * 4;
        acc[o] = rsum; acc[o + 1] = gsum; acc[o + 2] = bsum; acc[o + 3] = asum;
        if (y === 0) { vmin[x] = Math.min(x + rad1, wm) * 4; vmax[x] = Math.max(x - radius, 0) * 4; }
        const p1 = row + vmin[x];
        const p2 = row + vmax[x];
        rsum += data[p1] - data[p2];
        gsum += data[p1 + 1] - data[p2 + 1];
        bsum += data[p1 + 2] - data[p2 + 2];
        asum += data[p1 + 3] - data[p2 + 3];
      }
    }
    for (let x = 0; x < width; x++) {
      let yp = x;
      let rsum = acc[yp * 4] * rad1;
      let gsum = acc[yp * 4 + 1] * rad1;
      let bsum = acc[yp * 4 + 2] * rad1;
      let asum = acc[yp * 4 + 3] * rad1;
      for (let i = 1; i <= radius; i++) {
        yp += i > hm ? 0 : width;
        rsum += acc[yp * 4]; gsum += acc[yp * 4 + 1]; bsum += acc[yp * 4 + 2]; asum += acc[yp * 4 + 3];
      }
      for (let y = 0; y < height; y++) {
        const o = (y * width + x) * 4;
        data[o] = (rsum * div2 + 0.5) | 0;
        data[o + 1] = (gsum * div2 + 0.5) | 0;
        data[o + 2] = (bsum * div2 + 0.5) | 0;
        data[o + 3] = (asum * div2 + 0.5) | 0;
        if (x === 0) { vmin[y] = Math.min(y + rad1, hm) * width; vmax[y] = Math.max(y - radius, 0) * width; }
        const p1 = x + vmin[y];
        const p2 = x + vmax[y];
        rsum += acc[p1 * 4] - acc[p2 * 4];
        gsum += acc[p1 * 4 + 1] - acc[p2 * 4 + 1];
        bsum += acc[p1 * 4 + 2] - acc[p2 * 4 + 2];
        asum += acc[p1 * 4 + 3] - acc[p2 * 4 + 3];
      }
    }
  }
}

/**
 * AMLL's `setAlbum` grade: contrast 0.4 → saturate 3.0 → contrast 1.7 → brightness 0.75,
 * then the box blur. The result is the 32px texture the mesh is painted with.
 */
async function buildBackdropTexture(coverPath) {
  const N = BACKDROP_TEXTURE;
  const { data } = await sharp(coverPath)
    .resize(N, N, { fit: 'cover', position: 'centre' })
    .ensureAlpha()
    .raw()
    .toBuffer({ resolveWithObject: true });
  const clamp = value => (value < 0 ? 0 : value > 255 ? 255 : value);
  for (let i = 0; i < data.length; i += 4) {
    let r = data[i];
    let g = data[i + 1];
    let b = data[i + 2];
    r = (r - 128) * BACKDROP_CONTRAST_A + 128;
    g = (g - 128) * BACKDROP_CONTRAST_A + 128;
    b = (b - 128) * BACKDROP_CONTRAST_A + 128;
    const gray = r * 0.3 + g * 0.59 + b * 0.11;
    r = gray * -2.0 + r * BACKDROP_SATURATION;
    g = gray * -2.0 + g * BACKDROP_SATURATION;
    b = gray * -2.0 + b * BACKDROP_SATURATION;
    r = (r - 128) * BACKDROP_CONTRAST_B + 128;
    g = (g - 128) * BACKDROP_CONTRAST_B + 128;
    b = (b - 128) * BACKDROP_CONTRAST_B + 128;
    data[i] = clamp(r * BACKDROP_BRIGHTNESS);
    data[i + 1] = clamp(g * BACKDROP_BRIGHTNESS);
    data[i + 2] = clamp(b * BACKDROP_BRIGHTNESS);
  }
  boxBlurRgba(data, N, N, BACKDROP_BLUR_RADIUS, BACKDROP_BLUR_PASSES);
  const canvas = createCanvas(N, N);
  const ctx = canvas.getContext('2d');
  const image = ctx.createImageData(N, N);
  image.data.set(data);
  ctx.putImageData(image, 0, 0);
  return canvas;
}

/**
 * Mirror-tiles the texture into a 3×3 sheet so a uv range of [-1, 2] is covered. This is the
 * `MIRRORED_REPEAT` wrap AMLL sets on its WebGL texture, expressed as pixels we can blit.
 */
function buildBackdropTile(texture) {
  const N = texture.width;
  const tile = createCanvas(3 * N, 3 * N);
  const ctx = tile.getContext('2d');
  for (let iy = 0; iy < 3; iy++) {
    for (let ix = 0; ix < 3; ix++) {
      const flipX = ix === 1 ? 1 : -1;
      const flipY = iy === 1 ? 1 : -1;
      ctx.save();
      ctx.translate(ix * N, iy * N);
      ctx.scale(flipX, flipY);
      ctx.drawImage(texture, flipX < 0 ? -N : 0, flipY < 0 ? -N : 0);
      ctx.restore();
    }
  }
  return tile;
}

// Hermite blend basis: [h00, h01, h10, h11] for the parameter t in [0, 1].
function hermiteBasis(t) {
  const t2 = t * t;
  const t3 = t2 * t;
  return [2 * t3 - 3 * t2 + 1, -2 * t3 + 3 * t2, t3 - 2 * t2 + t, t3 - t2];
}

/**
 * Evaluates AMLL's bicubic Hermite patch mesh (`BHPMesh`) over the whole surface and returns
 * the per-vertex screen positions in [0, 1]. The mesh is static — AMLL only animates the
 * texture lookup — so this runs once per video.
 */
function buildBackdropMesh(subdivisions) {
  const { width: cpWidth, height: cpHeight, rows } = BACKDROP_CONTROL_POINTS;
  const uPower = 2 / (cpWidth - 1);
  const vPower = 2 / (cpHeight - 1);
  const at = (cx, cy) => {
    const [x, y, ur, vr, up, vp] = rows[cy * cpWidth + cx];
    const uRot = (ur * Math.PI) / 180;
    const vRot = (vr * Math.PI) / 180;
    const uScale = uPower * up;
    const vScale = vPower * vp;
    return {
      x, y,
      ux: Math.cos(uRot) * uScale,
      uy: Math.sin(uRot) * uScale,
      vx: -Math.sin(vRot) * vScale,
      vy: Math.cos(vRot) * vScale,
    };
  };
  // P(u, v) = B(u) · M · B(v), with M holding the corner locations and tangents.
  const coefficients = (p00, p01, p10, p11, axis) => {
    const l = p => p[axis];
    const u = p => p[axis === 'x' ? 'ux' : 'uy'];
    const v = p => p[axis === 'x' ? 'vx' : 'vy'];
    return [
      [l(p00), l(p01), v(p00), v(p01)],
      [l(p10), l(p11), v(p10), v(p11)],
      [u(p00), u(p01), 0, 0],
      [u(p10), u(p11), 0, 0],
    ];
  };
  const evaluate = (m, u, v) => {
    const bu = hermiteBasis(u);
    const bv = hermiteBasis(v);
    let sum = 0;
    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 4; j++) sum += bu[i] * m[i][j] * bv[j];
    }
    return sum;
  };
  const gridWidth = (cpWidth - 1) * subdivisions + 1;
  const gridHeight = (cpHeight - 1) * subdivisions + 1;
  // AMLL's vertex shader keeps the mesh undistorted: `if (aspect > 1) pos.y *= aspect;
  // else pos.x /= aspect`. On this 720x1280 canvas that magnifies x, so the mesh overflows
  // the sides and the canvas shows its middle — exactly what the shader's clip does.
  const aspect = WIDTH / HEIGHT;
  const scaleX = aspect > 1 ? 1 : 1 / aspect;
  const scaleY = aspect > 1 ? aspect : 1;
  const uvs = new Float32Array(gridWidth * gridHeight * 2);
  const positions = new Float32Array(gridWidth * gridHeight * 2);
  for (let gj = 0; gj < gridHeight; gj++) {
    const cy = Math.min(cpHeight - 2, Math.floor(gj / subdivisions));
    const v = gj / subdivisions - cy;
    for (let gi = 0; gi < gridWidth; gi++) {
      const cx = Math.min(cpWidth - 2, Math.floor(gi / subdivisions));
      const u = gi / subdivisions - cx;
      const mx = coefficients(at(cx, cy), at(cx, cy + 1), at(cx + 1, cy), at(cx + 1, cy + 1), 'x');
      const my = coefficients(at(cx, cy), at(cx, cy + 1), at(cx + 1, cy), at(cx + 1, cy + 1), 'y');
      const k = (gj * gridWidth + gi) * 2;
      // Screen space: x right, y down. The mesh's y points up, so it is flipped here.
      positions[k] = (evaluate(mx, u, v) * scaleX + 1) / 2;
      positions[k + 1] = (1 - evaluate(my, u, v) * scaleY) / 2;
      uvs[k] = gi / (gridWidth - 1);
      uvs[k + 1] = gj / (gridHeight - 1);
    }
  }
  // Evaluates the mesh at an arbitrary uv in [0, 1], returning the normalised screen point.
  // Used to find where the shader's rotation pivot (0.2, 0.2) and centre (0.5, 0.5) land.
  const evaluateAt = (u, v) => {
    const cx = Math.min(cpWidth - 2, Math.max(0, Math.floor(u * (cpWidth - 1))));
    const cy = Math.min(cpHeight - 2, Math.max(0, Math.floor(v * (cpHeight - 1))));
    const fu = u * (cpWidth - 1) - cx;
    const fv = v * (cpHeight - 1) - cy;
    const mx = coefficients(at(cx, cy), at(cx, cy + 1), at(cx + 1, cy), at(cx + 1, cy + 1), 'x');
    const my = coefficients(at(cx, cy), at(cx, cy + 1), at(cx + 1, cy), at(cx + 1, cy + 1), 'y');
    return {
      x: (evaluate(mx, fu, fv) * scaleX + 1) / 2,
      y: (1 - evaluate(my, fu, fv) * scaleY) / 2,
    };
  };
  return { gridWidth, gridHeight, uvs, positions, evaluateAt };
}

/**
 * Rasterises the control-point mesh warp in software: for each output pixel it finds the
 * triangle that covers it and bilinearly samples the tile through that triangle's barycentric
 * coordinates.
 *
 * This replaces a cairo `clip()` + `setTransform()` + `drawImage()` per triangle. cairo
 * antialiases each triangle's edges on its own, so the shared edges end up with a faint
 * dotted line (it shows as a soft arc once the mesh bends) that no clip overlap removes.
 * Here each pixel is owned by exactly one triangle, so the seams cannot occur; it also
 * measures faster than the cairo path.
 *
 * `tile` is the pre-upscaled 3x3 mirror sheet; `S` is the size of one texture cell in tile
 * pixels. Returns a canvas of `width` x `height`.
 */
function rasterizeMeshWarp(tile, S, mesh, width, height) {
  const { gridWidth, gridHeight, uvs, positions } = mesh;
  const tw = tile.width;
  const th = tile.height;
  const tileData = tile.getContext('2d').getImageData(0, 0, tw, th).data;
  const out = createCanvas(width, height);
  const outCtx = out.getContext('2d');
  const image = outCtx.createImageData(width, height);
  const data = image.data;

  const triangle = (a, b, c) => {
    const sa = a * 2;
    const sb = b * 2;
    const sc = c * 2;
    const x0 = positions[sa] * width;
    const y0 = positions[sa + 1] * height;
    const x1 = positions[sb] * width;
    const y1 = positions[sb + 1] * height;
    const x2 = positions[sc] * width;
    const y2 = positions[sc + 1] * height;
    // Tile-space (pixel) coordinates of the three texture samples.
    const u0 = (uvs[sa] + 1) * S;
    const v0 = (uvs[sa + 1] + 1) * S;
    const u1 = (uvs[sb] + 1) * S;
    const v1 = (uvs[sb + 1] + 1) * S;
    const u2 = (uvs[sc] + 1) * S;
    const v2 = (uvs[sc + 1] + 1) * S;
    const denom = (y1 - y2) * (x0 - x2) + (x2 - x1) * (y0 - y2);
    if (Math.abs(denom) < 1e-9) return;
    const invDenom = 1 / denom;
    let minX = Math.max(0, Math.floor(Math.min(x0, x1, x2)));
    let maxX = Math.min(width - 1, Math.ceil(Math.max(x0, x1, x2)));
    let minY = Math.max(0, Math.floor(Math.min(y0, y1, y2)));
    let maxY = Math.min(height - 1, Math.ceil(Math.max(y0, y1, y2)));
    for (let y = minY; y <= maxY; y++) {
      const py = y + 0.5;
      for (let x = minX; x <= maxX; x++) {
        const px = x + 0.5;
        const w0 = ((y1 - y2) * (px - x2) + (x2 - x1) * (py - y2)) * invDenom;
        const w1 = ((y2 - y0) * (px - x2) + (x0 - x2) * (py - y2)) * invDenom;
        const w2 = 1 - w0 - w1;
        // A small negative tolerance so pixels on a shared edge belong to exactly one of
        // the two triangles rather than to neither.
        if (w0 < -1e-7 || w1 < -1e-7 || w2 < -1e-7) continue;
        let tx = w0 * u0 + w1 * u1 + w2 * u2;
        let ty = w0 * v0 + w1 * v1 + w2 * v2;
        if (tx < 0) tx = 0; else if (tx > tw - 1) tx = tw - 1;
        if (ty < 0) ty = 0; else if (ty > th - 1) ty = th - 1;
        const xa = Math.floor(tx);
        const ya = Math.floor(ty);
        const xb = xa + 1 < tw ? xa + 1 : xa;
        const yb = ya + 1 < th ? ya + 1 : ya;
        const fx = tx - xa;
        const fy = ty - ya;
        const ia = (ya * tw + xa) * 4;
        const ib = (ya * tw + xb) * 4;
        const ic = (yb * tw + xa) * 4;
        const id = (yb * tw + xb) * 4;
        const o = (y * width + x) * 4;
        data[o] = tileData[ia] * (1 - fx) * (1 - fy) + tileData[ib] * fx * (1 - fy) + tileData[ic] * (1 - fx) * fy + tileData[id] * fx * fy;
        data[o + 1] = tileData[ia + 1] * (1 - fx) * (1 - fy) + tileData[ib + 1] * fx * (1 - fy) + tileData[ic + 1] * (1 - fx) * fy + tileData[id + 1] * fx * fy;
        data[o + 2] = tileData[ia + 2] * (1 - fx) * (1 - fy) + tileData[ib + 2] * fx * (1 - fy) + tileData[ic + 2] * (1 - fx) * fy + tileData[id + 2] * fx * fy;
        data[o + 3] = 255;
      }
    }
  };

  for (let j = 0; j < gridHeight - 1; j++) {
    for (let i = 0; i < gridWidth - 1; i++) {
      const a = j * gridWidth + i;
      const b = a + 1;
      const c = a + gridWidth;
      const d = c + 1;
      triangle(a, b, c);
      triangle(b, d, c);
    }
  }
  outCtx.putImageData(image, 0, 0);
  return out;
}

/**
 * Bakes AMLL's control-point mesh warp once, then animates it with a single affine blit.
 *
 * The fragment shader's per-frame work is a rotation of the *uv* about (0.2, 0.2)
 * (`finalUV = rot(uv - 0.2) * 0.8 + 0.5`). The mesh itself never changes, so rather than
 * re-rasterising its ~800 triangles every frame (measured 0.13ms each — 130ms per frame),
 * the warped texture is rasterised once and the rotation is applied to the result. Rotating
 * the warped image differs from rotating the uv before the warp only by the mesh's own
 * distortion, which on a wash this soft is invisible.
 *
 * The baked frame is mirror-tiled so the rotating corners stay filled, standing in for
 * the MIRRORED_REPEAT wrap AMLL sets on its texture. A static vignette is composited over
 * the result, matching `mask = 0.6 + smoothstep(0.8, 0.3, dist) * 0.4`.
 *
 * Returns a `drawBackdrop(target, elapsedMs)` closure. Async because the baked frame is
 * decoded once through `loadImage`.
 */
async function createBackdrop(texture, mesh, vignette) {
  const N = texture.width;
  const source = buildBackdropTile(texture);
  const scale = BACKDROP_TILE_SCALE;
  const tile = createCanvas(source.width * scale, source.height * scale);
  const tileCtx = tile.getContext('2d');
  tileCtx.imageSmoothingEnabled = true;
  tileCtx.imageSmoothingQuality = 'high';
  tileCtx.drawImage(source, 0, 0, tile.width, tile.height);
  const S = N * scale;
  const width = BACKDROP_MESH_WIDTH;
  const height = BACKDROP_MESH_HEIGHT;

  // Each quad is split into two triangles with AMLL's index order (TL–TR–BL and
  // TR–BR–BL), not the other diagonal: the two must share the TL–BR diagonal, or the
  // triangles leave a wedge of the quad uncovered.
  //
  // The warp is rasterised **in software**, not through cairo. cairo antialiases every
  // triangle's edges independently, so a tile blitted through `clip()` + `setTransform()`
  // leaves a faint dotted line along each shared edge — visible as a faint arc once the
  // mesh curves. A per-pixel barycentric fill assigns each output pixel to exactly one
  // triangle, so the seams cannot exist at all (and it measures faster than the cairo
  // path: ~280ms vs ~450ms for the full frame).
  const warped = rasterizeMeshWarp(tile, S, mesh, width, height);
  const warpedFrame = await loadImage(warped.toBuffer('image/png'));

  // Where the shader's rotation pivot (0.2, 0.2) and re-centre point (0.5, 0.5) land.
  const pivot = mesh.evaluateAt(BACKDROP_UV_PIVOT, BACKDROP_UV_PIVOT);
  const center = mesh.evaluateAt(0.5, 0.5);
  const pivotX = pivot.x * width;
  const pivotY = pivot.y * height;
  const centerX = center.x * width;
  const centerY = center.y * height;
  const magnify = 1 / BACKDROP_UV_ZOOM;

  // The frame is spun about `pivot`, so `T(x) = pivot + (1/zoom)·rot(-angle)·(x - center)`
  // maps every screen pixel back into the baked frame. Its inverse is
  // `x → center + zoom·rot(angle)·(x - pivot)`, so as `angle` sweeps each screen corner
  // traces a disc of radius `zoom·|corner - pivot|` **centred on the mesh centre** (the
  // radius is measured from the pivot, the centre is the mesh centre — getting either one
  // wrong leaves part of the frame unpainted, which is what showed as black corners). The
  // sheet is that disc's bounding box, mirror-tiled to stand in for the MIRRORED_REPEAT
  // wrap AMLL sets on its texture.
  const reach = BACKDROP_UV_ZOOM * Math.max(
    Math.hypot(pivotX, pivotY),
    Math.hypot(width - pivotX, pivotY),
    Math.hypot(pivotX, height - pivotY),
    Math.hypot(width - pivotX, height - pivotY),
  ) * 1.35;
  // The sheet's top-left is snapped to whole pixels: `drawBackdrop` blits it with nearest
  // sampling, and a fractional offset would make the mirror-tile seams land between pixels
  // and show up as a faint line. The sheet is padded by the 2px the rounding can move it.
  const offX = Math.round(centerX - reach);
  const offY = Math.round(centerY - reach);
  const sheetSize = Math.ceil(reach * 2) + 4;
  const sheet = createCanvas(sheetSize, sheetSize);
  const sheetCtx = sheet.getContext('2d');
  // Cover the whole sheet with mirror tiles. Tile `n` covers source `[n·w, (n+1)·w]`; odd
  // tiles are reflected, which is exactly MIRRORED_REPEAT. The reflection is done about the
  // tile's own edge (`translate(n·w); scale(-1, 1)` then blit at 0) so a flipped tile still
  // lands in its own cell — shifting by the image size instead leaves a one-tile gap.
  const nxMin = Math.floor(offX / width) - 1;
  const nxMax = Math.ceil((offX + sheetSize) / width) + 1;
  const nyMin = Math.floor(offY / height) - 1;
  const nyMax = Math.ceil((offY + sheetSize) / height) + 1;
  for (let ny = nyMin; ny <= nyMax; ny++) {
    for (let nx = nxMin; nx <= nxMax; nx++) {
      sheetCtx.save();
      sheetCtx.translate(nx * width - offX, ny * height - offY);
      if (nx & 1) { sheetCtx.translate(width, 0); sheetCtx.scale(-1, 1); }
      if (ny & 1) { sheetCtx.translate(0, height); sheetCtx.scale(1, -1); }
      sheetCtx.drawImage(warpedFrame, 0, 0);
      sheetCtx.restore();
    }
  }

  return function drawBackdrop(target, elapsedMs) {
    const t = elapsedMs / 1000;

    target.setTransform(1, 0, 0, 1, 0, 0);
    target.globalAlpha = 1.0;
    target.globalCompositeOperation = 'source-over';
    // Deep dark background fill
    target.fillStyle = '#05070d';
    target.fillRect(0, 0, width, height);

    // Layer 1: Deep rolling fluid swell (harmonic multi-frequency wave motion)
    const rot1 = Math.sin(t * 0.13) * 0.32 + Math.cos(t * 0.08) * 0.18 + t * 0.035;
    const sx1 = 1.10 + 0.14 * Math.sin(t * 0.21);
    const sy1 = 1.10 + 0.14 * Math.cos(t * 0.16);
    const dx1 = Math.sin(t * 0.17) * 140 + Math.cos(t * 0.27) * 60;
    const dy1 = Math.cos(t * 0.14) * 160 + Math.sin(t * 0.23) * 70;
    const kx1 = 0.10 * Math.sin(t * 0.24);

    target.save();
    target.imageSmoothingEnabled = false;
    target.translate(centerX + dx1, centerY + dy1);
    target.rotate(rot1);
    target.transform(sx1, 0, kx1, sy1, 0, 0);
    target.drawImage(sheet, -reach, -reach);
    target.restore();

    // Layer 2: Surface cross-current wave (opposing phase with screen blending)
    const rot2 = -Math.cos(t * 0.11) * 0.28 + Math.sin(t * 0.17) * 0.15 - t * 0.028;
    const sx2 = 1.16 + 0.16 * Math.cos(t * 0.19);
    const sy2 = 1.16 + 0.16 * Math.sin(t * 0.23);
    const dx2 = -Math.cos(t * 0.22) * 150 + Math.sin(t * 0.15) * 80;
    const dy2 = -Math.sin(t * 0.18) * 140 - Math.cos(t * 0.29) * 60;
    const ky2 = 0.12 * Math.cos(t * 0.20);

    target.save();
    target.globalAlpha = 0.52;
    target.globalCompositeOperation = 'screen';
    target.imageSmoothingEnabled = false;
    target.translate(centerX + dx2, centerY + dy2);
    target.rotate(rot2);
    target.transform(sx2, ky2, 0, sy2, 0, 0);
    target.drawImage(sheet, -reach, -reach);
    target.restore();

    // Layer 3: Static vignette overlay for Apple Music typography contrast
    target.setTransform(1, 0, 0, 1, 0, 0);
    target.globalAlpha = 1.0;
    target.globalCompositeOperation = 'source-over';
    target.imageSmoothingEnabled = true;
    target.drawImage(vignette, 0, 0, width, height);
  };
}

/**
 * Static vignette overlay. AMLL multiplies the frame by `mask = 0.6 + smoothstep(0.8, 0.3,
 * dist) * 0.4`; multiplying by `m` is the same as compositing `rgba(0, 0, 0, 1 - m)` over it,
 * and node-canvas' `source-over` blit is ~10x cheaper than a `multiply` blit (3ms vs 29ms at
 * 720x1280), so the mask is stored as a black overlay whose alpha is `1 - mask`.
 */
function buildBackdropVignette(width, height) {
  const canvas = createCanvas(width, height);
  const ctx = canvas.getContext('2d');
  const image = ctx.createImageData(width, height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const u = width === 1 ? 0 : x / (width - 1);
      const v = height === 1 ? 0 : y / (height - 1);
      const dist = Math.hypot(u - 0.5, v - 0.5);
      const raw = (BACKDROP_VIGNETTE_OUTER - dist) / (BACKDROP_VIGNETTE_OUTER - BACKDROP_VIGNETTE_INNER);
      const t = raw < 0 ? 0 : raw > 1 ? 1 : raw;
      const smooth = t * t * (3 - 2 * t);
      const mask = BACKDROP_VIGNETTE_BASE + smooth * (1 - BACKDROP_VIGNETTE_BASE);
      const o = (y * width + x) * 4;
      image.data[o] = 0;
      image.data[o + 1] = 0;
      image.data[o + 2] = 0;
      image.data[o + 3] = Math.round((1 - mask) * 255);
    }
  }
  ctx.putImageData(image, 0, 0);
  return canvas;
}

/**
 * node-canvas' `toBuffer('raw')` is premultiplied BGRA. ffmpeg's `overlay` filter expects
 * straight alpha, so the buffer is un-premultiplied in place before it is piped; doing it
 * here (rather than with an ffmpeg filter) keeps the pixel values exact and costs ~4ms/frame.
 */
function unpremultiplyBgra(buffer) {
  for (let i = 0; i < buffer.length; i += 4) {
    const a = buffer[i + 3];
    if (a === 0) { buffer[i] = 0; buffer[i + 1] = 0; buffer[i + 2] = 0; continue; }
    if (a === 255) continue;
    const f = 255 / a;
    const b = buffer[i] * f;
    const g = buffer[i + 1] * f;
    const r = buffer[i + 2] * f;
    buffer[i] = b > 255 ? 255 : b | 0;
    buffer[i + 1] = g > 255 ? 255 : g | 0;
    buffer[i + 2] = r > 255 ? 255 : r | 0;
  }
  return buffer;
}

async function writeWithBackpressure(stream, buffer) {
  if (stream.destroyed || stream.writableEnded) throw new Error('FFmpeg berhenti sebelum render selesai.');
  if (stream.write(buffer)) return;
  await once(stream, 'drain');
}

async function renderVideo(meta, audioPath, coverPath, lyrics, romanizedLines, outputPath, onProgress) {
  const cover = await loadImage(coverPath);
  const canvas = createCanvas(WIDTH, HEIGHT);
  const ctx = canvas.getContext('2d');
  ctx.textBaseline = 'alphabetic';
  // Lyrics are drawn onto their own transparent layer so the animated backdrop underneath
  // survives `drawLyricsFrame`'s clear; the two are composited once per frame.
  const lyricCanvas = createCanvas(WIDTH, HEIGHT);
  const lyricCtx = lyricCanvas.getContext('2d');
  lyricCtx.textBaseline = 'alphabetic';
  const durationMs = Math.round(meta.duration * 1000);
  const lines = lyrics.lines;
  // Script census for the whole song, computed once, so each line's per-word romanization is
  // routed to the same engine `romanizeLyrics` used for the whole-line text.
  const romanCtx = detectSongScript(lines);

  const preparedLines = [];
  for (let index = 0; index < lines.length; index++) {
    const line = lines[index];
    const lineLevel = !(line.words?.length);
    const visualWords = lineLevel ? [] : line.words;
    const wholeRoman = romanizedLines?.[index] ?? null;
    const groups = lineLevel ? null : groupSyllablesIntoWords(line.text, line.words);
    // A line without word timing is swept as one unit (Spotify-style); its window is
    // precomputed here so the per-frame loop only reads it.
    const sweep = lineLevel ? lineSweepWindow(line, lines[index + 1], durationMs) : null;
    // The romanization runs its own per-word wipe across the line's sung window: the word timings
    // when the line is word-synced, otherwise the line-level sweep window.
    const romanWindow = lineLevel
      ? sweep
      : {
          startMs: line.words[0].startMs,
          endMs: line.words[line.words.length - 1].endMs,
        };

    // Approach A: per-word romanization anchored 1:1 to each original word group (word-synced
    // lines only). The guard falls back to the whole-line text whenever the per-word pass would
    // change the romanization (lost inter-word context, e.g. Japanese particles / Korean finals).
    let perWord = null;
    if (wholeRoman && groups?.length) {
      perWord = await buildRomanSegments(line, romanCtx).catch(() => null);
      if (perWord && !sameRomanization(perWord.text, wholeRoman)) perWord = null;
    }
    const romanText = perWord ? perWord.text : wholeRoman;

    const layout = layoutLine(lyricCtx, line.text, visualWords, romanText);

    // Timing: per-word anchored (A), line-level linear sweep (unchanged), whole-line mapped
    // through the original word timing curve (B), or the safety-net linear window.
    if (perWord) attachRomanTiming(layout.romanRows, perWord.words);
    else if (lineLevel) assignRomanTiming(layout.romanRows, sweep);
    else if (wholeRoman && groups?.length) assignRomanTimingCurve(layout.romanRows, groups);
    else assignRomanTiming(layout.romanRows, romanWindow);

    // One pre-rendered strip per blur level: the sharp copy feeds the karaoke glow, and the
    // blurred copies are used by the inactive lines for depth blur. Background vocals bake their
    // dimmer opacity in, so they can still be drawn from a strip while the main lines animate.
    // The depth strips include the romanization; the karaoke glow is built from the main rows
    // only, so the secondary line never glows.
    const baseOpacity = line.background ? LYRIC_BG_ALPHA : 1;
    const ops = lineDrawOps(layout);
    const blurs = [];
    for (const radius of LYRIC_BLUR_RADII) blurs.push(await renderStrip(ops, layout.blockHeight, radius, baseOpacity));
    const glow = await renderStrip(mainRowOps(layout), layout.rows.length * LYRIC_ROW_HEIGHT, LYRIC_GLOW_BLUR, baseOpacity);
    // The romanization has its own held-word glow strip, positioned relative to the roman block.
    const romanOps = romanRowOps(layout);
    const romanGlow = romanOps.length
      ? await renderStrip(romanOps, layout.blockHeight, LYRIC_GLOW_BLUR, baseOpacity)
      : null;
    preparedLines.push({
      ...line, lineLevel, sweep, font: layout.font, rows: layout.rows, rowCount: layout.rowCount,
      romanFont: layout.romanFont, romanRows: layout.romanRows, blockHeight: layout.blockHeight,
      glow, romanGlow, blurs,
    });
  }
  const prepared = { lines: preparedLines, items: buildItems(lines), header: buildHeader(cover, meta) };

  const backdropTexture = await buildBackdropTexture(coverPath);
  const backdropMesh = buildBackdropMesh(MESH_SUBDIVISIONS);
  const backdropVignette = buildBackdropVignette(BACKDROP_MESH_WIDTH, BACKDROP_MESH_HEIGHT);
  const drawBackdrop = await createBackdrop(backdropTexture, backdropMesh, backdropVignette);

  const frames = Math.ceil(meta.duration * FPS);
  const args = [
    '-hide_banner', '-loglevel', 'error', '-y',
    '-f', 'rawvideo', '-pixel_format', 'bgra', '-video_size', `${WIDTH}x${HEIGHT}`, '-framerate', String(FPS), '-i', 'pipe:0',
    '-i', audioPath,
    '-map', `${RAW_INPUT}:v`, '-map', `${AUDIO_INPUT}:a:0`, '-t', String(meta.duration), '-r', String(FPS),
    '-c:v', 'libx264', '-preset', 'veryfast', '-crf', '20', '-pix_fmt', 'yuv420p',
    '-c:a', 'aac', '-b:a', '96k', '-movflags', '+faststart', outputPath,
  ];
  const ff = spawn('ffmpeg', args, { windowsHide: true, stdio: ['pipe', 'ignore', 'pipe'] });
  let ffError = '';
  let childError = null;
  ff.stderr.on('data', chunk => { ffError += chunk.toString(); if (ffError.length > 32000) ffError = ffError.slice(-32000); });
  ff.stdin.on('error', err => { childError = err; });
  const closePromise = new Promise((resolve, reject) => {
    ff.on('error', reject);
    ff.on('close', code => code === 0 ? resolve() : reject(new Error(ffError.trim() || childError?.message || `FFmpeg exited with ${code}`)));
  });
  try {
    for (let frame = 0; frame < frames; frame++) {
      if (childError) throw childError;
      const elapsedMs = Math.min(durationMs, Math.round(frame * 1000 / FPS));
      drawBackdrop(ctx, elapsedMs);
      lyricCtx.clearRect(0, 0, WIDTH, HEIGHT);
      drawLyricsFrame(lyricCtx, prepared, elapsedMs, durationMs);
      ctx.drawImage(lyricCanvas, 0, 0);
      // The backdrop is opaque, so every pixel already has alpha 255 and node-canvas' raw BGRA
      // is effectively straight — no un-premultiply pass is needed here.
      await writeWithBackpressure(ff.stdin, canvas.toBuffer('raw'));
      if (frame % (FPS * 3) === 0 && onProgress) {
        const percent = Math.min(99, Math.round((frame / frames) * 100));
        onProgress({
          stage: 'render',
          seconds: Math.min(meta.duration, frame / FPS),
          duration: meta.duration,
          frame,
          totalFrames: frames,
          percent,
          meta,
          lyrics,
        });
      }
    }
    ff.stdin.end();
    if (onProgress) {
      onProgress({
        stage: 'finishing',
        seconds: meta.duration,
        duration: meta.duration,
        frame: frames,
        totalFrames: frames,
        percent: 100,
        meta,
        lyrics,
      });
    }
    await closePromise;
  } catch (error) {
    try { ff.stdin.destroy(); } catch {}
    try { ff.kill('SIGKILL'); } catch {}
    throw error;
  }
  const stat = await fsp.stat(outputPath);
  if (stat.size < 100 * 1024) throw new Error('Video hasil render terlalu kecil atau kosong.');
}

/** Thrown when the caller's `onConfirm` declines to continue after a lyric warning. */
class LyricVideoCancelled extends Error {
  constructor(reason) {
    super('Pembuatan video lirik dibatalkan.');
    this.name = 'LyricVideoCancelled';
    this.cancelled = true;
    this.reason = reason || null;
  }
}

async function createLyricVideo(input, options = {}) {
  const tempDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'wa-lyricvideo-'));
  let keep = false;
  try {
    if (options.onProgress) await options.onProgress({ stage: 'search' });
    const meta = await getVideoMetadata(String(input || '').trim());
    if (options.onProgress) await options.onProgress({ stage: 'lyrics', meta });
    // Romanization-aware: this also decides whether the caller has to confirm anything, and it
    // runs before the download so a cancelled job never pays for the audio/cover fetch.
    const { lyrics, romanizedLines, romanizedSource, warnings, romanized } = await resolveLyrics(meta);
    if (warnings.length && typeof options.onConfirm === 'function') {
      const proceed = await options.onConfirm({ meta, lyrics, warnings, romanized });
      if (!proceed) throw new LyricVideoCancelled(warnings);
    }
    if (options.onProgress) await options.onProgress({ stage: 'download', meta, lyrics });
    const [audioPath, coverPath] = await Promise.all([downloadAudio(meta, tempDir), downloadCover(meta, tempDir)]);
    if (options.onProgress) await options.onProgress({ stage: 'render', meta, lyrics });
    const outputPath = path.join(tempDir, 'lyric-video.mp4');
    await renderVideo(meta, audioPath, coverPath, lyrics, romanizedLines, outputPath, options.onProgress);
    keep = true;
    return {
      outputPath,
      tempDir,
      title: meta.title,
      artist: meta.artist,
      duration: meta.duration,
      source: lyrics.provider,
      wordSynced: lyrics.wordSynced,
      romanized,
      romanizedSource,
      warnings,
      // `approximate` is true only for the LRCLIB plain-text fallback, whose line timestamps
      // are themselves guessed. A line-level source is still accurately timed per line (it is
      // swept as one fill), so it is not "approximate" — it is simply `lineLevel`.
      lineLevel: !lyrics.wordSynced,
      approximateTiming: Boolean(lyrics.approximate),
      cleanup: async () => fsp.rm(tempDir, { recursive: true, force: true }),
    };
  } finally {
    if (!keep) await fsp.rm(tempDir, { recursive: true, force: true }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// [REMOTE RENDER] helper CDN + GitHub API
// ---------------------------------------------------------------------------

async function cdnUpload(buffer, filename, contentType) {
  const cfg = getRemoteConfig();
  const form = new FormData();
  form.append('file', new Blob([buffer], { type: contentType || 'application/octet-stream' }), filename);
  const res = await fetch(cfg.cdnApiBase + '/v1/upload', {
    method: 'POST',
    headers: { Authorization: 'Bearer ' + cfg.cdnApiKey },
    body: form,
  });
  const text = await res.text();
  let data = {};
  try { data = JSON.parse(text); } catch (_) {}
  if (!res.ok || !data.success || !data.url) {
    throw new Error('CDN upload gagal: HTTP ' + res.status + ' ' + text.slice(0, 200));
  }
  return data;
}

async function cdnDelete(key) {
  const cfg = getRemoteConfig();
  if (!key) return;
  try {
    await fetch(cfg.cdnApiBase + '/v1/files/' + key, {
      method: 'DELETE',
      headers: { Authorization: 'Bearer ' + cfg.cdnApiKey },
    });
  } catch (_) {}
}

async function ghApi(pathname, options = {}) {
  const cfg = getRemoteConfig();
  if (!cfg.githubRepo || !cfg.githubToken) {
    throw new Error('githubRepo/githubToken belum diisi di global.lyricVideoRemote');
  }
  const res = await fetch('https://api.github.com/repos/' + cfg.githubRepo + pathname, {
    ...options,
    headers: {
      Accept: 'application/vnd.github+json',
      Authorization: 'Bearer ' + cfg.githubToken,
      'X-GitHub-Api-Version': '2022-11-28',
      ...(options.headers || {}),
    },
  });
  const text = await res.text();
  let data = {};
  try { data = JSON.parse(text); } catch (_) {}
  return { ok: res.ok, status: res.status, data, text };
}

// ---------------------------------------------------------------------------
// [REMOTE RENDER] Fase panel: metadata + lirik + konfirmasi + yt-dlp + CDN.
// ---------------------------------------------------------------------------

async function prepareLyricVideo(input, options = {}) {
  const tempDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'wa-lyricvideo2-'));
  if (options.onProgress) await options.onProgress({ stage: 'search' });
  const meta = await getVideoMetadata(String(input || '').trim());
  if (options.onProgress) await options.onProgress({ stage: 'lyrics', meta });
  const resolved = await resolveLyrics(meta);
  const { lyrics, romanizedLines, romanizedSource, warnings, romanized } = resolved;
  if (warnings.length && typeof options.onConfirm === 'function') {
    if (!(await options.onConfirm({ meta, lyrics, warnings, romanized }))) {
      await fsp.rm(tempDir, { recursive: true, force: true }).catch(() => {});
      throw new LyricVideoCancelled(warnings);
    }
  }
  if (options.onProgress) await options.onProgress({ stage: 'download', meta, lyrics });
  const [audioPath, coverPath] = await Promise.all([downloadAudio(meta, tempDir), downloadCover(meta, tempDir)]);
  return { tempDir, meta, lyrics, romanizedLines, romanizedSource, warnings, romanized, audioPath, coverPath };
}

// Dipakai scripts/lyric-video-worker.js di GitHub Actions.
async function renderLyricVideoJob(job, audioPath, coverPath, outputPath, onProgress) {
  if (!job || !job.meta || !job.lyrics) throw new Error('Job tidak valid');
  await renderVideo(job.meta, audioPath, coverPath, job.lyrics, job.romanizedLines || [], outputPath, onProgress);
}

module.exports = {
  createLyricVideo,
  LyricVideoCancelled,
  getRemoteConfig,
  cdnUpload,
  cdnDelete,
  ghApi,
  prepareLyricVideo,
  renderLyricVideoJob,
};
