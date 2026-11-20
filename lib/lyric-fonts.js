'use strict';

/**
 * Per-script font resolution for the lyric renderer.
 *
 * node-canvas leans on Pango for glyph fallback, but that fallback is unreliable on
 * Windows, so rather than trusting one family to cover every script we detect the script
 * of each line and pick an explicit family for it. Fonts are registered from bundled
 * files first, then from the platform font directories, and finally we fall back to a
 * plain system family name so rendering never hard-fails.
 */
const fs = require('fs');
const os = require('os');
const path = require('path');

let canvasLib;
function getCanvas() {
  if (canvasLib === undefined) {
    try { canvasLib = require('canvas'); } catch { canvasLib = null; }
  }
  return canvasLib;
}

// Order matters: the first match wins, so kana is checked before Han (Japanese uses both).
const SCRIPT_RULES = [
  ['japanese', /[\u3040-\u30ff]/],
  ['korean', /[\u1100-\u11ff\u3130-\u318f\uac00-\ud7a3]/],
  ['chinese', /[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]/],
  ['thai', /[\u0e00-\u0e7f]/],
  ['devanagari', /[\u0900-\u097f]/],
  ['bengali', /[\u0980-\u09ff]/],
  ['tamil', /[\u0b80-\u0bff]/],
  ['telugu', /[\u0c00-\u0c7f]/],
  ['arabic', /[\u0600-\u06ff\u0750-\u077f\ufb50-\ufdff\ufe70-\ufeff]/],
  ['hebrew', /[\u0590-\u05ff]/],
  ['greek', /[\u0370-\u03ff]/],
  ['cyrillic', /[\u0400-\u04ff]/],
];

// Candidate font files per script (lowercase basenames) plus the system families used
// when no file can be registered.
const FONT_CANDIDATES = {
  latin: {
    // Roboto is the reference player's typeface (Metrolist/utaloom run on Android, whose
    // default is Roboto). Its metrics were matched against the reference frames, so the
    // bundled Roboto files are preferred and the other faces are only a safety net.
    regular: ['Roboto-Regular.ttf', 'FontsFree-Net-SFProText-Semibold.ttf', 'NotoSans-Regular.ttf', 'arial.ttf', 'segoeui.ttf'],
    bold: ['Roboto-Bold.ttf', 'FontsFree-Net-SFProText-Semibold.ttf', 'NotoSans-Bold.ttf', 'arialbd.ttf', 'segoeuib.ttf'],
    families: ['Roboto', 'SF Pro Text', 'Arial', 'Segoe UI', 'Noto Sans'],
  },
  japanese: {
    regular: ['NotoSansCJK-Regular.ttc', 'NotoSansJP-Regular.otf', 'yugothr.ttc', 'msgothic.ttc', 'meiryo.ttc'],
    bold: ['NotoSansCJK-Bold.ttc', 'NotoSansJP-Bold.otf', 'yugothb.ttc', 'msgothic.ttc', 'meiryob.ttc'],
    families: ['Noto Sans CJK JP', 'Yu Gothic', 'MS Gothic', 'Meiryo', 'Microsoft YaHei'],
  },
  korean: {
    regular: ['NotoSansCJK-Regular.ttc', 'NotoSansKR-Regular.otf', 'malgun.ttf'],
    bold: ['NotoSansCJK-Bold.ttc', 'NotoSansKR-Bold.otf', 'malgunbd.ttf'],
    families: ['Noto Sans CJK KR', 'Malgun Gothic'],
  },
  chinese: {
    regular: ['NotoSansCJK-Regular.ttc', 'NotoSansSC-Regular.otf', 'NotoSansTC-Regular.otf', 'msyh.ttc', 'simsun.ttc'],
    bold: ['NotoSansCJK-Bold.ttc', 'NotoSansSC-Bold.otf', 'msyhbd.ttc', 'simsun.ttc'],
    families: ['Noto Sans CJK SC', 'Microsoft YaHei', 'SimSun'],
  },
  thai: {
    regular: ['NotoSansThai-Regular.ttf', 'leelawui.ttf', 'tahoma.ttf'],
    bold: ['NotoSansThai-Bold.ttf', 'leelauib.ttf', 'tahomabd.ttf'],
    families: ['Noto Sans Thai', 'Leelawadee UI', 'Tahoma'],
  },
  devanagari: {
    regular: ['NotoSansDevanagari-Regular.ttf', 'nirmala.ttf', 'mangal.ttf'],
    bold: ['NotoSansDevanagari-Bold.ttf', 'nirmalab.ttf', 'mangalb.ttf'],
    families: ['Noto Sans Devanagari', 'Nirmala UI', 'Mangal'],
  },
  bengali: {
    regular: ['NotoSansBengali-Regular.ttf', 'nirmala.ttf', 'vrinda.ttf'],
    bold: ['NotoSansBengali-Bold.ttf', 'nirmalab.ttf', 'vrindab.ttf'],
    families: ['Noto Sans Bengali', 'Nirmala UI', 'Vrinda'],
  },
  tamil: {
    regular: ['NotoSansTamil-Regular.ttf', 'nirmala.ttf', 'latha.ttf'],
    bold: ['NotoSansTamil-Bold.ttf', 'nirmalab.ttf', 'lathab.ttf'],
    families: ['Noto Sans Tamil', 'Nirmala UI', 'Latha'],
  },
  telugu: {
    regular: ['NotoSansTelugu-Regular.ttf', 'nirmala.ttf', 'gautami.ttf'],
    bold: ['NotoSansTelugu-Bold.ttf', 'nirmalab.ttf', 'gautamib.ttf'],
    families: ['Noto Sans Telugu', 'Nirmala UI', 'Gautami'],
  },
  arabic: {
    regular: ['NotoSansArabic-Regular.ttf', 'segoeui.ttf', 'tahoma.ttf', 'arial.ttf'],
    bold: ['NotoSansArabic-Bold.ttf', 'segoeuib.ttf', 'tahomabd.ttf', 'arialbd.ttf'],
    families: ['Noto Sans Arabic', 'Segoe UI', 'Tahoma', 'Arial'],
  },
  hebrew: {
    regular: ['NotoSansHebrew-Regular.ttf', 'segoeui.ttf', 'arial.ttf'],
    bold: ['NotoSansHebrew-Bold.ttf', 'segoeuib.ttf', 'arialbd.ttf'],
    families: ['Noto Sans Hebrew', 'Segoe UI', 'Arial'],
  },
  greek: {
    regular: ['NotoSans-Regular.ttf', 'segoeui.ttf', 'arial.ttf', 'DejaVuSans.ttf'],
    bold: ['NotoSans-Bold.ttf', 'segoeuib.ttf', 'arialbd.ttf', 'DejaVuSans-Bold.ttf'],
    families: ['Segoe UI', 'Arial', 'DejaVu Sans', 'Noto Sans'],
  },
  cyrillic: {
    regular: ['NotoSans-Regular.ttf', 'segoeui.ttf', 'arial.ttf', 'DejaVuSans.ttf'],
    bold: ['NotoSans-Bold.ttf', 'segoeuib.ttf', 'arialbd.ttf', 'DejaVuSans-Bold.ttf'],
    families: ['Segoe UI', 'Arial', 'DejaVu Sans', 'Noto Sans'],
  },
};

const GENERIC_FAMILIES = new Set(['sans-serif', 'serif', 'monospace', 'cursive', 'fantasy']);

// Files that are already a semibold/demibold face: asking Canvas for `bold` on top of them
// makes it synthesise a heavier, rougher stroke, so the weight prefix is dropped instead.
const PREBOLD_FILE = /semibold|demibold|[-_]sb\b|[-_]600\b/i;

let fontIndex = null;
let registered = false;
const resolved = {};

function buildIndex() {
  const index = new Map();
  const dirs = [path.join(__dirname, 'font')];
  if (process.platform === 'win32') {
    dirs.push(path.join(process.env.WINDIR || 'C:\\Windows', 'Fonts'));
  } else {
    dirs.push('/usr/share/fonts', '/usr/local/share/fonts', path.join(os.homedir(), '.fonts'), path.join(os.homedir(), '.local/share/fonts'));
  }
  for (const dir of dirs) walk(dir, index, 0);
  return index;
}

function walk(dir, index, depth) {
  if (depth > 5) return;
  let entries;
  try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      walk(full, index, depth + 1);
    } else if (/\.(ttf|otf|ttc|otc)$/i.test(entry.name)) {
      const key = entry.name.toLowerCase();
      if (!index.has(key)) index.set(key, full);
    }
  }
}

function findFont(names, index) {
  for (const name of names) {
    const hit = index.get(name.toLowerCase());
    if (hit) return hit;
  }
  return null;
}

function ensureRegistered() {
  if (registered) return;
  registered = true;
  fontIndex = buildIndex();
  const canvas = getCanvas();
  const canRegister = canvas && typeof canvas.registerFont === 'function';
  for (const script of Object.keys(FONT_CANDIDATES)) {
    const cfg = FONT_CANDIDATES[script];
    const alias = `Lyric-${script}`;
    const regular = canRegister ? findFont(cfg.regular, fontIndex) : null;
    if (regular) {
      try {
        canvas.registerFont(regular, { family: alias });
        const boldFile = findFont(cfg.bold, fontIndex);
        let bold = false;
        if (boldFile) {
          try { canvas.registerFont(boldFile, { family: alias, weight: 'bold' }); bold = true; } catch { bold = false; }
        }
        resolved[script] = {
          family: alias,
          bold,
          // The chosen regular file may already be a semibold face; then `bold` must not be
          // requested again or Canvas fakes the extra weight and the glyphs look coarse.
          prebold: PREBOLD_FILE.test(path.basename(regular)),
        };
        continue;
      } catch { /* fall through to system family names */ }
    }
    resolved[script] = { family: null, bold: true, prebold: false };
  }
}

function detectScript(text) {
  const value = String(text || '');
  for (const [name, re] of SCRIPT_RULES) {
    if (re.test(value)) return name;
  }
  return 'latin';
}

function quoteFamily(name) {
  if (GENERIC_FAMILIES.has(name)) return name;
  return /^[a-z0-9-]+$/i.test(name) ? name : `"${name}"`;
}

/**
 * Returns a CSS font shorthand for the script that [text] uses, e.g.
 * `bold 42px "Lyric-chinese", sans-serif`. Callers set it straight on `ctx.font`.
 */
function resolveFont(text, size = 42, weight = 'bold') {
  ensureRegistered();
  const script = detectScript(text);
  const entry = resolved[script] || { family: null, bold: true, prebold: false };
  const families = entry.family ? [entry.family] : (FONT_CANDIDATES[script]?.families || ['Arial']);
  const list = [...families, 'sans-serif'].map(quoteFamily).join(', ');
  const dropBold = weight === 'bold' && entry.family && (entry.bold === false || entry.prebold);
  const prefix = !dropBold && weight && weight !== 'normal' ? `${weight} ` : '';
  return `${prefix}${size}px ${list}`;
}

module.exports = { resolveFont, detectScript };
