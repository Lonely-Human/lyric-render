'use strict';

/**
 * Offline lyric romanization, ported from cabrata/utaloom's
 * `app/src/main/kotlin/com/utaloom/lyrics/Romanization.kt` (GPL-3.0, itself derived from
 * Metrolist). Covers the same languages as the Android app:
 *
 *   Japanese (kuromoji + wanakana), Korean (romaja), Chinese (pinyin-pro),
 *   Hindi (Devanagari), Punjabi (Gurmukhi) and the Cyrillic languages
 *   (Russian, Ukrainian, Serbian, Bulgarian, Belarusian, Kyrgyz, Macedonian).
 *
 * The line count and indices of the input are preserved exactly (`string|null` per line) so a
 * romanized secondary line can be mapped back to the original line's karaoke timing.
 *
 * Only the tables/algorithms that cannot be served by a JS library are ported verbatim; the
 * kana→romaji map is replaced by `wanakana.toRomaji` and TinyPinyin by `pinyin-pro`.
 */
const fs = require('fs');
const path = require('path');
const kuromoji = require('kuromoji');
const wanakana = require('wanakana');
const { pinyin } = require('pinyin-pro');

/** Languages that can be auto-detected and romanized, mirroring the Android app. */
const SUPPORTED_LANGUAGES = [
  'Japanese', 'Korean', 'Chinese', 'Hindi', 'Punjabi',
  'Russian', 'Ukrainian', 'Serbian', 'Bulgarian', 'Belarusian', 'Kyrgyz', 'Macedonian',
];

// ---------------------------------------------------------------------------------------------
// Tables (ported verbatim from Romanization.kt)
// ---------------------------------------------------------------------------------------------

const HANGUL_ROMAJA_MAP = {
  cho: {
    'ᄀ': 'g', 'ᄁ': 'kk', 'ᄂ': 'n', 'ᄃ': 'd',
    'ᄄ': 'tt', 'ᄅ': 'r', 'ᄆ': 'm', 'ᄇ': 'b',
    'ᄈ': 'pp', 'ᄉ': 's', 'ᄊ': 'ss', 'ᄋ': '',
    'ᄌ': 'j', 'ᄍ': 'jj', 'ᄎ': 'ch', 'ᄏ': 'k',
    'ᄐ': 't', 'ᄑ': 'p', 'ᄒ': 'h',
  },
  jung: {
    'ᅡ': 'a', 'ᅢ': 'ae', 'ᅣ': 'ya', 'ᅤ': 'yae',
    'ᅥ': 'eo', 'ᅦ': 'e', 'ᅧ': 'yeo', 'ᅨ': 'ye',
    'ᅩ': 'o', 'ᅪ': 'wa', 'ᅫ': 'wae', 'ᅬ': 'oe',
    'ᅭ': 'yo', 'ᅮ': 'u', 'ᅯ': 'wo', 'ᅰ': 'we',
    'ᅱ': 'wi', 'ᅲ': 'yu', 'ᅳ': 'eu', 'ᅴ': 'eui',
    'ᅵ': 'i',
  },
  jong: {
    'ᆨ': 'k', 'ᆨᄋ': 'g', 'ᆨᄂ': 'ngn', 'ᆨᄅ': 'ngn', 'ᆨᄆ': 'ngm', 'ᆨᄒ': 'kh',
    'ᆩ': 'kk', 'ᆩᄋ': 'kg', 'ᆩᄂ': 'ngn', 'ᆩᄅ': 'ngn', 'ᆩᄆ': 'ngm', 'ᆩᄒ': 'kh',
    'ᆪ': 'k', 'ᆪᄋ': 'ks', 'ᆪᄂ': 'ngn', 'ᆪᄅ': 'ngn', 'ᆪᄆ': 'ngm', 'ᆪᄒ': 'kch',
    'ᆫ': 'n', 'ᆫᄅ': 'll', 'ᆬ': 'n', 'ᆬᄋ': 'nj', 'ᆬᄂ': 'nn', 'ᆬᄅ': 'nn',
    'ᆬᄆ': 'nm', 'ᆬㅎ': 'nch', 'ᆭ': 'n', 'ᆭᄋ': 'nh', 'ᆭᄅ': 'nn', 'ᆮ': 't',
    'ᆮᄋ': 'd', 'ᆮᄂ': 'nn', 'ᆮᄅ': 'nn', 'ᆮᄆ': 'nm', 'ᆮᄒ': 'th', 'ᆯ': 'l',
    'ᆯᄋ': 'r', 'ᆯᄂ': 'll', 'ᆯᄅ': 'll', 'ᆰ': 'k', 'ᆰᄋ': 'lg', 'ᆰᄂ': 'ngn',
    'ᆰᄅ': 'ngn', 'ᆰᄆ': 'ngm', 'ᆰᄒ': 'lkh', 'ᆱ': 'm', 'ᆱᄋ': 'lm', 'ᆱᄂ': 'mn',
    'ᆱᄅ': 'mn', 'ᆱᄆ': 'mm', 'ᆱᄒ': 'lmh', 'ᆲ': 'p', 'ᆲᄋ': 'lb', 'ᆲᄂ': 'mn',
    'ᆲᄅ': 'mn', 'ᆲᄆ': 'mm', 'ᆲᄒ': 'lph', 'ᆳ': 't', 'ᆳᄋ': 'ls', 'ᆳᄂ': 'nn',
    'ᆳᄅ': 'nn', 'ᆳᄆ': 'nm', 'ᆳᄒ': 'lsh', 'ᆴ': 't', 'ᆴᄋ': 'lt', 'ᆴᄂ': 'nn',
    'ᆴᄅ': 'nn', 'ᆴᄆ': 'nm', 'ᆴᄒ': 'lth', 'ᆵ': 'p', 'ᆵᄋ': 'lp', 'ᆵᄂ': 'mn',
    'ᆵᄅ': 'mn', 'ᆵᄆ': 'mm', 'ᆵᄒ': 'lph', 'ᆶ': 'l', 'ᆶᄋ': 'lh', 'ᆶᄂ': 'll',
    'ᆶᄅ': 'll', 'ᆶᄆ': 'lm', 'ᆶᄒ': 'lh', 'ᆷ': 'm', 'ᆷᄅ': 'mn', 'ᆸ': 'p',
    'ᆸᄋ': 'b', 'ᆸᄂ': 'mn', 'ᆸᄅ': 'mn', 'ᆸᄆ': 'mm', 'ᆸᄒ': 'ph', 'ᆹ': 'p',
    'ᆹᄋ': 'ps', 'ᆹᄂ': 'mn', 'ᆹᄅ': 'mn', 'ᆹᄆ': 'mm', 'ᆹᄒ': 'psh', 'ᆺ': 't',
    'ᆺᄋ': 's', 'ᆺᄂ': 'nn', 'ᆺᄅ': 'nn', 'ᆺᄆ': 'nm', 'ᆺᄒ': 'sh', 'ᆻ': 't',
    'ᆻᄋ': 'ss', 'ᆻᄂ': 'tn', 'ᆻᄅ': 'tn', 'ᆻᄆ': 'nm', 'ᆻᄒ': 'th', 'ᆼ': 'ng',
    'ᆽ': 't', 'ᆽᄋ': 'j', 'ᆽᄂ': 'nn', 'ᆽᄅ': 'nn', 'ᆽᄆ': 'nm', 'ᆽᄒ': 'ch',
    'ᆾ': 't', 'ᆾᄋ': 'ch', 'ᆾᄂ': 'nn', 'ᆾᄅ': 'nn', 'ᆾᄆ': 'nm', 'ᆾᄒ': 'ch',
    'ᆿ': 'k', 'ᆿᄋ': 'k', 'ᆿᄂ': 'ngn', 'ᆿᄅ': 'ngn', 'ᆿᄆ': 'ngm', 'ᆿᄒ': 'kh',
    'ᇀ': 't', 'ᇀᄋ': 't', 'ᇀᄂ': 'nn', 'ᇀᄅ': 'nn', 'ᇀᄆ': 'nm', 'ᇀᄒ': 'th',
    'ᇁ': 'p', 'ᇁᄋ': 'p', 'ᇁᄂ': 'mn', 'ᇁᄅ': 'mn', 'ᇁᄆ': 'mm', 'ᇁᄒ': 'ph',
    'ᇂ': 't', 'ᇂᄋ': 'h', 'ᇂᄂ': 'nn', 'ᇂᄅ': 'nn', 'ᇂᄆ': 'mm', 'ᇂᄒ': 't',
    'ᇂᄀ': 'k',
  },
};

const DEVANAGARI_ROMAJI_MAP = {
  'अ': 'a', 'आ': 'aa', 'इ': 'i', 'ई': 'ee', 'उ': 'u', 'ऊ': 'oo',
  'ऋ': 'ri', 'ए': 'e', 'ऐ': 'ai', 'ओ': 'o', 'औ': 'au',
  'क': 'k', 'ख': 'kh', 'ग': 'g', 'घ': 'gh', 'ङ': 'ng',
  'च': 'ch', 'छ': 'chh', 'ज': 'j', 'झ': 'jh', 'ञ': 'ny',
  'ट': 't', 'ठ': 'th', 'ड': 'd', 'ढ': 'dh', 'ण': 'n',
  'त': 't', 'थ': 'th', 'द': 'd', 'ध': 'dh', 'न': 'n',
  'प': 'p', 'फ': 'ph', 'ब': 'b', 'भ': 'bh', 'म': 'm',
  'य': 'y', 'र': 'r', 'ल': 'l', 'व': 'v',
  'श': 'sh', 'ष': 'sh', 'स': 's', 'ह': 'h',
  'क्ष': 'ksh', 'त्र': 'tr', 'ज्ञ': 'gy', 'श्र': 'shr',
  'ा': 'aa', 'ि': 'i', 'ी': 'ee', 'ु': 'u', 'ू': 'oo',
  'ृ': 'ri', 'े': 'e', 'ै': 'ai', 'ो': 'o', 'ौ': 'au',
  'ं': 'n', 'ः': 'h', 'ँ': 'n', '़': '', '्': '',
  '०': '0', '१': '1', '२': '2', '३': '3', '४': '4',
  '५': '5', '६': '6', '७': '7', '८': '8', '९': '9',
  'ॐ': 'Om', 'ऽ': '',
  'क़': 'q', 'ख़': 'kh', 'ग़': 'g', 'ज़': 'z', 'ड़': 'r', 'ढ़': 'rh', 'फ़': 'f', 'य़': 'y',
  // Decomposed characters with Nukta
  'क\u093C': 'q', 'ख\u093C': 'kh', 'ग\u093C': 'g', 'ज\u093C': 'z', 'ड\u093C': 'r',
  'ढ\u093C': 'rh', 'फ\u093C': 'f', 'य\u093C': 'y',
};

const GURMUKHI_ROMAJI_MAP = {
  'ੳ': 'o', 'ਅ': 'a', 'ੲ': 'e', 'ਸ': 's', 'ਹ': 'h',
  'ਕ': 'k', 'ਖ': 'kh', 'ਗ': 'g', 'ਘ': 'gh', 'ਙ': 'ng',
  'ਚ': 'ch', 'ਛ': 'chh', 'ਜ': 'j', 'ਝ': 'jh', 'ਞ': 'ny',
  'ਟ': 't', 'ਠ': 'th', 'ਡ': 'd', 'ਢ': 'dh', 'ਣ': 'n',
  'ਤ': 't', 'ਥ': 'th', 'ਦ': 'd', 'ਧ': 'dh', 'ਨ': 'n',
  'ਪ': 'p', 'ਫ': 'ph', 'ਬ': 'b', 'ਭ': 'bh', 'ਮ': 'm',
  'ਯ': 'y', 'ਰ': 'r', 'ਲ': 'l', 'ਵ': 'v', 'ੜ': 'r',
  'ਸ਼': 'sh', 'ਖ਼': 'kh', 'ਗ਼': 'g', 'ਜ਼': 'z', 'ਫ਼': 'f', 'ਲ਼': 'l',
  'ਾ': 'aa', 'ਿ': 'i', 'ੀ': 'ee', 'ੁ': 'u', 'ੂ': 'oo',
  'ੇ': 'e', 'ੈ': 'ai', 'ੋ': 'o', 'ੌ': 'au',
  'ੰ': 'n', 'ਂ': 'n', 'ੱ': '', '੍': '', '਼': '',
  'ੴ': 'Ek Onkar',
  '੦': '0', '੧': '1', '੨': '2', '੩': '3', '੪': '4',
  '੫': '5', '੬': '6', '੭': '7', '੮': '8', '੯': '9',
};

const GENERAL_CYRILLIC_ROMAJI_MAP = {
  'А': 'A', 'Б': 'B', 'В': 'V', 'Г': 'G', 'Ґ': 'G', 'Д': 'D',
  'Ѓ': 'Ǵ', 'Ђ': 'Đ', 'Е': 'E', 'Ё': 'Yo', 'Є': 'Ye', 'Ж': 'Zh',
  'З': 'Z', 'Ѕ': 'Dz', 'И': 'I', 'І': 'I', 'Ї': 'Yi', 'Й': 'Y',
  'Ј': 'Y', 'К': 'K', 'Л': 'L', 'Љ': 'Ly', 'М': 'M', 'Н': 'N',
  'Њ': 'Ny', 'О': 'O', 'П': 'P', 'Р': 'R', 'С': 'S', 'Т': 'T',
  'Ћ': 'Ć', 'У': 'U', 'Ў': 'Ŭ', 'Ф': 'F', 'Х': 'Kh', 'Ц': 'Ts',
  'Ч': 'Ch', 'Џ': 'Dž', 'Ш': 'Sh', 'Щ': 'Shch', 'Ъ': 'ʺ', 'Ы': 'Y',
  'Ь': 'ʹ', 'Э': 'E', 'Ю': 'Yu', 'Я': 'Ya',
  'Ѡ': 'O', 'Ѣ': 'Ya', 'Ѥ': 'Ye', 'Ѧ': 'Ya', 'Ѩ': 'Ya',
  'Ѫ': 'U', 'Ѭ': 'Yu', 'Ѯ': 'Ks', 'Ѱ': 'Ps', 'Ѳ': 'F',
  'Ѵ': 'I', 'Ѷ': 'I', 'Ғ': 'Gh', 'Ҕ': 'G', 'Җ': 'Zh',
  'Ҙ': 'Dz', 'Қ': 'Q', 'Ҝ': 'K', 'Ҟ': 'K', 'Ҡ': 'K',
  'Ң': 'Ng', 'Ҥ': 'Ng', 'Ҧ': 'P', 'Ҩ': 'O', 'Ҫ': 'S',
  'Ҭ': 'T', 'Ү': 'U', 'Ұ': 'U', 'Ҳ': 'Kh', 'Ҵ': 'Ts',
  'Ҷ': 'Ch', 'Ҹ': 'Ch', 'Һ': 'H', 'Ҽ': 'Ch', 'Ҿ': 'Ch',
  'Ќ': 'Ḱ', 'Ө': 'Ö',

  'а': 'a', 'б': 'b', 'в': 'v', 'г': 'g', 'ґ': 'g', 'д': 'd',
  'ѓ': 'ǵ', 'ђ': 'đ', 'е': 'e', 'ё': 'yo', 'є': 'ye', 'ж': 'zh',
  'з': 'z', 'ѕ': 'dz', 'и': 'i', 'і': 'i', 'ї': 'yi', 'й': 'y',
  'ј': 'y', 'к': 'k', 'л': 'l', 'љ': 'ly', 'м': 'm', 'н': 'n',
  'њ': 'ny', 'о': 'o', 'п': 'p', 'р': 'r', 'с': 's', 'т': 't',
  'ћ': 'ć', 'у': 'u', 'ў': 'ŭ', 'ф': 'f', 'х': 'kh', 'ц': 'ts',
  'ч': 'ch', 'џ': 'dž', 'ш': 'sh', 'щ': 'shch', 'ъ': 'ʺ', 'ы': 'y',
  'ь': 'ʹ', 'э': 'e', 'ю': 'yu', 'я': 'ya',
  'ѡ': 'o', 'ѣ': 'ya', 'ѥ': 'ye', 'ѧ': 'ya', 'ѩ': 'ya',
  'ѫ': 'u', 'ѭ': 'yu', 'ѯ': 'ks', 'ѱ': 'ps', 'ѳ': 'f',
  'ѵ': 'i', 'ѷ': 'i', 'ғ': 'gh', 'ҕ': 'g', 'җ': 'zh',
  'ҙ': 'dz', 'қ': 'q', 'ҝ': 'k', 'ҟ': 'k', 'ҡ': 'k',
  'ң': 'ng', 'ҥ': 'ng', 'ҧ': 'p', 'ҩ': 'o', 'ҫ': 's',
  'ҭ': 't', 'ү': 'u', 'ұ': 'u', 'ҳ': 'kh', 'ҵ': 'ts',
  'ҷ': 'ch', 'ҹ': 'ch', 'һ': 'h', 'ҽ': 'ch', 'ҿ': 'ch',
  'ќ': 'ḱ', 'ө': 'ö',
};

const RUSSIAN_ROMAJI_MAP = {
  'ого': 'ovo', 'Ого': 'Ovo', 'его': 'evo', 'Его': 'Evo',
};

const UKRAINIAN_ROMAJI_MAP = {
  'Г': 'H', 'г': 'h',
  'Ґ': 'G', 'ґ': 'g',
  'Є': 'Ye', 'є': 'ye',
  'І': 'I', 'і': 'i',
  'Ї': 'Yi', 'ї': 'yi',
};

const SERBIAN_ROMAJI_MAP = {
  'Ж': 'Ž', 'Љ': 'Lj', 'Њ': 'Nj', 'Ц': 'C', 'Ч': 'Č',
  'Џ': 'Dž', 'Ш': 'Š', 'Х': 'H',

  'ж': 'ž', 'љ': 'lj', 'њ': 'nj', 'ц': 'c', 'ч': 'č',
  'џ': 'dž', 'ш': 'š', 'х': 'h',
};

const BULGARIAN_ROMAJI_MAP = {
  'Ж': 'Zh', 'Ц': 'Ts', 'Ч': 'Ch', 'Ш': 'Sh', 'Щ': 'Sht',
  'Ъ': 'A', 'Ь': 'Y', 'Ю': 'Yu', 'Я': 'Ya',

  'ж': 'zh', 'ц': 'ts', 'ч': 'ch', 'ш': 'sh', 'щ': 'sht',
  'ъ': 'a', 'ь': 'y', 'ю': 'yu', 'я': 'ya',
};

const BELARUSIAN_ROMAJI_MAP = {
  'Г': 'H', 'г': 'h', 'Ў': 'W', 'ў': 'w',
};

const KYRGYZ_ROMAJI_MAP = {
  'Ү': 'Ü', 'ү': 'ü', 'Ы': 'Y', 'ы': 'y',
};

const MACEDONIAN_ROMAJI_MAP = {
  'Ѓ': 'Gj', 'Ѕ': 'Dz', 'И': 'I', 'Ј': 'J', 'Љ': 'Lj',
  'Њ': 'Nj', 'Ќ': 'Kj', 'Џ': 'Dž', 'Ч': 'Č', 'Ш': 'Sh',
  'Ж': 'Zh', 'Ц': 'C', 'Х': 'H',

  'ѓ': 'gj', 'ѕ': 'dz', 'и': 'i', 'ј': 'j', 'љ': 'lj',
  'њ': 'nj', 'ќ': 'kj', 'џ': 'dž', 'ч': 'č', 'ш': 'sh',
  'ж': 'zh', 'ц': 'c', 'х': 'h',

  'Ѐ': 'E', 'ѐ': 'e', 'Ѝ': 'I', 'ѝ': 'i',
};

// Detection sets (ported verbatim). Each is a Set of the letters a language is allowed to use;
// a text is that language when it contains a letter of the language and every Cyrillic character
// it has is in the set.
const toSet = str => new Set(Array.from(str));

const RUSSIAN_CYRILLIC_LETTERS = toSet(
  'АБВГДЕЁЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯ' +
  'абвгдеёжзийклмнопрстуфхцчшщъыьэюя',
);

const UKRAINIAN_CYRILLIC_LETTERS = toSet(
  'АБВГҐДЕЄЖЗИІЇЙКЛМНОПРСТУФХЦЧШЩЬЮЯ' +
  'абвгґдеєжзиіїйклмнопрстуфхцчшщьюя',
);

const SERBIAN_CYRILLIC_LETTERS = toSet(
  'АБВГДЂЕЖЗИЈКЛЉМНЊОПРСТЋУФХЦЧЏШ' +
  'абвгдђежзијклљмнњопрстћуфхцчџш',
);

const BULGARIAN_CYRILLIC_LETTERS = toSet(
  'АБВГДЕЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЬЮЯ' +
  'абвгдежзийклмнопрстуфхцчшщъьюя',
);

const BELARUSIAN_CYRILLIC_LETTERS = toSet(
  'АБВГДЕЁЖЗІЙКЛМНОПРСТУЎФХЦЧШЬЮЯЫЭ' +
  'абвгдеёжзійклмнопрстуўфхцчшььюяыэ',
);

const KYRGYZ_CYRILLIC_LETTERS = toSet(
  'АБВГДЕЁЖЗИЙКЛМНОҢОӨПРСТУҮФХЦЧШЩЪЫЬЭЮЯ' +
  'абвгдеёжзийклмноңоөпрстуүфхцчшщъыьэюя',
);

const MACEDONIAN_CYRILLIC_LETTERS = toSet(
  'АБВГДЃЕЖЗЅИЈКЛЉМНЊОПРСТЌУФХЦЧЏШ' +
  'абвгдѓежзѕијклљмнњопрстќуфхцчџш' +
  'ЀѐЍѝ',
);

const UKRAINIAN_SPECIFIC_CYRILLIC_LETTERS = toSet('ҐґЄєІіЇї');
const SERBIAN_SPECIFIC_CYRILLIC_LETTERS = toSet('ЂђЈјЉљЊњЋћЏџ');
const BELARUSIAN_SPECIFIC_CYRILLIC_LETTERS = toSet('ЎўІі');
const KYRGYZ_SPECIFIC_CYRILLIC_LETTERS = toSet('ҢңӨөҮү');
const MACEDONIAN_SPECIFIC_CYRILLIC_LETTERS = toSet('ЃѓЅѕЌќ');

const CYRILLIC_RE = /[\u0400-\u04FF]/;

// ---------------------------------------------------------------------------------------------
// kuromoji (lazy, cached)
// ---------------------------------------------------------------------------------------------

let tokenizerPromise = null;

/** Builds the Japanese tokenizer once (dictionary load is ~30 MB, 1–2 s) and caches it. */
function getTokenizer() {
  if (!tokenizerPromise) {
    tokenizerPromise = new Promise((resolve, reject) => {
      const localDict = path.join(__dirname, 'node_modules', 'kuromoji', 'dict');
      const parentDict = path.join(__dirname, '..', 'node_modules', 'kuromoji', 'dict');
      const dicPath = fs.existsSync(localDict) ? localDict : parentDict;
      kuromoji
        .builder({ dicPath })
        .build((err, tokenizer) => (err ? reject(err) : resolve(tokenizer)));
    });
  }
  return tokenizerPromise;
}

// ---------------------------------------------------------------------------------------------
// Per-language romanizers
// ---------------------------------------------------------------------------------------------

/**
 * Strips artificial whitespace between CJK characters introduced by syllable segmentation in lyrics providers.
 * Keeps spaces around Latin / non-CJK words intact.
 */
function cleanCJKSpacing(text) {
  if (!text) return '';
  return text.replace(/([\p{Script=Hiragana}\p{Script=Katakana}\p{Script=Han}\p{Script=Hangul}])\s+(?=[\p{Script=Hiragana}\p{Script=Katakana}\p{Script=Han}\p{Script=Hangul}])/gu, '$1');
}

/** Japanese: kuromoji readings (particle は→wa, へ→e) → wanakana romaji, `ー` glued back. */
async function romanizeJapanese(text) {
  if (!text || !text.trim()) return text;
  const tokenizer = await getTokenizer();
  const clean = cleanCJKSpacing(text);
  const tokens = tokenizer.tokenize(clean);
  const merged = [];
  for (const token of tokens) {
    if (!token.surface_form || !token.surface_form.trim()) continue;
    let reading = token.reading;
    if (token.pos === '助詞') {
      if (token.surface_form === 'は') reading = 'ワ';
      else if (token.surface_form === 'へ') reading = 'エ';
    } else if (token.pronunciation && token.pronunciation !== '*') {
      reading = token.pronunciation;
    } else if (!reading || reading === '*') {
      reading = token.surface_form;
    }
    // A standalone chōonpu must ride on the previous token, otherwise it romanizes to "-".
    if (reading === 'ー' && merged.length) merged[merged.length - 1] += reading;
    else merged.push(reading);
  }
  return merged
    .map(reading => {
      let r = wanakana.toRomaji(reading).toLowerCase();
      return r.replace(/([aeiou])-/gi, '$1$1').replace(/-/g, '');
    })
    .join(' ')
    .replace(/\s+/g, ' ')
    .trim();
}

/**
 * Decomposes Korean text into romanized syllables, preserving the 1:1 mapping between
 * input characters and output Romaja slices (including final consonant assimilation).
 * Returns { fullStr, charSlices }, where `charSlices[i]` is the Romaja slice for `text[i]`.
 */
function romanizeKoreanWithSlices(text) {
  if (!text || !text.trim()) return { fullStr: text, charSlices: [] };
  const charSlices = [];
  let prevFinal = null;
  let prevHangulIdx = -1;

  for (let i = 0; i < text.length; i++) {
    charSlices.push('');
    const char = text[i];
    const code = char.charCodeAt(0);
    if (code >= 0xAC00 && code <= 0xD7A3) {
      const syllableIndex = code - 0xAC00;
      const choIndex = Math.floor(syllableIndex / (21 * 28));
      const jungIndex = Math.floor((syllableIndex % (21 * 28)) / 28);
      const jongIndex = syllableIndex % 28;

      const choChar = String.fromCharCode(0x1100 + choIndex);
      const jungChar = String.fromCharCode(0x1161 + jungIndex);
      const jongChar = jongIndex === 0 ? null : String.fromCharCode(0x11A7 + jongIndex);

      if (prevFinal != null && prevHangulIdx >= 0) {
        const contextKey = prevFinal + choChar;
        const jong = HANGUL_ROMAJA_MAP.jong[contextKey]
          ?? HANGUL_ROMAJA_MAP.jong[prevFinal]
          ?? prevFinal;
        charSlices[prevHangulIdx] += jong;
      }

      const cho = HANGUL_ROMAJA_MAP.cho[choChar] ?? choChar;
      const jung = HANGUL_ROMAJA_MAP.jung[jungChar] ?? jungChar;
      charSlices[i] += cho + jung;
      prevFinal = jongChar;
      prevHangulIdx = i;
    } else {
      if (prevFinal != null && prevHangulIdx >= 0) {
        charSlices[prevHangulIdx] += (HANGUL_ROMAJA_MAP.jong[prevFinal] ?? prevFinal);
        prevFinal = null;
        prevHangulIdx = -1;
      }
      charSlices[i] += char;
    }
  }
  if (prevFinal != null && prevHangulIdx >= 0) {
    charSlices[prevHangulIdx] += (HANGUL_ROMAJA_MAP.jong[prevFinal] ?? prevFinal);
  }

  const fullStr = charSlices.join('');
  return { fullStr, charSlices };
}

/** Korean: decompose each Hangul syllable into cho/jung/jong, resolving the final in context. */
function romanizeKorean(text) {
  if (!text || !text.trim()) return text;
  return romanizeKoreanWithSlices(text).fullStr;
}

/**
 * Chinese: romanize only the CJK runs and pass everything else through untouched.
 *
 * `pinyin-pro@3` splits non-CJK text into single letters when asked for a whole mixed string
 * (`"ni hao   w o r l d"`), so the text is split first and only the CJK runs are converted.
 */
function romanizeChinese(text) {
  if (!text || !text.trim()) return text;
  return String(text)
    .replace(/[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]+/g, run =>
      pinyin(run, { toneType: 'none', type: 'string' }).trim())
    .replace(/([，。！？；：、“”‘’（）《》〈〉…—])/g, ' $1 ')
    .replace(/\s+/g, ' ')
    .trim();
}

/**
 * Decomposes Chinese text into Pinyin slices aligned 1:1 with input characters.
 * CJK characters get their contextual Pinyin from pinyin-pro array mode.
 * Non-CJK characters (punctuation, Latin, digits) pass through untouched.
 */
function romanizeChineseWithSlices(text) {
  if (!text || !text.trim()) return { fullStr: text, charSlices: [] };
  const CJK_RE = /[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]/;
  const charSlices = new Array(text.length);

  let i = 0;
  while (i < text.length) {
    if (CJK_RE.test(text[i])) {
      const start = i;
      while (i < text.length && CJK_RE.test(text[i])) i++;
      const run = text.slice(start, i);
      const arr = pinyin(run, { toneType: 'none', type: 'array' });
      for (let k = 0; k < run.length; k++) {
        charSlices[start + k] = arr[k] || '';
      }
    } else {
      charSlices[i] = text[i];
      i++;
    }
  }

  const fullStr = romanizeChinese(text);
  return { fullStr, charSlices };
}

/** Hindi (Devanagari), including the two-character (char + nukta) sequences. */
function romanizeHindi(text) {
  const sb = [];
  let i = 0;
  while (i < text.length) {
    let consumed = false;
    if (i + 1 < text.length) {
      const twoChar = text.substring(i, i + 2);
      const mapped = DEVANAGARI_ROMAJI_MAP[twoChar];
      if (mapped != null) { sb.push(mapped); i += 2; consumed = true; }
    }
    if (!consumed) {
      const charStr = text[i];
      sb.push(DEVANAGARI_ROMAJI_MAP[charStr] ?? charStr);
      i += 1;
    }
  }
  return sb.join('');
}

/** Punjabi (Gurmukhi), including Adhak (gemination) and the two-character nukta sequences. */
function romanizePunjabi(text) {
  const sb = [];
  let i = 0;
  while (i < text.length) {
    const char = text[i];
    let consumed = false;

    // Adhak (Gemination): double the following consonant.
    if (char === '\u0A71') {
      if (i + 1 < text.length) {
        const nextMapped = GURMUKHI_ROMAJI_MAP[text[i + 1]];
        if (nextMapped != null && nextMapped.length) sb.push(nextMapped[0]);
      }
      i++;
      continue;
    }

    if (i + 1 < text.length) {
      const twoChar = text.substring(i, i + 2);
      const mapped = GURMUKHI_ROMAJI_MAP[twoChar];
      if (mapped != null) { sb.push(mapped); i += 2; consumed = true; }
    }
    if (!consumed) {
      sb.push(GURMUKHI_ROMAJI_MAP[char] ?? char);
      i++;
    }
  }
  return sb.join('');
}

/**
 * Splits a Cyrillic line into word / separator tokens the way the Kotlin source does
 * (`split("((?<=\\s|[.,!?;])|(?=\\s|[.,!?;]))")`), so a word token's first character is
 * word-initial and separators are preserved in the output.
 */
function splitCyrillicTokens(text) {
  return text
    .split(/((?<=\s|[.,!?;])|(?=\s|[.,!?;]))/)
    .filter(part => part.length > 0);
}

const CYRILLIC_PUNCT_RE = /^[.,!?;]$/;

/** Russian: general Cyrillic map + a few 3-character sequences and word-initial "е" → "ye". */
function romanizeRussianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    let charIndex = 0;
    while (charIndex < word.length) {
      let consumed = false;
      if (charIndex + 2 < word.length) {
        const threeChar = word.substring(charIndex, charIndex + 3);
        if (Object.prototype.hasOwnProperty.call(RUSSIAN_ROMAJI_MAP, threeChar)) {
          sb.push(RUSSIAN_ROMAJI_MAP[threeChar]);
          charIndex += 3;
          consumed = true;
        }
      }
      if (!consumed) {
        const charStr = word[charIndex];
        if ((charStr === 'е' || charStr === 'Е') && (charIndex === 0 || /\s/.test(word[charIndex - 1]))) {
          sb.push(charStr === 'е' ? 'ye' : 'Ye');
        } else {
          sb.push(GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
        }
        charIndex += 1;
      }
    }
  }
  return sb.join('');
}

/** Ukrainian: the Ukrainian overrides, plus Ю/Я → Iu/Ia after a consonant. */
function romanizeUkrainianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    let charIndex = 0;
    while (charIndex < word.length) {
      const charStr = word[charIndex];
      let processed = false;
      const prev = word[charIndex - 1];
      if (charIndex > 0 && isLetter(prev) && !isCyrillicVowel(prev)) {
        if (charStr === 'Ю') { sb.push('Iu'); processed = true; }
        else if (charStr === 'ю') { sb.push('iu'); processed = true; }
        else if (charStr === 'Я') { sb.push('Ia'); processed = true; }
        else if (charStr === 'я') { sb.push('ia'); processed = true; }
      }
      if (!processed) {
        sb.push(UKRAINIAN_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
      }
      charIndex++;
    }
  }
  return sb.join('');
}

/** Serbian: the Serbian overrides over the general Cyrillic map. */
function romanizeSerbianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    for (const charStr of word) {
      sb.push(SERBIAN_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
    }
  }
  return sb.join('');
}

/** Bulgarian: the Bulgarian overrides over the general Cyrillic map. */
function romanizeBulgarianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    for (const charStr of word) {
      sb.push(BULGARIAN_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
    }
  }
  return sb.join('');
}

/** Belarusian: the Belarusian overrides, with word-initial "е" → "ye". */
function romanizeBelarusianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    let charIndex = 0;
    while (charIndex < word.length) {
      const charStr = word[charIndex];
      if ((charStr === 'е' || charStr === 'Е') && (charIndex === 0 || /\s/.test(word[charIndex - 1]))) {
        sb.push(charStr === 'е' ? 'ye' : 'Ye');
      } else {
        sb.push(BELARUSIAN_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
      }
      charIndex += 1;
    }
  }
  return sb.join('');
}

/** Kyrgyz: the Kyrgyz overrides over the general Cyrillic map. */
function romanizeKyrgyzInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    for (const charStr of word) {
      sb.push(KYRGYZ_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
    }
  }
  return sb.join('');
}

/** Macedonian: the Macedonian overrides over the general Cyrillic map. */
function romanizeMacedonianInternal(text) {
  const sb = [];
  for (const word of splitCyrillicTokens(text)) {
    if (CYRILLIC_PUNCT_RE.test(word) || !word.trim()) { sb.push(word); continue; }
    for (const charStr of word) {
      sb.push(MACEDONIAN_ROMAJI_MAP[charStr] ?? GENERAL_CYRILLIC_ROMAJI_MAP[charStr] ?? charStr);
    }
  }
  return sb.join('');
}

const isLetter = char => char != null && /[^\W\d_]/u.test(char);
const isCyrillicVowel = char => char != null && 'АаЕеЄєИиІіЇїОоУуЮюЯяЫыЭэ'.includes(char);

/**
 * Cyrillic romanization. `language` pins the language; otherwise it is auto-detected. Returns
 * `null` when there is nothing to romanize (no Cyrillic, or a lone "е"/"Е" which is noise).
 */
function romanizeCyrillic(text, language = null) {
  if (!text) return null;
  const cyrillicChars = Array.from(text).filter(ch => CYRILLIC_RE.test(ch));
  if (!cyrillicChars.length || (cyrillicChars.length === 1 && (cyrillicChars[0] === 'е' || cyrillicChars[0] === 'Е'))) {
    return null;
  }
  switch (language) {
    case 'Russian': return romanizeRussianInternal(text);
    case 'Ukrainian': return romanizeUkrainianInternal(text);
    case 'Serbian': return romanizeSerbianInternal(text);
    case 'Bulgarian': return romanizeBulgarianInternal(text);
    case 'Belarusian': return romanizeBelarusianInternal(text);
    case 'Kyrgyz': return romanizeKyrgyzInternal(text);
    case 'Macedonian': return romanizeMacedonianInternal(text);
    default:
      if (isRussian(text)) return romanizeRussianInternal(text);
      if (isUkrainian(text)) return romanizeUkrainianInternal(text);
      if (isSerbian(text)) return romanizeSerbianInternal(text);
      if (isBulgarian(text)) return romanizeBulgarianInternal(text);
      if (isBelarusian(text)) return romanizeBelarusianInternal(text);
      if (isKyrgyz(text)) return romanizeKyrgyzInternal(text);
      if (isMacedonian(text)) return romanizeMacedonianInternal(text);
      return null;
  }
}

// ---------------------------------------------------------------------------------------------
// Detection
// ---------------------------------------------------------------------------------------------

const allCyrillicInSet = (text, set) =>
  Array.from(text).every(ch => set.has(ch) || !CYRILLIC_RE.test(ch));
const anyInSet = (text, set) => Array.from(text).some(ch => set.has(ch));

function isRussian(text) {
  return anyInSet(text, RUSSIAN_CYRILLIC_LETTERS) && allCyrillicInSet(text, RUSSIAN_CYRILLIC_LETTERS);
}

function isUkrainian(text) {
  return (anyInSet(text, UKRAINIAN_CYRILLIC_LETTERS) || anyInSet(text, UKRAINIAN_SPECIFIC_CYRILLIC_LETTERS))
    && Array.from(text).every(ch =>
      UKRAINIAN_CYRILLIC_LETTERS.has(ch) || UKRAINIAN_SPECIFIC_CYRILLIC_LETTERS.has(ch) || !CYRILLIC_RE.test(ch));
}

function isSerbian(text) {
  return (anyInSet(text, SERBIAN_CYRILLIC_LETTERS) || anyInSet(text, SERBIAN_SPECIFIC_CYRILLIC_LETTERS))
    && Array.from(text).every(ch =>
      SERBIAN_CYRILLIC_LETTERS.has(ch) || SERBIAN_SPECIFIC_CYRILLIC_LETTERS.has(ch) || !CYRILLIC_RE.test(ch));
}

function isBulgarian(text) {
  return anyInSet(text, BULGARIAN_CYRILLIC_LETTERS) && allCyrillicInSet(text, BULGARIAN_CYRILLIC_LETTERS);
}

function isBelarusian(text) {
  return (anyInSet(text, BELARUSIAN_CYRILLIC_LETTERS) || anyInSet(text, BELARUSIAN_SPECIFIC_CYRILLIC_LETTERS))
    && Array.from(text).every(ch =>
      BELARUSIAN_CYRILLIC_LETTERS.has(ch) || BELARUSIAN_SPECIFIC_CYRILLIC_LETTERS.has(ch) || !CYRILLIC_RE.test(ch));
}

function isKyrgyz(text) {
  return (anyInSet(text, KYRGYZ_CYRILLIC_LETTERS) || anyInSet(text, KYRGYZ_SPECIFIC_CYRILLIC_LETTERS))
    && Array.from(text).every(ch =>
      KYRGYZ_CYRILLIC_LETTERS.has(ch) || KYRGYZ_SPECIFIC_CYRILLIC_LETTERS.has(ch) || !CYRILLIC_RE.test(ch));
}

function isMacedonian(text) {
  return (anyInSet(text, MACEDONIAN_CYRILLIC_LETTERS) || anyInSet(text, MACEDONIAN_SPECIFIC_CYRILLIC_LETTERS))
    && Array.from(text).every(ch =>
      MACEDONIAN_CYRILLIC_LETTERS.has(ch) || MACEDONIAN_SPECIFIC_CYRILLIC_LETTERS.has(ch) || !CYRILLIC_RE.test(ch));
}

/**
 * Detects the Cyrillic language of a whole song (not per line) so every line is romanized with
 * the same alphabet. Mirrors the dispatch order of `romanize` in Romanization.kt.
 */
function detectCyrillicLanguage(lines) {
  const text = (Array.isArray(lines) ? lines.map(l => l.text || '') : [String(lines || '')]).join('\n');
  if (!CYRILLIC_RE.test(text)) return null;
  if (isUkrainian(text)) return 'Ukrainian';
  if (isRussian(text)) return 'Russian';
  if (isSerbian(text)) return 'Serbian';
  if (isBulgarian(text)) return 'Bulgarian';
  if (isBelarusian(text)) return 'Belarusian';
  if (isKyrgyz(text)) return 'Kyrgyz';
  if (isMacedonian(text)) return 'Macedonian';
  return null;
}

/**
 * Script census for the whole song, so a Kanji-only Japanese line in a song that has kana is
 * still routed to the Japanese romanizer instead of the Chinese one.
 * Romanization is strictly restricted to Japanese, Korean, and Chinese (CJK).
 */
function detectSongScript(lines) {
  const all = (Array.isArray(lines) ? lines.map(l => l.text || '') : [String(lines || '')]).join('\n');
  return {
    hasKana: /[\u3040-\u309f\u30a0-\u30ff]/.test(all),
    hasHangul: /[\uac00-\ud7a3\u1100-\u11ff\u3130-\u318f]/.test(all),
    hasCJK: /[\u4e00-\u9fff\u3400-\u4dbf\uf900-\ufaff]/.test(all),
  };
}

/**
 * Romanizes one line based on the song-level script context.
 * Strictly limited to Japanese (romaji), Korean (romaja), and Chinese (pinyin).
 * All other languages return null (no romanization displayed).
 */
async function romanizeLine(line, ctx) {
  const text = line.text || '';
  if (!text.trim()) return null;
  const has = re => re.test(text);
  // Japanese: kana OR (CJK and the song has kana), so Kanji-only lines join the Japanese path.
  if (has(/[\u3040-\u309f\u30a0-\u30ff]/) || (has(/[\u4e00-\u9fff\u3400-\u4dbf\uf900-\ufaff]/) && ctx.hasKana)) {
    return romanizeJapanese(text);
  }
  // Korean: Hangul
  if (has(/[\uac00-\ud7a3\u1100-\u11ff\u3130-\u318f]/)) return romanizeKorean(text);
  // Chinese: Hanzi without Japanese kana
  if (has(/[\u4e00-\u9fff\u3400-\u4dbf\uf900-\ufaff]/) && !ctx.hasKana) return romanizeChinese(text);

  // Other languages: do not romanize
  return null;
}

/**
 * Romanizes every line of a song. Only active for Japanese, Korean, and Chinese songs.
 * Returns null for any other languages.
 */
async function romanizeLyrics(lines) {
  if (!Array.isArray(lines) || !lines.length) return null;
  const ctx = detectSongScript(lines);
  // Only process if the song contains Japanese (Kana), Korean (Hangul), or Chinese (Hanzi)
  if (!ctx.hasKana && !ctx.hasHangul && !ctx.hasCJK) return null;

  const out = [];
  let any = false;
  for (const line of lines) {
    let romanized = null;
    try {
      romanized = await romanizeLine(line, ctx);
    } catch {
      romanized = null;
    }
    // A "romanization" that is identical to the source is not a romanization.
    if (romanized && romanized.trim().toLowerCase() === (line.text || '').trim().toLowerCase()) {
      romanized = null;
    }
    if (romanized) any = true;
    out.push(romanized);
  }
  return any ? out : null;
}

module.exports = {
  cleanCJKSpacing,
  romanizeLyrics,
  romanizeLine,
  romanizeJapanese,
  romanizeKorean,
  romanizeKoreanWithSlices,
  romanizeChinese,
  romanizeChineseWithSlices,
  romanizeHindi,
  romanizePunjabi,
  romanizeCyrillic,
  detectSongScript,
  detectCyrillicLanguage,
  getTokenizer,
  // Exposed for the tests; they mirror `isRussian`/`isUkrainian`/… in Romanization.kt.
  isRussian,
  isUkrainian,
  isSerbian,
  isBulgarian,
  isBelarusian,
  isKyrgyz,
  isMacedonian,
  SUPPORTED_LANGUAGES,
};
