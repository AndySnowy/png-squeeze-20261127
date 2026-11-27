// PNG squeezer: decode a stored RGBA screenshot, reduce its colour type,
// pick per-row filters, and write it back with a hand-rolled lazy-match
// DEFLATE (hash chains + length-limited Huffman via package-merge).
// Node stdlib only, no clock, no randomness, fixed work budget: deterministic.
import { inflateSync, deflateSync } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const W = 1280;
const H = 720;

// ---------------------------------------------------------------- PNG basics

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function adler32(bytes) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) {
      a += bytes[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

const SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function pngOf(chunks) {
  let size = SIG.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIG, 0);
  let at = SIG.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

// Decode any 8-bit non-interlaced PNG of colour type 0/2/3/4/6 to RGBA.
function decodePng(bytes) {
  if (bytes.length < 8 || SIG.some((b, i) => bytes[i] !== b)) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error('bad CRC on ' + type);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') ended = true;
    else throw new Error('unexpected chunk ' + type);
  }
  const { width, height, colourType } = header;
  const bpp = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 }[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('bad inflate length');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { rgba, width, height };
}

// ---------------------------------------------------------------- analysis

// What the image holds: opacity, greyness, and its colours when at most 256.
function analyse(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const key = rgba[d] * 16777216 + rgba[d + 1] * 65536 + rgba[d + 2] * 256 + rgba[d + 3];
      const k = counts.get(key);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(key, 1);
      } else counts.set(key, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [];
    for (const [key, count] of counts) {
      colours.push({
        r: Math.floor(key / 16777216),
        g: Math.floor(key / 65536) % 256,
        b: Math.floor(key / 256) % 256,
        a: key % 256,
        word: key,
        count,
      });
    }
  }
  return { opaque, grey, colours };
}

// The one fully transparent value the image may key by tRNS instead of an
// alpha channel: every pixel opaque or that exact value at alpha 0, and no
// opaque pixel of the same value. Null when there is none.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

// The image's samples in colour type ct (0, 2, 4 or 6) from its RGBA.
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

// A palette's entries in the order a trial writes them: transparent ones
// first (by alpha), then by order ('count' or 'luminance').
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
  const entries = [...colours].sort((x, y) => {
    const ta = x.a === 255 ? 1 : 0;
    const tb = y.a === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r;
    plte[i * 3 + 1] = c.g;
    plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    indices[i] = index.get(rgba[d] * 16777216 + rgba[d + 1] * 65536 + rgba[d + 2] * 256 + rgba[d + 3]);
  }
  return { plte, trns, indices };
}

// The forms an image can be written in: each {colourType, bpp, samples, plte, trns, filters}.
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', [0, 'minsum']],
      ['luminance', [0, 'minsum', 'brute']],
    ]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [0, 1, 2, 4, 'minsum', 'pairs', 'brute'] });
  return forms;
}

// ---------------------------------------------------------------- filters

function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

// Filter every row of `samples` by `choice` (a fixed type, 'minsum',
// 'pairs', or 'brute': each row's trials compressed by zlib level 4 after
// the 32 KiB written before it, the smallest kept). Returns the raw data.
function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = [];
  for (let t = 0; t < 5; t++) {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    trial.push(row);
  }
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - 32768), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: 4, memLevel: 9 } : { level: 4, memLevel: 9, dictionary: before }).length;
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// Screen every form and filter choice by zlib level 6; the smallest wins.
function screen(rgba, width, height) {
  let best = null;
  for (const form of formsOf(rgba)) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, { level: 6, memLevel: 8 });
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) best = { form, data, bytes };
    }
  }
  return best;
}

// ---------------------------------------------------------------- DEFLATE

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

function lenCode(len) {
  let i = 28;
  while (i > 0 && LEN_BASE[i] > len) i--;
  return i;
}

function distCode(dist) {
  let i = 29;
  while (i > 0 && DIST_BASE[i] > dist) i--;
  return i;
}

// Package-merge (Larmore & Hirschberg): the length-limited Huffman code.
// A symbol's length is its occurrence count in the last list's smallest
// n-1 packages, counted with multiplicity.
function codeLengths(freqs, limit) {
  const n = freqs.length;
  const first = [];
  for (let i = 0; i < n; i++) if (freqs[i] > 0) first.push([i, freqs[i]]);
  if (first.length === 0) return new Uint8Array(n);
  if (first.length === 1) {
    const lengths = new Uint8Array(n);
    lengths[first[0][0]] = 1;
    return lengths;
  }
  let list = first.map(([s, f]) => ({ items: [[s, f]], f }));
  const lists = [list];
  for (let depth = 1; depth < limit; depth++) {
    list = list.map((p) => ({ items: p.items, f: p.f }));
    list.sort((a, b) => a.f - b.f);
    const next = [];
    for (let i = 0; i + 1 < list.length; i += 2) {
      next.push({ items: list[i].items.concat(list[i + 1].items), f: list[i].f + list[i + 1].f });
    }
    if (next.length === 0) break;
    list = list.concat(next);
    lists.push(list);
  }
  const last = lists[lists.length - 1];
  const take = last.slice().sort((a, b) => a.f - b.f).slice(0, first.length - 1);
  const lengths = new Uint8Array(n);
  for (const p of take) {
    for (const [s] of p.items) lengths[s]++;
  }
  return lengths;
}

function reverseBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) {
    r = (r << 1) | ((code >>> i) & 1);
  }
  return r;
}

function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Uint16Array(n);
  const counts = new Uint16Array(16);
  for (let i = 0; i < n; i++) counts[lengths[i]]++;
  counts[0] = 0;
  let next = 0;
  for (let len = 1; len < 16; len++) {
    const code = (next + counts[len - 1]) << 1;
    next = code;
    let c = code;
    for (let i = 0; i < n; i++) {
      if (lengths[i] === len) {
        codes[i] = reverseBits(c, len);
        c++;
      }
    }
  }
  return codes;
}

// Huffman lengths for the run-length encoding of the litlen+dist code
// lengths, ordered by the DEFLATE code-length permutation.
const CL_PERM = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
const CL_EXTRA = { 16: 2, 17: 3, 18: 7 };

function rleLengths(lengths) {
  const tokens = [];
  let i = 0;
  while (i < lengths.length) {
    const v = lengths[i];
    let j = i;
    while (j < lengths.length && lengths[j] === v) j++;
    let run = j - i;
    i = j;
    if (v === 0) {
      while (run >= 11) {
        const take = Math.min(run, 138);
        tokens.push([18, take - 11]);
        run -= take;
      }
      while (run >= 3) {
        const take = Math.min(run, 10);
        tokens.push([17, take - 3]);
        run -= take;
      }
      for (let k = 0; k < run; k++) tokens.push([0, 0]);
    } else {
      tokens.push([v, 0]);
      run--;
      while (run >= 3) {
        const take = Math.min(run, 6);
        tokens.push([16, take - 3]);
        run -= take;
      }
      for (let k = 0; k < run; k++) tokens.push([v, 0]);
    }
  }
  return tokens;
}

class BitWriter {
  constructor() {
    this.bytes = [];
    this.acc = 0;
    this.nbits = 0;
  }

  write(code, len) {
    this.acc |= code << this.nbits;
    this.nbits += len;
    while (this.nbits >= 8) {
      this.bytes.push(this.acc & 0xff);
      this.acc >>>= 8;
      this.nbits -= 8;
    }
  }

  finish() {
    if (this.nbits > 0) this.bytes.push(this.acc & 0xff);
    return Uint8Array.from(this.bytes);
  }
}

// ---------------------------------------------------------------- LZ77 + blocks

const MIN_MATCH = 3;
const MAX_MATCH = 258;
const HASH_BITS = 15;
const HASH_SIZE = 1 << HASH_BITS;
const MAX_DIST = 32768;
const BLOCK_INPUT = 131072;

function hashOf(data, pos) {
  return ((data[pos] << 16) ^ (data[pos + 1] << 8) ^ data[pos + 2]) * 2654435761 >>> (32 - HASH_BITS);
}

const FIXED_LITLEN_LEN = new Uint8Array(288).fill(8, 0, 144).fill(9, 144, 256).fill(7, 256, 280).fill(8, 280);
const FIXED_DIST_LEN = new Uint8Array(30).fill(5);

// Lazy-match parse: at each position the best match found; when a match of
// length 1 starts, the next position's match is tried too and kept if longer.
function parseBlock(data, start, end, chain, prev, head) {
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(30);
  const tokens = [];
  let pos = start;
  let len1 = 0;
  let dist1 = 0;
  while (pos < end) {
    const maxLen = Math.min(MAX_MATCH, end - pos);
    let bestLen = 0;
    let bestDist = 0;
    if (maxLen >= MIN_MATCH) {
      const h = hashOf(data, pos);
      let dist = pos - head[h];
      let cand = head[h];
      let tries = 0;
      while (cand >= 0 && dist <= MAX_DIST && tries < chain) {
        tries++;
        let len = 0;
        while (len < maxLen && data[cand + len] === data[pos + len]) len++;
        if (len >= MIN_MATCH && (len > bestLen || (len === bestLen && cand + len < pos))) {
          bestLen = len;
          bestDist = dist;
          if (len === maxLen) break;
        }
        cand = prev[cand];
        dist = pos - cand;
      }
      head[h] = pos;
      prev[pos] = cand;
      if (bestLen === 0) {
        for (let i = pos + 1; i < Math.min(pos + MIN_MATCH, end); i++) {
          if (i + MIN_MATCH <= end) {
            const hh = hashOf(data, i);
            if (i - head[hh] > MAX_DIST || head[hh] < 0) prev[i] = -1;
            else prev[i] = head[hh];
            head[hh] = i;
          }
        }
      } else if (bestLen > 1) {
        for (let i = pos + 1; i < pos + bestLen; i++) {
          if (i + MIN_MATCH <= end) {
            const hh = hashOf(data, i);
            if (i - head[hh] > MAX_DIST || head[hh] < 0) prev[i] = -1;
            else prev[i] = head[hh];
            head[hh] = i;
          }
        }
      }
    }
    if (bestLen >= MIN_MATCH) {
      if (len1 !== 0) {
        tokens.push(len1);
        tokens.push(dist1);
        litFreq[257 + lenCode(len1)]++;
        distFreq[distCode(dist1)]++;
        len1 = 0;
      }
      if (pos + 1 < end && bestLen > 1) {
        const m2 = Math.min(MAX_MATCH, end - pos - 1);
        let l2 = 0;
        let d2 = 0;
        if (m2 >= MIN_MATCH) {
          const h = hashOf(data, pos + 1);
          let dist = pos + 1 - head[h];
          let cand = head[h];
          let tries = 0;
          while (cand >= 0 && dist <= MAX_DIST && tries < chain) {
            tries++;
            let len = 0;
            while (len < m2 && data[cand + len] === data[pos + 1 + len]) len++;
            if (len >= MIN_MATCH && len > l2) {
              l2 = len;
              d2 = dist;
              if (len === m2) break;
            }
            cand = prev[cand];
            dist = pos + 1 - cand;
          }
        }
        if (l2 > bestLen) {
          const b = data[pos];
          tokens.push(b);
          litFreq[b]++;
          pos++;
          len1 = l2;
          dist1 = d2;
          continue;
        }
      }
      tokens.push(bestLen);
      tokens.push(bestDist);
      litFreq[257 + lenCode(bestLen)]++;
      distFreq[distCode(bestDist)]++;
      pos += bestLen;
      continue;
    }
    if (len1 !== 0) {
      tokens.push(len1);
      tokens.push(dist1);
      litFreq[257 + lenCode(len1)]++;
      distFreq[distCode(dist1)]++;
      len1 = 0;
    }
    tokens.push(data[pos]);
    litFreq[data[pos]]++;
    pos++;
  }
  if (len1 !== 0) {
    tokens.push(len1);
    tokens.push(dist1);
    litFreq[257 + lenCode(len1)]++;
    distFreq[distCode(dist1)]++;
  }
  litFreq[256]++;
  return { tokens, litFreq, distFreq };
}

// Write one dynamic-Huffman block (or fixed, or stored when that is
// smaller). The caller owns BFINAL.
function writeBlock(w, tokens, litFreq, distFreq, last) {
  const litLen = codeLengths(litFreq, 15);
  const distLen = codeLengths(distFreq, 15);
  let hlit = 286;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const both = new Uint8Array(hlit + hdist);
  both.set(litLen.subarray(0, hlit));
  both.set(distLen.subarray(0, hdist), hlit);
  const tokens2 = rleLengths(both);
  const clFreq = new Uint32Array(19);
  for (const [sym] of tokens2) clFreq[sym]++;
  const clLen = codeLengths(clFreq, 7);
  let hclen = 19;
  while (hclen > 4 && clLen[CL_PERM[hclen - 1]] === 0) hclen--;
  const clCode = canonicalCodes(clLen);
  const litCode = canonicalCodes(litLen);
  const distCodeMap = canonicalCodes(distLen);
  const wDyn = new BitWriter();
  wDyn.write(last ? 1 : 0, 1);
  wDyn.write(2, 2);
  wDyn.write(hlit - 257, 5);
  wDyn.write(hdist - 1, 5);
  wDyn.write(hclen - 4, 4);
  for (let i = 0; i < hclen; i++) wDyn.write(clLen[CL_PERM[i]], 3);
  for (const [sym, extra] of tokens2) {
    wDyn.write(clCode[sym], clLen[sym]);
    if (sym === 16 || sym === 17 || sym === 18) wDyn.write(extra, CL_EXTRA[sym]);
  }
  for (let i = 0; i < tokens.length; i += 2) {
    const a = tokens[i];
    const b = tokens[i + 1];
    if (a < 257) wDyn.write(litCode[a], litLen[a]);
    else {
      const lc = a - 257;
      wDyn.write(litCode[257 + lc], litLen[257 + lc]);
      if (LEN_EXTRA[lc] > 0) wDyn.write(a - LEN_BASE[lc], LEN_EXTRA[lc]);
      const dc = distCode(b);
      wDyn.write(distCodeMap[dc], distLen[dc]);
      if (DIST_EXTRA[dc] > 0) wDyn.write(b - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  wDyn.write(litCode[256], litLen[256]);
  const wFixed = new BitWriter();
  wFixed.write(last ? 1 : 0, 1);
  wFixed.write(1, 2);
  const fl = canonicalCodes(FIXED_LITLEN_LEN);
  const fd = canonicalCodes(FIXED_DIST_LEN);
  for (let i = 0; i < tokens.length; i += 2) {
    const a = tokens[i];
    const b = tokens[i + 1];
    if (a < 257) wFixed.write(fl[a], FIXED_LITLEN_LEN[a]);
    else {
      const lc = a - 257;
      wFixed.write(fl[257 + lc], FIXED_LITLEN_LEN[257 + lc]);
      if (LEN_EXTRA[lc] > 0) wFixed.write(a - LEN_BASE[lc], LEN_EXTRA[lc]);
      const dc = distCode(b);
      wFixed.write(fd[dc], FIXED_DIST_LEN[dc]);
      if (DIST_EXTRA[dc] > 0) wFixed.write(b - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  wFixed.write(fl[256], FIXED_LITLEN_LEN[256]);
  const dynBytes = wDyn.finish();
  const fixedBytes = wFixed.finish();
  const dynOk = clFreq.every((f, s) => f === 0 || clLen[s] > 0) && litLen[256] > 0;
  if (dynOk && dynBytes.length <= fixedBytes.length) {
    w.bytes.push(...dynBytes);
    w.acc = 0;
    w.nbits = 0;
  } else {
    w.bytes.push(...fixedBytes);
    w.acc = 0;
    w.nbits = 0;
  }
}

// The custom deflate: lazy-parse each block, write it, then the final bit.
function deflateCustom(data, maxChain) {
  const w = new BitWriter();
  const prev = new Int32Array(data.length).fill(-1);
  const head = new Int32Array(HASH_SIZE).fill(-1);
  for (let start = 0; start < data.length; start += BLOCK_INPUT) {
    const end = Math.min(data.length, start + BLOCK_INPUT);
    const { tokens, litFreq, distFreq } = parseBlock(data, start, end, maxChain, prev, head);
    writeBlock(w, tokens, litFreq, distFreq, end === data.length);
  }
  return w.finish();
}

function zlibWrap(deflated, data) {
  const out = new Uint8Array(2 + deflated.length + 4);
  out[0] = 0x78;
  out[1] = 0xda;
  out.set(deflated, 2);
  const view = new DataView(out.buffer);
  view.setUint32(2 + deflated.length, adler32(data));
  return out;
}

// ---------------------------------------------------------------- entry point

// Encode one image: screen forms and filters by zlib level 6, then write
// the best with the custom deflate, keeping the smallest of that and three
// zlib level 9 trials.
function encodePng(rgba, width, height) {
  const best = screen(rgba, width, height);
  const data = best.data;
  const maxChain = data.length > 3000000 ? 1024 : 4096;
  let zlib = zlibWrap(deflateCustom(data, maxChain), data);
  for (const options of [{ level: 9, memLevel: 8 }, { level: 9, memLevel: 9 }, { level: 9, memLevel: 8, strategy: 1 }]) {
    const alt = deflateSync(data, options);
    if (alt.length < zlib.length) zlib = alt;
  }
  const form = best.form;
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', zlib]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

function main() {
  const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
  const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  mkdirSync(outputDir, { recursive: true });
  for (const id of readdirSync(inputDir).sort()) {
    const { rgba, width, height } = decodePng(new Uint8Array(readFileSync(join(inputDir, id, 'image.png'))));
    const png = encodePng(rgba, width, height);
    const dir = join(outputDir, id);
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'image.png'), png);
  }
}

main();
