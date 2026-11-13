// Live Photo maker core — pure JS, no dependencies. Works in browsers and Node 18+.
//
// A Live Photo is a still image + a QuickTime movie linked by a shared "content identifier":
//   • JPEG: EXIF Apple MakerNote tag 0x0011 = UUID
//   • MOV:  moov/meta key  com.apple.quicktime.content.identifier = UUID
//           plus a timed-metadata track holding com.apple.quicktime.still-image-time
//           at the key-photo moment.
// The movie is remuxed (no re-encode): media data is copied byte-for-byte, only the
// container header (moov) is rewritten and moved to the end of the file.

const te = new TextEncoder();

// ---------- byte helpers ----------
function concat(arrs) {
  let len = 0;
  for (const a of arrs) len += a.length;
  const out = new Uint8Array(len);
  let o = 0;
  for (const a of arrs) { out.set(a, o); o += a.length; }
  return out;
}
const be16 = (n) => { const b = new Uint8Array(2); new DataView(b.buffer).setUint16(0, n); return b; };
const be32 = (n) => { const b = new Uint8Array(4); new DataView(b.buffer).setUint32(0, n >>> 0); return b; };
const zeros = (n) => new Uint8Array(n);
const cc = (s) => { const b = te.encode(s); if (b.length !== 4) throw new Error('fourcc ' + s); return b; };
const str4 = (b, o) => String.fromCharCode(b[o], b[o + 1], b[o + 2], b[o + 3]);
const dvOf = (b) => new DataView(b.buffer, b.byteOffset, b.byteLength);

function boxRaw(typeBytes, parts) {
  const payload = concat(parts);
  return concat([be32(8 + payload.length), typeBytes, payload]);
}
const box = (type, ...parts) => boxRaw(cc(type), parts);

// ---------- QuickTime box tree ----------
const CONTAINERS = new Set(['moov', 'trak', 'mdia', 'minf', 'stbl', 'edts', 'dinf']);

function parseBoxes(buf, start, end) {
  const dv = dvOf(buf);
  const out = [];
  let p = start;
  while (p + 8 <= end) {
    let size = dv.getUint32(p);
    const type = str4(buf, p + 4);
    let hdr = 8;
    if (size === 1) { size = Number(dv.getBigUint64(p + 8)); hdr = 16; }
    else if (size === 0) size = end - p;
    if (size < hdr || p + size > end) throw new Error(`Corrupt box "${type}" in movie header`);
    out.push({ type, start: p, hdr, size });
    p += size;
  }
  return out;
}

function toTree(buf, start, end) {
  return parseBoxes(buf, start, end).map((b) =>
    CONTAINERS.has(b.type)
      ? { type: b.type, children: toTree(buf, b.start + b.hdr, b.start + b.size) }
      : { type: b.type, data: buf.slice(b.start + b.hdr, b.start + b.size) });
}

function serialize(n) {
  return n.children ? box(n.type, ...n.children.map(serialize)) : (n.raw || box(n.type, n.data));
}
const child = (n, t) => n.children && n.children.find((c) => c.type === t);
const path = (n, ...ts) => ts.reduce((a, t) => a && child(a, t), n);

// ---------- top-level scan of a File/Blob ----------
async function scanTop(file) {
  const size = file.size;
  const tops = [];
  let p = 0;
  while (size - p >= 8) {
    const h = new Uint8Array(await file.slice(p, Math.min(p + 16, size)).arrayBuffer());
    const dv = dvOf(h);
    let bsize = dv.getUint32(0);
    const type = str4(h, 4);
    let hdr = 8, toEnd = false;
    if (bsize === 1) { bsize = Number(dv.getBigUint64(8)); hdr = 16; }
    else if (bsize === 0) { bsize = size - p; toEnd = true; }
    if (bsize < hdr || p + bsize > size) {
      if (tops.length && tops.some((t) => t.type === 'moov')) break; // trailing junk
      throw new Error('This file is not a valid MP4/MOV video.');
    }
    tops.push({ type, start: p, size: bsize, hdr, toEnd });
    p += bsize;
  }
  return tops;
}

// ---------- info ----------
function trackInfo(trak) {
  const hdlr = path(trak, 'mdia', 'hdlr');
  const handler = hdlr ? str4(hdlr.data, 8) : '';
  const stsd = path(trak, 'mdia', 'minf', 'stbl', 'stsd');
  const codec = stsd && stsd.data.length >= 16 ? str4(stsd.data, 12) : '';
  return { handler, codec };
}

function mvhdInfo(mvhd) {
  const d = dvOf(mvhd.data);
  const v = mvhd.data[0];
  const timescale = v === 1 ? d.getUint32(20) : d.getUint32(12);
  const duration = v === 1 ? Number(d.getBigUint64(24)) : d.getUint32(16);
  return { timescale, duration, nextTrackId: d.getUint32(mvhd.data.length - 4) };
}

export async function inspectVideo(file) {
  const tops = await scanTop(file);
  const m = tops.find((b) => b.type === 'moov');
  if (!m) throw new Error('This file has no movie header — is it an MP4 or MOV?');
  const buf = new Uint8Array(await file.slice(m.start, m.start + m.size).arrayBuffer());
  const moov = { type: 'moov', children: toTree(buf, m.hdr, m.size) };
  const mv = mvhdInfo(child(moov, 'mvhd'));
  const tracks = moov.children.filter((c) => c.type === 'trak').map(trackInfo);
  const video = tracks.find((t) => t.handler === 'vide');
  return {
    duration: mv.duration / mv.timescale,
    videoCodec: video ? video.codec : null,
    hasAudio: tracks.some((t) => t.handler === 'soun'),
    compatible: !!video && ['avc1', 'avc3', 'hvc1', 'hev1'].includes(video.codec),
  };
}

// ---------- moov/meta with content identifier ----------
const CONTENT_ID_KEY = 'com.apple.quicktime.content.identifier';
const STILL_TIME_KEY = 'com.apple.quicktime.still-image-time';

function buildMeta(existing, assetId) {
  let keys = []; // {ns:Uint8Array(4), name:Uint8Array}
  let items = []; // {index, payload}
  if (existing) {
    const d = existing.data;
    let off = -1;
    if (d.length >= 12 && str4(d, 4) === 'hdlr') off = 0;            // QuickTime style
    else if (d.length >= 16 && str4(d, 8) === 'hdlr') off = 4;       // ISO FullBox style
    if (off >= 0) {
      const kids = parseBoxes(d, off, d.length);
      const h = kids.find((k) => k.type === 'hdlr');
      if (h && str4(d, h.start + h.hdr + 8) === 'mdta') {
        const kb = kids.find((k) => k.type === 'keys');
        const ib = kids.find((k) => k.type === 'ilst');
        if (kb) {
          const dv = dvOf(d);
          const count = dv.getUint32(kb.start + kb.hdr + 4);
          let p = kb.start + kb.hdr + 8;
          for (let i = 0; i < count; i++) {
            const ks = dv.getUint32(p);
            keys.push({ ns: d.slice(p + 4, p + 8), name: d.slice(p + 8, p + ks) });
            p += ks;
          }
        }
        if (ib) {
          for (const it of parseBoxes(d, ib.start + ib.hdr, ib.start + ib.size)) {
            const idx = dvOf(d).getUint32(it.start + 4);
            items.push({ index: idx, payload: d.slice(it.start + it.hdr, it.start + it.size) });
          }
        }
      }
    }
  }
  // drop any old content identifier, re-index
  const td = new TextDecoder();
  const keep = keys.map((k, i) => ({ ...k, old: i + 1 })).filter((k) => td.decode(k.name) !== CONTENT_ID_KEY);
  const remap = new Map(keep.map((k, i) => [k.old, i + 1]));
  items = items.filter((it) => remap.has(it.index)).map((it) => ({ index: remap.get(it.index), payload: it.payload }));
  keys = keep;
  keys.push({ ns: cc('mdta'), name: te.encode(CONTENT_ID_KEY) });
  items.push({
    index: keys.length,
    payload: box('data', be32(1) /* UTF-8 */, be32(0) /* locale */, te.encode(assetId)),
  });

  const hdlr = box('hdlr', be32(0), be32(0), cc('mdta'), zeros(12), zeros(1));
  const keysBox = box('keys', be32(0), be32(keys.length),
    ...keys.map((k) => concat([be32(8 + k.name.length), k.ns, k.name])));
  const ilst = box('ilst', ...items.map((it) => boxRaw(be32(it.index), [it.payload])));
  return box('meta', hdlr, keysBox, ilst);
}

// ---------- timed metadata track (still-image-time) ----------
const MATRIX = [0x10000, 0, 0, 0, 0x10000, 0, 0, 0, 0x40000000];

function buildStillTrack({ trackId, timescale, stillUnits, sampleOffset, sampleSize }) {
  const sampleDur = Math.max(1, Math.round(timescale / 100));
  const trackDur = stillUnits + sampleDur;
  const tkhd = box('tkhd', be32(0x000001), be32(0), be32(0), be32(trackId), be32(0), be32(trackDur),
    zeros(8), be16(0), be16(0), be16(0), be16(0), ...MATRIX.map(be32), be32(0), be32(0));
  const entries = [];
  if (stillUnits > 0) entries.push(concat([be32(stillUnits), be32(0xffffffff), be32(0x10000)]));
  entries.push(concat([be32(sampleDur), be32(0), be32(0x10000)]));
  const edts = box('edts', box('elst', be32(0), be32(entries.length), ...entries));
  const mdhd = box('mdhd', be32(0), be32(0), be32(0), be32(timescale), be32(sampleDur), be16(0x55c4), be16(0));
  const hdlr = box('hdlr', be32(0), cc('mhlr'), cc('meta'), zeros(12), zeros(1));
  const keyEntry = boxRaw(be32(1), [
    box('keyd', cc('mdta'), te.encode(STILL_TIME_KEY)),
    box('dtyp', be32(0), be32(65)), // well-known type 65 = signed 8-bit int
  ]);
  const mebx = box('mebx', zeros(6), be16(1), box('keys', keyEntry));
  const stbl = box('stbl',
    box('stsd', be32(0), be32(1), mebx),
    box('stts', be32(0), be32(1), be32(1), be32(sampleDur)),
    box('stsc', be32(0), be32(1), be32(1), be32(1), be32(1)),
    box('stsz', be32(0), be32(0), be32(1), be32(sampleSize)),
    box('stco', be32(0), be32(1), be32(sampleOffset)));
  const minf = box('minf', box('nmhd', be32(0)),
    box('dinf', box('dref', be32(0), be32(1), box('url ', be32(1)))), stbl);
  return box('trak', tkhd, edts, box('mdia', mdhd, hdlr, minf));
}

// ---------- main: make Live Photo MOV ----------
/**
 * @param {Blob} file      source .mp4/.mov (H.264 or HEVC)
 * @param {{assetId:string, stillTime:number}} opts  stillTime in seconds
 * @returns {Promise<Blob>} QuickTime movie
 */
export async function makeLivePhotoMov(file, { assetId, stillTime }) {
  const tops = await scanTop(file);
  const m = tops.find((b) => b.type === 'moov');
  if (!m) throw new Error('This file has no movie header — is it an MP4 or MOV?');
  const moovBuf = new Uint8Array(await file.slice(m.start, m.start + m.size).arrayBuffer());
  const moov = { type: 'moov', children: toTree(moovBuf, m.hdr, m.size) };

  // 1. lay out the new file: ftyp | original media boxes | metadata mdat | moov
  const ftyp = box('ftyp', cc('qt  '), be32(0), cc('qt  '));
  const parts = [ftyp];
  const moved = [];
  let off = ftyp.length;
  for (const b of tops) {
    if (b.type === 'ftyp' || b.type === 'moov') continue;
    if (b.toEnd) {
      if (b.size > 0xffffffff) throw new Error('Video too large.');
      parts.push(be32(b.size), file.slice(b.start + 4, b.start + b.size));
    } else {
      parts.push(file.slice(b.start, b.start + b.size));
    }
    moved.push({ from: b.start, to: b.start + b.size, at: off });
    off += b.size;
  }
  const sample = concat([be32(9), be32(1), new Uint8Array([0xff])]); // key 1 = -1
  const metaMdat = box('mdat', sample);
  const sampleOffset = off + 8;
  parts.push(metaMdat);
  off += metaMdat.length;
  if (off > 0xffffffff) throw new Error('Video too large (over 4 GB).');

  const remap = (o) => {
    for (const r of moved) if (o >= r.from && o < r.to) return o - r.from + r.at;
    throw new Error('Unsupported layout: media data stored outside mdat.');
  };

  // 2. patch chunk offsets in every existing track
  for (const trak of moov.children.filter((c) => c.type === 'trak')) {
    const stbl = path(trak, 'mdia', 'minf', 'stbl');
    if (!stbl) continue;
    for (const t of stbl.children) {
      if (t.type !== 'stco' && t.type !== 'co64') continue;
      const dv = dvOf(t.data);
      const n = dv.getUint32(4);
      if (t.type === 'stco') {
        for (let i = 0; i < n; i++) dv.setUint32(8 + i * 4, remap(dv.getUint32(8 + i * 4)));
      } else {
        for (let i = 0; i < n; i++) dv.setBigUint64(8 + i * 8, BigInt(remap(Number(dv.getBigUint64(8 + i * 8)))));
      }
    }
  }

  // 3. new track id + still-image-time track
  const mvhd = child(moov, 'mvhd');
  const mv = mvhdInfo(mvhd);
  const trackIds = moov.children.filter((c) => c.type === 'trak')
    .map((t) => { const d = child(t, 'tkhd').data; return dvOf(d).getUint32(d[0] === 1 ? 20 : 12); });
  const trackId = Math.max(mv.nextTrackId, ...trackIds.map((i) => i + 1));
  dvOf(mvhd.data).setUint32(mvhd.data.length - 4, trackId + 1);

  const maxUnits = Math.max(0, mv.duration - 1);
  const stillUnits = Math.min(maxUnits, Math.max(0, Math.round(stillTime * mv.timescale)));
  const stillTrak = buildStillTrack({
    trackId, timescale: mv.timescale, stillUnits, sampleOffset, sampleSize: sample.length,
  });

  // 4. content identifier in moov/meta
  const metaIdx = moov.children.findIndex((c) => c.type === 'meta');
  const meta = buildMeta(metaIdx >= 0 ? moov.children[metaIdx] : null, assetId);
  if (metaIdx >= 0) moov.children.splice(metaIdx, 1);

  let lastTrak = -1;
  moov.children.forEach((c, i) => { if (c.type === 'trak') lastTrak = i; });
  moov.children.splice(lastTrak + 1, 0, { type: 'trak', raw: stillTrak }, { type: 'meta', raw: meta });

  parts.push(serialize(moov));
  return new Blob(parts, { type: 'video/quicktime' });
}

// ---------- JPEG: EXIF with Apple MakerNote content identifier ----------
function buildIFD(entries, ifdOffset) {
  entries = [...entries].sort((a, b) => a.tag - b.tag);
  const size = 2 + entries.length * 12 + 4;
  const head = new Uint8Array(size);
  const dv = dvOf(head);
  dv.setUint16(0, entries.length);
  const data = [];
  let dataOff = ifdOffset + size;
  entries.forEach((e, i) => {
    const q = 2 + i * 12;
    dv.setUint16(q, e.tag);
    dv.setUint16(q + 2, e.type);
    dv.setUint32(q + 4, e.count);
    if (e.value.length <= 4) head.set(e.value, q + 8);
    else {
      dv.setUint32(q + 8, dataOff);
      data.push(e.value);
      if (e.value.length % 2) data.push(zeros(1));
      dataOff += e.value.length + (e.value.length % 2);
    }
  });
  return concat([head, ...data]);
}
const ascii = (s) => concat([te.encode(s), zeros(1)]);

/**
 * Adds EXIF (with Apple MakerNote content identifier) to a JPEG.
 * Existing APP0/APP1 segments are replaced.
 */
export function addLivePhotoExif(jpeg, { assetId, width, height }) {
  if (jpeg[0] !== 0xff || jpeg[1] !== 0xd8) throw new Error('Not a JPEG');
  let p = 2;
  while (p + 4 <= jpeg.length && jpeg[p] === 0xff && (jpeg[p + 1] === 0xe0 || jpeg[p + 1] === 0xe1)) {
    p += 2 + ((jpeg[p + 2] << 8) | jpeg[p + 3]);
  }

  const makerIFD = buildIFD([
    { tag: 0x0001, type: 9, count: 1, value: be32(14) },
    { tag: 0x0011, type: 2, count: assetId.length + 1, value: ascii(assetId) },
  ], 14);
  const makerNote = concat([te.encode('Apple iOS'), new Uint8Array([0, 0, 1]), te.encode('MM'), makerIFD]);

  const exifEntries = [
    { tag: 0x9000, type: 7, count: 4, value: te.encode('0232') },
    { tag: 0x927c, type: 7, count: makerNote.length, value: makerNote },
    { tag: 0xa001, type: 3, count: 1, value: be16(1) },
    { tag: 0xa002, type: 4, count: 1, value: be32(width) },
    { tag: 0xa003, type: 4, count: 1, value: be32(height) },
  ];
  const ifd0 = (exifOff) => buildIFD([
    { tag: 0x010f, type: 2, count: 6, value: ascii('Apple') },
    { tag: 0x0112, type: 3, count: 1, value: be16(1) },
    { tag: 0x8769, type: 4, count: 1, value: be32(exifOff) },
  ], 8);
  const exifOff = 8 + ifd0(0).length;
  const tiff = concat([te.encode('MM'), be16(42), be32(8), ifd0(exifOff), buildIFD(exifEntries, exifOff)]);
  const payload = concat([te.encode('Exif'), zeros(2), tiff]);
  if (payload.length + 2 > 0xffff) throw new Error('EXIF too large');
  const app1 = concat([new Uint8Array([0xff, 0xe1]), be16(payload.length + 2), payload]);
  return concat([new Uint8Array([0xff, 0xd8]), app1, jpeg.subarray(p)]);
}

export function newAssetId() {
  return (globalThis.crypto && crypto.randomUUID
    ? crypto.randomUUID()
    : 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = (Math.random() * 16) | 0;
      return (c === 'x' ? r : (r & 3) | 8).toString(16);
    })).toUpperCase();
}
