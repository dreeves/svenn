'use strict'
// The worker that draws, for view.html, a drawing too big for SVG paths (23's: see view.html's canvasRenderer()).
// canvas.js?file=F&n=N fetches F, the SVG of drawing N, reads it (parse()) and cuts curve 0 into cells (cells()). Each
// message from the page is then a view to draw: draw() draws it on a canvas of its own and posts the page the drawing,
// an ImageBitmap; a newer view stops a drawing still under way. If the file can't be read, it posts the page the error.
const PAGE = 51200, MID = PAGE / 2     // the side of every drawing's square page, and its centre (venn.py's PAGE)
const G = 64                           // the cells: a G by G grid of the page
const BATCH = 64                       // ms a batch of drawing takes, about; between batches the worker looks for views
const params = new URLSearchParams(location.search)
const canvas = new OffscreenCanvas(1, 1)
// Drawn on the CPU (willReadFrequently), where the getImageData() that ends each batch costs little and has the
// batch drawn then
const ctx = canvas.getContext('2d', { willReadFrequently: true })
// Each finished drawing is copied to this canvas, drawn on the GPU, before it goes to the page: WebKit uploads a
// drawing from a CPU canvas to the GPU on the page's own thread when the page shows it, which took 145 to 364 ms a
// drawing in a 2560 by 1440 window with 2 device pixels to a CSS pixel. With the copy made here (and the canvas a
// layer of its own: view.html), the page's longest frame over three redraws there was 34 to 46 ms.
const shown = new OffscreenCanvas(1, 1), copy = shown.getContext('2d')

// The drawing's SVG, from its bytes b, which must be exactly as venn.py's write_svg() writes them: the header; curve
// 0's path data, a start and cubic spans, closed; then its n uses, each turning it about the page's centre, all with
// one stroke-width. Returns curve 0's points, xy (the start, then three a span), the uses' colours and angles, and
// the stroke-width. Anything else throws "i: got ≠ want", i the byte where they part.
function parse(b, n) {
  let i = 0
  const bytes = s => new TextEncoder().encode(s), show = bytes => JSON.stringify(new TextDecoder().decode(bytes))
  const fail = want => { throw new Error(`${i}: ${show(b.subarray(i, i + 24))} ≠ ${want}`) }
  const expect = s => {                // s: the bytes of a string
    for (let j = 0; j < s.length; j++, i++) if (b[i] !== s[j]) fail(show(s.subarray(j)))
  }
  const digits = () => {               // the digits from byte i on: their value as an integer, and how many
    const i0 = i
    let v = 0
    for (; b[i] >= 48 && b[i] <= 57; i++) v = v * 10 + b[i] - 48
    return [v, i - i0]
  }
  // A number, -?\d+(\.\d+)?, of 15 digits at most, read as its digits over a power of ten: the one rounding that
  // Number() would make, since the digits and the power are exact as doubles
  const POW10 = Array.from({ length: 16 }, (_, k) => 10 ** k), MINUS = 45, POINT = 46
  const number = () => {
    const i0 = i, sign = b[i] === MINUS ? -1 : 1
    i += b[i] === MINUS ? 1 : 0
    const [whole, w] = digits(), point = b[i] === POINT ? 1 : 0
    i += point
    const [part, p] = digits()
    if (!(w >= 1 && p >= point && w + p <= 15)) {
      i = i0
      fail('/-?\\d+(\\.\\d+)?/ (≤ 15 \\d)')
    }
    return sign * (whole * POW10[p] + part) / POW10[p]
  }
  const [COMMA, SPACE, SPAN] = [',', ' ', ' C'].map(bytes)
  const point = q => {                 // a point, x,y, into xy[q] and xy[q + 1]
    xy[q] = number()
    expect(COMMA)
    xy[q + 1] = number()
  }
  expect(bytes('<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" version="1.1" '
               + `viewBox="0 0 ${PAGE} ${PAGE}">\n<defs><path id="curve" d="M`))
  let spans = 0                        // a C each, up to the path data's closing quote
  for (let j = i; j < b.length && b[j] !== 34; j++) if (b[j] === 67) spans++
  const xy = new Float64Array(2 + 6 * spans)
  point(0)
  for (let q = 2; q < xy.length; q += 6) {
    expect(SPAN)
    point(q)
    expect(SPACE)
    point(q + 2)
    expect(SPACE)
    point(q + 4)
  }
  const z = i                          // where the path data ends
  expect(bytes(' Z"/></defs>\n'))
  if (xy[0] !== xy.at(-2) || xy[1] !== xy.at(-1)) throw new Error(`${z}: ${xy.at(-2)},${xy.at(-1)} ≠ ${xy[0]},${xy[1]}`)
  // The uses, a few hundred bytes each: use k as USE(k, width) says, width the first one's stroke-width
  const USE = (k, width) => new RegExp(`<use id="curve-${k}" href="#curve" fill="none" stroke="(#[0-9a-f]{6})" `
    + `stroke-width="(${width})" stroke-linecap="round" stroke-linejoin="round" `
    + `transform="rotate\\((-?\\d{1,15}(?:\\.\\d+)?) ${MID} ${MID}\\)"/>\\n`, 'y')
  const start = i, tail = new TextDecoder().decode(b.subarray(i))
  let width = '\\d{1,15}(?:\\.\\d+)?'
  const uses = Array.from({ length: n }, (_, k) => {
    const want = USE(k, width)
    want.lastIndex = i - start
    const m = want.exec(tail) ?? fail(want)
    i += m[0].length
    width = m[2].replace('.', '\\.')
    return m
  })
  expect(bytes('</svg>\n'))
  if (i !== b.length) fail('""')
  return { xy, colours: uses.map(m => m[1]), angles: uses.map(m => Number(m[3])), width: Number(uses[0][2]) }
}

// Curve 0 cut along the grid of cells: each span goes to the cell holding its start, and each cell's spans, in curve
// order, become a Path2D (a subpath for each run of consecutive spans), with the box bounding their control points,
// which bounds the spans themselves: paths[c], boxes[4c to 4c + 3] (x0, y0, x1, y1), spans[c] (how many).
function cells(xy) {
  const m = (xy.length - 2) / 6, of = new Int32Array(m), first = new Int32Array(G * G + 1)
  for (let s = 0; s < m; s++) {
    const x = xy[6 * s], y = xy[6 * s + 1]
    if (!(x >= 0 && x <= PAGE && y >= 0 && y <= PAGE)) throw new Error(`${x},${y} ∉ [0, ${PAGE}]²`)
    of[s] = Math.min(G - 1, Math.floor(x * G / PAGE)) * G + Math.min(G - 1, Math.floor(y * G / PAGE))
    first[of[s] + 1]++
  }
  for (let c = 0; c < G * G; c++) first[c + 1] += first[c]
  const order = new Int32Array(m), next = first.slice(0, G * G)
  for (let s = 0; s < m; s++) order[next[of[s]]++] = s   // the spans, cell by cell, in curve order within each
  const paths = [], boxes = [], spans = []
  for (let c = 0; c < G * G; c++) {
    const p = new Path2D()
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity
    for (let q = first[c]; q < first[c + 1]; q++) {
      const o = 6 * order[q]
      if (q === first[c] || order[q - 1] !== order[q] - 1) p.moveTo(xy[o], xy[o + 1])   // a run of spans starts
      p.bezierCurveTo(xy[o + 2], xy[o + 3], xy[o + 4], xy[o + 5], xy[o + 6], xy[o + 7])
      for (let j = o; j < o + 8; j += 2) {
        x0 = Math.min(x0, xy[j])
        x1 = Math.max(x1, xy[j])
        y0 = Math.min(y0, xy[j + 1])
        y1 = Math.max(y1, xy[j + 1])
      }
    }
    paths.push(p)
    boxes.push(x0, y0, x1, y1)
    spans.push(first[c + 1] - first[c])
  }
  return { paths, boxes, spans }
}

// Draw a view, job: { x, y, s } (page point (x, y) at the window's top left, s page units to a CSS pixel), fit (s at
// zoom 1), w and h (the window, in CSS pixels), dpr (device pixels to a CSS pixel), k (curves 0 to k shown).
let latest = 0                         // the number of the latest job: the drawing of an older one stops
let quota = 2000                       // spans in a batch: about BATCH ms' worth, at the last batch's rate
function draw({ colours, angles, width, cells: { paths, boxes, spans } }, { x, y, s, fit, w, h, dpr, k }) {
  const job = ++latest
  // The lines are width / fit CSS pixels wide at any zoom, the SVG's stroke-width at fit. Wider than about 0.9 device
  // pixel, they fall off the browsers' fast path for thin lines: drawing 23 in a 2560 by 1440 window with 2 device
  // pixels to a CSS pixel took Chromium 3.9 s with lines 0.9 device pixel wide and 10 to 12.5 s with lines 0.95 to 1.35
  // wide, WebKit 5.4 s at 1, 52 s at 1.1 and 62 s at 1.35, after which it showed nothing, and Firefox 30 s at 1.35. So
  // the canvas has a pixel for each device pixel, or fewer, r to a CSS pixel, just enough to keep the lines 0.85 of its
  // own pixels wide (each then spread over more than one device pixel on the screen); then it took 1.4 to 4.1 s, and
  // the lines look a little softer.
  const r = Math.min(dpr, 0.85 * fit / width)
  canvas.width = Math.round(w * r)     // which also clears it and resets the context
  canvas.height = Math.round(h * r)
  ctx.lineCap = ctx.lineJoin = 'round'
  ctx.lineWidth = width * s / fit      // in page units, under the transforms below
  // The work: each cell of each curve shown whose box meets the window turned back by that curve's angle, widened by
  // half a line and two canvas pixels (antialiasing reaches one)
  const work = [], pad = ctx.lineWidth / 2 + 2 * s / r
  for (let i = 0; i <= k; i++) {
    const a = angles[i] * Math.PI / 180, c = Math.cos(a), sn = Math.sin(a), f = r / s
    // Curve i is curve 0 turned by a about the centre: page point p goes to f (turn(p) - (x, y)) on the canvas
    const transform = [f * c, f * sn, -f * sn, f * c, f * (MID - c * MID + sn * MID - x), f * (MID - sn * MID - c * MID - y)]
    const corners = [[x, y], [x + w * s, y], [x, y + h * s], [x + w * s, y + h * s]]
      .map(([px, py]) => [MID + (px - MID) * c + (py - MID) * sn, MID - (px - MID) * sn + (py - MID) * c])
    const x0 = Math.min(...corners.map(p => p[0])) - pad, x1 = Math.max(...corners.map(p => p[0])) + pad
    const y0 = Math.min(...corners.map(p => p[1])) - pad, y1 = Math.max(...corners.map(p => p[1])) + pad
    for (let q = 0; q < paths.length; q++) {
      if (boxes[4 * q] <= x1 && boxes[4 * q + 2] >= x0 && boxes[4 * q + 1] <= y1 && boxes[4 * q + 3] >= y0) work.push([transform, colours[i], q])
    }
  }
  let next = 0
  const batch = () => {
    if (job !== latest) return         // a newer view came in meanwhile
    const t0 = performance.now()
    let done = 0
    for (; next < work.length && done < quota; next++) {
      const [transform, colour, q] = work[next]
      ctx.setTransform(...transform)
      ctx.strokeStyle = colour
      ctx.stroke(paths[q])
      done += spans[q]
    }
    ctx.getImageData(0, 0, 1, 1)       // waits for the batch to be drawn: Chromium only records strokes until then
    quota = Math.max(1, done * BATCH / Math.max(1, performance.now() - t0))
    if (next < work.length) return setTimeout(batch)
    shown.width = canvas.width
    shown.height = canvas.height
    copy.drawImage(canvas, 0, 0)
    copy.getImageData(0, 0, 1, 1)       // waits for the copy, here rather than on the page's thread
    const bitmap = shown.transferToImageBitmap()
    postMessage({ bitmap, at: { x, y, s }, r, colours }, [bitmap])
  }
  setTimeout(batch)
}

const drawing = fetch(new URL(params.get('file'), location.href))
  .then(r => r.ok ? r.arrayBuffer() : Promise.reject(new Error(r.status)))   // just the status, as view.html says it
  .then(b => parse(new Uint8Array(b), Number(params.get('n'))))
  .then(({ xy, ...d }) => ({ ...d, cells: cells(xy) }))
drawing.catch(e => postMessage({ error: e.message }))
onmessage = ({ data }) => drawing.then(d => draw(d, data))
