'use strict'
// The worker that draws, for view.html, a drawing too big for SVG paths (23's: see view.html's canvasRenderer()), and
// the shading (view.html's shade()) of every drawing. canvas.js?file=F&n=N fetches F, the SVG of drawing N, reads it
// (parse()), cuts curve 0 into cells (cells()) and puts its spans in a tree of boxes (tree()). Each message from the
// page is then a view to draw: draw() draws its curves on a canvas of its own and the shading on another, and posts the
// page the drawings, ImageBitmaps; a newer view stops a drawing still under way. If the file can't be read, it posts
// the page the error.
const PAGE = 51200, MID = PAGE / 2     // the side of every drawing's square page, and its centre (venn.py's PAGE)
const G = 64                           // the cells: a G by G grid of the page
const BATCH = 64                       // ms a batch of drawing takes, about; between batches the worker looks for views
const params = new URLSearchParams(location.search)
const canvas = new OffscreenCanvas(1, 1)
// Drawn on the CPU (willReadFrequently), where the getImageData() that ends each batch costs little and has the
// batch drawn then
const ctx = canvas.getContext('2d', { willReadFrequently: true })
const shading = new OffscreenCanvas(1, 1), shade = shading.getContext('2d', { willReadFrequently: true })   // likewise
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

// A tree over runs of curve 0's spans, for outline(). Node k covers spans a to b - 1: its box, boxes[4k] to
// boxes[4k + 3] (x0, y0, x1, y1), bounds their control points, and so the spans; and its flatness, flat[k], bounds how
// far they stray from the chord between their ends (the segment from the start of span a to the end of span b - 1).
// If b - a > 1, its children, over spans a to mid - 1 and mid to b - 1 (mid = (a + b) >> 1), are nodes k + 1 and
// k + 2 (mid - a), and its flatness is theirs, the larger, plus how far their chords' common end strays from its own
// chord (every point of their chords strays no further than their ends do).
function tree(xy) {
  const nodes = 2 * (xy.length - 2) / 6 - 1, boxes = new Float64Array(4 * nodes), flat = new Float64Array(nodes)
  const off = (q, a, b) => {           // how far point q of xy strays from the segment from point a to point b
    const dx = xy[b] - xy[a], dy = xy[b + 1] - xy[a + 1], l = dx * dx + dy * dy
    const u = Math.max(0, Math.min(1, ((xy[q] - xy[a]) * dx + (xy[q + 1] - xy[a + 1]) * dy) / (l || 1)))
    return Math.hypot(xy[q] - xy[a] - u * dx, xy[q + 1] - xy[a + 1] - u * dy)
  }
  const build = (k, a, b) => {
    const mid = (a + b) >> 1, l = k + 1, r = k + 2 * (mid - a)
    if (b - a === 1) {
      const c = xy.subarray(6 * a, 6 * a + 8)
      boxes.set([Math.min(c[0], c[2], c[4], c[6]), Math.min(c[1], c[3], c[5], c[7]),
                 Math.max(c[0], c[2], c[4], c[6]), Math.max(c[1], c[3], c[5], c[7])], 4 * k)
      flat[k] = Math.max(off(6 * a + 2, 6 * a, 6 * b), off(6 * a + 4, 6 * a, 6 * b))
      return
    }
    build(l, a, mid)
    build(r, mid, b)
    for (let j = 0; j < 4; j++) boxes[4 * k + j] = (j < 2 ? Math.min : Math.max)(boxes[4 * l + j], boxes[4 * r + j])
    flat[k] = Math.max(flat[l], flat[r]) + off(6 * mid, 6 * a, 6 * b)
  }
  build(0, 0, (xy.length - 2) / 6)
  return { boxes, flat }
}

// Curve 0 as a Path2D to fill for a view whose box in curve 0's page is [x0, y0, x1, y1]: exact where it comes into the
// box, but each run of spans whose box misses the box, or that strays under tol from its chord, replaced by the chord.
// Where the run's box misses the view's, that changes which side of the curve no point of the view is on (the run
// and its chord lie in the run's box); where the run strays under tol, none further than 2 tol from the curve (the
// run and its chord lie within tol of the chord, which lies within tol of the run). So the fill needs few pieces at any
// zoom: in a 1200 by 800 window, curve 0 of 23 took WebKit 7 s to fill as the polygon of its 729,449 knots, 0.72 s as
// that of every 4th knot, 87 ms of every 16th (Chromium 52, 20 and 8 ms), and has 42,000 lines and 61 spans this
// way at fit with tol half a pixel, 8,700 and 192 zoomed in by 16. Returns the path and how many pieces it has.
function outline(xy, { boxes, flat }, [x0, y0, x1, y1], tol) {
  const p = new Path2D()
  const walk = (k, a, b) => {
    const i = 4 * k, mid = (a + b) >> 1
    if (boxes[i] > x1 || boxes[i + 2] < x0 || boxes[i + 1] > y1 || boxes[i + 3] < y0 || flat[k] < tol) p.lineTo(xy[6 * b], xy[6 * b + 1])
    else if (b - a === 1) p.bezierCurveTo(xy[6 * a + 2], xy[6 * a + 3], xy[6 * a + 4], xy[6 * a + 5], xy[6 * a + 6], xy[6 * a + 7])
    else return walk(k + 1, a, mid) + walk(k + 2 * (mid - a), mid, b)
    return 1
  }
  p.moveTo(xy[0], xy[1])
  const pieces = walk(0, 0, (xy.length - 2) / 6)
  p.closePath()
  return [p, pieces]
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
// zoom 1), w and h (the window, in CSS pixels), dpr (device pixels to a CSS pixel), k (curves 0 to k shown), inside
// (inside[i]: whether the shading is inside curve i, or outside it), colour (the shading's), seq (the job's number,
// posted back with its drawing).
let latest = 0                         // the number of the latest job: the drawing of an older one stops
let quota = 2000                       // spans in a batch: about BATCH ms' worth, at the last batch's rate
function draw({ colours, angles, width, xy, tree, cells: { paths, boxes, spans } }, { x, y, s, fit, w, h, dpr, k, inside, colour, seq }) {
  const job = ++latest
  // The lines are width / fit CSS pixels wide at any zoom, the SVG's stroke-width at fit. Wider than about 0.9 device
  // pixel, they fall off the browsers' fast path for thin lines: drawing 23 in a 2560 by 1440 window with 2 device
  // pixels to a CSS pixel took Chromium 3.9 s with lines 0.9 device pixel wide and 10 to 12.5 s with lines 0.95 to 1.35
  // wide, WebKit 5.4 s at 1, 52 s at 1.1 and 62 s at 1.35, after which it showed nothing, and Firefox 30 s at 1.35. So
  // the canvas has a pixel for each device pixel, or fewer, r to a CSS pixel, just enough to keep the lines 0.85 of its
  // own pixels wide (each then spread over more than one device pixel on the screen); then it took 1.4 to 4.1 s, and
  // the lines look a little softer.
  const r = Math.min(dpr, 0.85 * fit / width)
  // The shading has no lines, and its edges must hide under the curves' (as SVG paths, as wide as at fit), so its
  // canvas has rs pixels to a CSS pixel: as many as the curves', but at least one, unless the screen has fewer
  const rs = Math.min(dpr, Math.max(1, r))
  for (const [c, q] of [[canvas, r], [shading, rs]]) {
    c.width = Math.round(w * q)        // which also clears it and resets the context
    c.height = Math.round(h * q)
  }
  ctx.lineCap = ctx.lineJoin = 'round'
  ctx.lineWidth = width * s / fit      // in page units, under the transforms below
  // Curve i is curve 0 turned by its angle a about the centre (turns[i]: cos a, sin a): page point p goes to
  // q (turn(p) - (x, y)) / s on a canvas with q pixels to a CSS pixel, under transform(turns[i], q). The window, turned
  // back by a, and widened by half a line and two canvas pixels (antialiasing reaches one), lies in the box views[i]
  // (x0, y0, x1, y1) of curve 0's page.
  const turns = angles.map(deg => [Math.cos(deg * Math.PI / 180), Math.sin(deg * Math.PI / 180)])
  const transform = ([c, sn], q) => {
    const f = q / s
    return [f * c, f * sn, -f * sn, f * c, f * (MID - c * MID + sn * MID - x), f * (MID - sn * MID - c * MID - y)]
  }
  const pad = ctx.lineWidth / 2 + 2 * s / r
  const views = turns.map(([c, sn]) => {
    const corners = [[x, y], [x + w * s, y], [x, y + h * s], [x + w * s, y + h * s]]
      .map(([px, py]) => [MID + (px - MID) * c + (py - MID) * sn, MID - (px - MID) * sn + (py - MID) * c])
    return [Math.min(...corners.map(p => p[0])) - pad, Math.min(...corners.map(p => p[1])) - pad,
            Math.max(...corners.map(p => p[0])) + pad, Math.max(...corners.map(p => p[1])) + pad]
  })
  // The work, a step at a time, each saying how many spans (or pieces) it drew. First the shading: colour all over,
  // then kept only inside each curve checked (destination-in) and cleared inside each other (destination-out), each
  // curve's outline() for this view, exact to half a pixel of the shading's canvas
  const work = [() => {
    shade.fillStyle = colour
    shade.fillRect(0, 0, shading.width, shading.height)
    return 0
  }, ...inside.map((isIn, i) => () => {
    const [path, pieces] = outline(xy, tree, views[i], s / rs / 2)
    shade.globalCompositeOperation = isIn ? 'destination-in' : 'destination-out'
    shade.setTransform(...transform(turns[i], rs))
    shade.fill(path)
    return pieces
  })]
  // Then the curves shown: each cell of each whose box meets the window, turned back
  for (let i = 0; i <= k; i++) {
    const [x0, y0, x1, y1] = views[i], t = transform(turns[i], r)
    for (let q = 0; q < paths.length; q++) {
      if (boxes[4 * q] <= x1 && boxes[4 * q + 2] >= x0 && boxes[4 * q + 1] <= y1 && boxes[4 * q + 3] >= y0) work.push(() => {
        ctx.setTransform(...t)
        ctx.strokeStyle = colours[i]
        ctx.stroke(paths[q])
        return spans[q]
      })
    }
  }
  let next = 0
  const batch = () => {
    if (job !== latest) return         // a newer view came in meanwhile
    const t0 = performance.now()
    let done = 0
    for (; next < work.length && done < quota; next++) done += work[next]()
    for (const g of [ctx, shade]) g.getImageData(0, 0, 1, 1)   // waits for the batch to be drawn: Chromium only records
                                                                // drawing until then
    quota = Math.max(1, done * BATCH / Math.max(1, performance.now() - t0))
    if (next < work.length) return setTimeout(batch)
    const bitmaps = [canvas, shading].map(c => {
      shown.width = c.width
      shown.height = c.height
      copy.drawImage(c, 0, 0)
      copy.getImageData(0, 0, 1, 1)     // waits for the copy, here rather than on the page's thread
      return shown.transferToImageBitmap()
    })
    postMessage({ bitmap: bitmaps[0], shading: bitmaps[1], at: { x, y, s }, r, rs, colours, angles, seq }, bitmaps)
  }
  setTimeout(batch)
}

const drawing = fetch(new URL(params.get('file'), location.href))
  .then(r => r.ok ? r.arrayBuffer() : Promise.reject(new Error(r.status)))   // just the status, as view.html says it
  .then(b => parse(new Uint8Array(b), Number(params.get('n'))))
  .then(d => ({ ...d, cells: cells(d.xy), tree: tree(d.xy) }))
drawing.catch(e => postMessage({ error: e.message }))
onmessage = ({ data }) => drawing.then(d => draw(d, data))
