// Browser quals for view.html, the viewer. quals.py runs this and reads its output: it serves the repo over HTTP,
// opens the viewer in Chromium, WebKit and Firefox with Playwright, and prints {check: [problem, ...]} as JSON, each
// problem one line naming the browser and what went wrong. quals.py holds each check's replicata and expectata.
//
// Usage: node tools/browser_quals.mjs N ... canvas N ...   (every n whose drawing the viewer shows as SVG paths, then
// every n it draws on a canvas; quals.py passes them)
import assert from 'node:assert/strict'
import http from 'node:http'
import path from 'node:path'
import zlib from 'node:zlib'
import { readFile } from 'node:fs/promises'
import { fileURLToPath } from 'node:url'
import { chromium, firefox, webkit } from 'playwright'

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const ARGS = process.argv.slice(2), CUT = ARGS.indexOf('canvas')
assert(CUT >= 0, `no "canvas" among the arguments: ${ARGS}`)
const PATHS = ARGS.slice(0, CUT).map(Number)    // the n whose drawings the viewer shows as SVG paths
const CANVAS = ARGS.slice(CUT + 1).map(Number)  // and those it draws on a canvas
const SMALL = 7                       // the n most checks use: quick to load, with curves enough to tell apart
const W = 1200, H = 800               // the window
const TYPES = { '.html': 'text/html', '.css': 'text/css', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
                '.ico': 'image/x-icon', '.webmanifest': 'application/manifest+json', '.js': 'text/javascript' }
assert(PATHS.includes(SMALL), `n = ${SMALL} is not among the n given: ${PATHS}`)
const nn = n => String(n).padStart(2, '0')   // as in the drawings' file names

// A static file server for the repo, answering 404 for what is not there, as GitHub Pages does. It sends no cache
// headers, so every fetch reaches it; served lists the path of every request, in order.
const served = []
const server = http.createServer(async (req, res) => {
  const at = new URL(req.url, 'http://localhost').pathname
  served.push(at)
  const file = path.join(ROOT, at)
  const body = await readFile(file).catch(() => null)
  res.writeHead(body ? 200 : 404, body ? { 'content-type': TYPES[path.extname(file)] } : {})
  res.end(body ?? '')
})
await new Promise(ok => server.listen(0, '127.0.0.1', ok))
const BASE = `http://127.0.0.1:${server.address().port}`

// The square page and the stroke-width of drawing n, from its SVG file
async function drawing(n) {
  const text = await readFile(path.join(ROOT, 'img', `venn-${nn(n)}.svg`), 'utf8')
  return { page: Number(text.match(/viewBox="0 0 ([\d.]+) [\d.]+"/)[1]),
           stroke: Number(text.match(/stroke-width="([\d.]+)"/)[1]) }
}

const frames = page => page.evaluate(() => new Promise(ok => requestAnimationFrame(() => requestAnimationFrame(ok))))
const ctm = page => page.evaluate(() => {
  const m = document.querySelector('#stage svg').getScreenCTM()
  return { a: m.a, d: m.d, e: m.e, f: m.f }
})
const under = (m, [x, y]) => [(x - m.e) / m.a, (y - m.f) / m.d]   // the page point drawn at screen point (x, y)
const at = (m, [x, y]) => [m.a * x + m.e, m.d * y + m.f]          // the screen point where page point (x, y) is drawn
const far = (p, q) => Math.hypot(p[0] - q[0], p[1] - q[1])
const fmt = p => `(${p.map(v => v.toFixed(2)).join(', ')})`
// Each curve's line on screen: how it scales, and how wide it is
const strokes = page => page.evaluate(() => [...document.querySelectorAll('#stage path')].map(p => {
  const s = getComputedStyle(p)
  return [s.vectorEffect, parseFloat(s.strokeWidth)]
}))
// Where the page goes at zoom 1: the square that fits below the top controls and clear of the swatches (a row along
// the bottom, or in a landscape window a column along the right edge), centred there, but never less than half the
// window's shorter side, and then never past the window's left edge; side is that square's side in pixels, (x, y) its
// centre
const area = page => page.evaluate(() => {
  const t = document.getElementById('top').getBoundingClientRect().bottom
  const c = document.getElementById('curves'), r = c.getBoundingClientRect()
  const column = getComputedStyle(c).writingMode !== 'horizontal-tb'
  const right = column ? r.left : innerWidth, bottom = column ? innerHeight : r.top
  const side = Math.max(Math.min(right, bottom - t), Math.min(innerWidth, innerHeight) / 2)
  return { x: Math.max(right, side) / 2, y: (t + bottom) / 2, side }
})
// Dispatch synthetic pointer events at the stage, as a mouse, pen or finger would send them
const pointers = (page, events) => page.evaluate(events => {
  const stage = document.getElementById('stage')
  for (const [type, init] of events) stage.dispatchEvent(new PointerEvent(type, { bubbles: true, ...init }))
}, events)
const ready = (page, n) => page.waitForFunction(
  n => document.querySelectorAll('#curves button:enabled').length === n && document.querySelectorAll('#stage path').length === n, n,
  { timeout: 60000 })   // loading 19 (4 MB, 19 paths of 55,000 spans) can take a busy machine over 10 s

// Open the viewer for n and wait until it is ready. Not for the page's load event, which no check needs (it waits for
// the stand-in PNG too) and which once took WebKit more than 10 s on a busy machine: ready() allows 60.
async function open(page, n) {
  await page.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
  await ready(page, n)
}

// Expect the screen point s to still show page point p (to half a pixel), and the scale to be want
function holds(problem, m, s, p, want, what) {
  if (far(at(m, p), s) > 0.5) problem(`${what}: page point ${fmt(p)} moved from ${fmt(s)} to ${fmt(at(m, p))}`)
  if (Math.abs(m.a / want - 1) > 1e-3 || Math.abs(m.d / want - 1) > 1e-3) problem(`${what}: scale ${m.a}, ${m.d}, not ${want}`)
}

// ---- The canvas. The viewer draws each n in CANVAS on a canvas, by a worker, not as SVG paths. Its checks see it
// through spy() and compare(), and compute each view they expect themselves, as a mapping {x, y, s}: page point (x, y)
// at the window's top left, s page units to a CSS pixel.

// Installed in the page before the viewer's own script (page.addInitScript). window.__seen records the times (the
// page's clock, in ms) when the page asks a worker for anything (asked: postMessage), shows a new drawing on a canvas
// (shown: transferFromImageBitmap), and draws on or resizes a canvas in the document itself (drawn); and when each
// animation frame begins (frames).
function spy() {
  const seen = window.__seen = { asked: [], shown: [], drawn: [], frames: [] }
  const log = (list, proto, k, counts = () => true) => {
    const f = proto[k]
    proto[k] = function (...args) {
      if (counts(this)) list.push(performance.now())
      return f.apply(this, args)
    }
  }
  log(seen.asked, Worker.prototype, 'postMessage')
  log(seen.shown, ImageBitmapRenderingContext.prototype, 'transferFromImageBitmap')
  for (const k of ['stroke', 'fill', 'drawImage', 'putImageData', 'clearRect', 'fillRect', 'strokeRect', 'fillText', 'strokeText'])
    log(seen.drawn, CanvasRenderingContext2D.prototype, k, ctx => ctx.canvas.isConnected)
  for (const k of ['width', 'height']) {   // setting either clears a canvas
    const d = Object.getOwnPropertyDescriptor(HTMLCanvasElement.prototype, k)
    Object.defineProperty(HTMLCanvasElement.prototype, k, { ...d, set(v) {
      if (this.isConnected) seen.drawn.push(performance.now())
      d.set.call(this, v)
    } })
  }
  const frame = t => {
    seen.frames.push(t)
    requestAnimationFrame(frame)
  }
  requestAnimationFrame(frame)
}

// Installed in the page before the viewer's own script, like spy(): each message from a worker reaches the page's
// listener as usual, or, while window.__held is an array, waits in it, as a function that delivers it
function holdable() {
  const listen = Worker.prototype.addEventListener
  Worker.prototype.addEventListener = function (type, f, options) {
    const held = e => window.__held ? window.__held.push(() => f.call(this, e)) : f.call(this, e)
    return listen.call(this, type, type === 'message' ? held : f, options)
  }
}

// In the page: the viewer's canvas against its reference, curves 0 to k of the drawing's file as this draws them
// itself: curve 0's path data handed to Path2D (once a page), stroked once a curve, turned as its use says, in its
// colour, under mapping m, with lines px CSS pixels wide, at r canvas pixels to a CSS pixel, on a canvas the size of
// the viewer's. mismatch: the summed difference of their colours, each weighted by its alpha, the canvas's alpha first
// scaled by 1 / ink (so that antialiasing that covers a few percent more or less differs only in ink), over the
// reference's own sum: 0 for the same picture, about 2 for pictures with nothing in common. ink: the canvas's total
// alpha over the reference's. Also the canvas's size in pixels and its box in the window.
async function compare([file, m, k, px, r]) {
  window.__file ??= fetch(file).then(r => r.text()).then(text => ({
    path: new Path2D(text.match(/<path id="curve" d="([^"]*)"/)[1]),
    uses: [...text.matchAll(/<use [^>]*? stroke="([^"]*)" [^>]*? transform="rotate\(([^ ]+) ([^ ]+) ([^ ]+)\)"\/>/g)]
      .map(([, stroke, deg, cx, cy]) => ({ stroke, deg: Number(deg), cx: Number(cx), cy: Number(cy) })),
  }))
  const f = await window.__file, view = document.querySelector('#stage canvas'), box = view.getBoundingClientRect()
  const w = view.width, h = view.height
  const pixels = draw => {
    const c = document.createElement('canvas')   // not in the document, so not counted by spy()
    c.width = w
    c.height = h
    const g = c.getContext('2d', { willReadFrequently: true })
    draw(g)
    return g.getImageData(0, 0, w, h).data
  }
  const V = pixels(g => g.drawImage(view, 0, 0))
  const R = pixels(g => {
    g.lineCap = g.lineJoin = 'round'
    g.lineWidth = px * m.s
    for (const u of f.uses.slice(0, k + 1)) {
      g.setTransform(new DOMMatrix([r / m.s, 0, 0, r / m.s, -m.x * r / m.s, -m.y * r / m.s])
        .translate(u.cx, u.cy).rotate(u.deg).translate(-u.cx, -u.cy))
      g.strokeStyle = u.stroke
      g.stroke(f.path)
    }
  })
  let va = 0, ra = 0
  for (let i = 3; i < V.length; i += 4) { va += V[i]; ra += R[i] }
  const scale = va ? ra / va : 1
  let diff = 0, sum = 0
  for (let i = 0; i < V.length; i += 4) {
    const av = V[i + 3] * scale, ar = R[i + 3]
    diff += Math.abs(V[i] * av - R[i] * ar) + Math.abs(V[i + 1] * av - R[i + 1] * ar) +
            Math.abs(V[i + 2] * av - R[i + 2] * ar) + 255 * Math.abs(av - ar)
    sum += (R[i] + R[i + 1] + R[i + 2] + 255) * ar
  }
  return { mismatch: diff / sum, ink: va / ra, size: [w, h], box: [box.left, box.top, box.width, box.height],
           window: [innerWidth, innerHeight] }
}

// The mapping at fit: the page's centre at the centre of area() a, its side (in page units) across a.side pixels
const fitted = (a, side) => ({ s: side / a.side, x: side / 2 - a.x * side / a.side, y: side / 2 - a.y * side / a.side })
// Mapping m zoomed by f about window point (x, y), which goes on showing the same page point; held to 1/2 to 1000
// times the fit
function zoomed(m, fit, [x, y], f) {
  const s = fit.s / Math.min(Math.max(fit.s / m.s * f, 1 / 2), 1000)
  return { s, x: m.x + x * (m.s - s), y: m.y + y * (m.s - s) }
}

// Expect the canvas to match its reference: curves 0 to k of drawing n under mapping m, with lines as wide on screen as
// at fit, at the canvas's resolution: a pixel for each device pixel, or fewer, as many as make the lines 0.85 of the
// canvas's pixels wide (see qual_viewer_canvas_big)
async function matches(page, n, m, k, what, problem) {
  const { page: side, stroke } = await drawing(n), a = await area(page)
  const px = stroke * a.side / side, dpr = await page.evaluate(() => devicePixelRatio), r = Math.min(dpr, 0.85 / px)
  const got = await page.evaluate(compare, [`img/venn-${nn(n)}.svg`, m, k, px, r])
  const [w, h] = got.window, want = [Math.round(w * r), Math.round(h * r)]
  if (String(got.size) !== String(want)) problem(`${what}: the canvas has ${got.size} pixels, not ${want} (${r} to a CSS pixel)`)
  if (got.box.some((v, i) => Math.abs(v - [0, 0, w, h][i]) > 1)) problem(`${what}: the canvas covers ${got.box}, not the window, ${w} by ${h}`)
  if (!(got.mismatch <= 0.2)) problem(`${what}: differs from its reference by ${got.mismatch.toFixed(3)} of its ink`)
  if (!(Math.abs(got.ink - 1) <= 0.2)) problem(`${what}: ${got.ink.toFixed(3)} times the reference's ink`)
}

const now = page => page.evaluate(() => performance.now())
// Wait until the canvas shows the drawing last asked for, asked after page time t (the viewer asks SETTLE ms after the
// view stops, or at once, as after a swatch)
const drawnSince = (page, t, timeout = 180000) => page.waitForFunction(t => {
  const { asked, shown } = window.__seen
  return asked.at(-1) > t && shown.at(-1) > asked.at(-1)
}, t, { timeout, polling: 100 })

// Open the viewer for n with spy() installed, and wait for its first drawing (loading 23, 56 MB, and drawing it can
// take a busy machine tens of seconds). The viewer puts its canvas in #stage at once: without one in 5 s, fail rather
// than wait, since an SVG viewer would go on to make paths of all of 23's 56 MB.
async function openCanvas(page, n) {
  await page.addInitScript(spy)
  await page.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
  await page.waitForSelector('#stage canvas', { state: 'attached', timeout: 5000 })
  await drawnSince(page, 0)
  await page.waitForFunction(n => document.querySelectorAll('#curves button:enabled').length === n, n)
}

// A page in a context of its own, a window w by h with dpr device pixels to a CSS pixel
async function sized(page, w, h, dpr) {
  const context = await page.context().browser().newContext({ viewport: { width: w, height: h }, deviceScaleFactor: dpr })
  const p = await context.newPage()
  p.setDefaultTimeout(10000)
  await p.route(/fonts\.(googleapis|gstatic)\.com/, r => r.abort())
  return p
}

// Drawing n's file: its text, the first knots of curve 0 (its start and the ends of its first spans, which lie on it),
// and the colours of its uses
async function source(n) {
  const text = await readFile(path.join(ROOT, 'img', `venn-${nn(n)}.svg`), 'utf8'), d = text.indexOf(' d="') + 4
  const xy = text.slice(d, text.indexOf(' C', text.indexOf(' C', d + 1) + 1)).match(/-?\d+(?:\.\d+)?/g).map(Number)
  return { text, knots: [[xy[0], xy[1]], [xy[6], xy[7]]], colours: [...text.matchAll(/ stroke="(#[0-9a-f]{6})"/g)].map(m => m[1]) }
}
const rgb = hex => `rgb(${[1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16)).join(', ')})`

// ---- The shading (quals.py: shading, probe, turn). Its checks look at screenshots, at probes: points of the page at
// least near() pixels on screen from every curve, whose labels (bit i set iff the point is inside curve i) they find
// from the drawing's file themselves.

// A probe is at least NEAR pixels beyond half a line's width from every curve: the shading has not been seen wrong
// further than 1.08 pixels beyond a line's edge, in any browser (AGENTS.md, fourth session)
const NEAR = 1.5
const GRID = 10                       // pixels between the points tried as probes, across and down the window
const FINE = 2                        // and in qual_viewer_shading, which looks at the edges of the shading too
const FAR = 5                         // pixels on screen from every other curve, at least, for a pixel covered()
const site = await readFile(path.join(ROOT, 'site.css'), 'utf8')
const hex = name => site.match(new RegExp(`--${name}: #([0-9a-f]{6});`))[1].match(/../g).map(h => parseInt(h, 16))
const SHADED = hex('line'), UNSHADED = hex('paper')   // a probe's colour, shaded or not
const curvesIn = L => `{${[...Array(31).keys()].filter(i => L >> i & 1).join(', ')}}`   // label L's curves, "{0, 2}"

// The pixels of a PNG with 8 bits a channel, RGB or RGBA, not interlaced, as Playwright's screenshots are: its width
// and height, and the RGBA of its pixels, row by row
function png(b) {
  const chunks = []
  for (let i = 8; i < b.length; i += 12 + b.readUInt32BE(i)) chunks.push([b.toString('latin1', i + 4, i + 8), b.subarray(i + 8, i + 8 + b.readUInt32BE(i))])
  const head = chunks[0][1], w = head.readUInt32BE(0), h = head.readUInt32BE(4)
  assert(chunks[0][0] === 'IHDR' && head[8] === 8 && [2, 6].includes(head[9]) && head[12] === 0,
         `a PNG with ${chunks[0][0]} first, bit depth ${head[8]}, colour type ${head[9]}, interlace ${head[12]}`)
  const bpp = head[9] === 6 ? 4 : 3, stride = w * bpp
  const raw = zlib.inflateSync(Buffer.concat(chunks.filter(([k]) => k === 'IDAT').map(([, data]) => data)))
  const rgba = new Uint8Array(4 * w * h), line = new Uint8Array(stride), up = new Uint8Array(stride)
  for (let y = 0; y < h; y++) {
    const filter = raw[y * (stride + 1)], row = raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1))
    for (let x = 0; x < stride; x++) {
      const a = x < bpp ? 0 : line[x - bpp], b = up[x], c = x < bpp ? 0 : up[x - bpp], p = a + b - c
      const paeth = Math.abs(p - a) <= Math.abs(p - b) && Math.abs(p - a) <= Math.abs(p - c) ? a : Math.abs(p - b) <= Math.abs(p - c) ? b : c
      line[x] = row[x] + [0, a, b, (a + b) >> 1, paeth][filter]
    }
    for (let x = 0; x < w; x++) for (let k = 0; k < 4; k++) rgba[4 * (y * w + x) + k] = k < bpp ? line[bpp * x + k] : 255
    up.set(line)
  }
  return { w, h, rgba }
}

// Drawing n as its file gives it: the side of its page; curve 0's points xy (its start, then three a span); the angles
// its uses turn it by (degrees, clockwise on screen, as in SVG's rotate()); and, for label(), a tree of boxes over runs
// of curve 0's spans: node k covers spans lo[k] to hi[k] - 1, whose control points lie in the box boxes[4k] to
// boxes[4k + 3] (x0, y0, x1, y1), and its children are nodes kids[2k] and kids[2k + 1], or -1 for a single span. Read
// once a run (23's file is 56 MB).
const shapes = new Map()
function shape(n) {
  if (!shapes.has(n)) shapes.set(n, readFile(path.join(ROOT, 'img', `venn-${nn(n)}.svg`), 'utf8').then(text => {
    const d = text.indexOf(' d="M') + 4
    const xy = Float64Array.from(text.slice(d, text.indexOf('"', d)).matchAll(/-?\d+(?:\.\d+)?/g), m => Number(m[0]))
    const spans = (xy.length - 2) / 6, nodes = 2 * spans - 1
    const lo = new Int32Array(nodes), hi = new Int32Array(nodes), kids = new Int32Array(2 * nodes).fill(-1)
    const boxes = new Float64Array(4 * nodes)
    let next = 0
    const build = (a, b) => {
      const k = next++
      lo[k] = a
      hi[k] = b
      if (b - a === 1) {
        const c = xy.subarray(6 * a, 6 * a + 8)
        boxes.set([Math.min(c[0], c[2], c[4], c[6]), Math.min(c[1], c[3], c[5], c[7]),
                   Math.max(c[0], c[2], c[4], c[6]), Math.max(c[1], c[3], c[5], c[7])], 4 * k)
      } else {
        const l = build(a, (a + b) >> 1), r = build((a + b) >> 1, b)
        kids.set([l, r], 2 * k)
        for (let j = 0; j < 4; j++) boxes[4 * k + j] = (j < 2 ? Math.min : Math.max)(boxes[4 * l + j], boxes[4 * r + j])
      }
      return k
    }
    build(0, spans)
    return { side: Number(text.match(/viewBox="0 0 ([\d.]+) /)[1]), xy, lo, hi, kids, boxes,
             angles: [...text.matchAll(/ transform="rotate\(([^ ]+) /g)].map(m => Number(m[1])) }
  }))
  return shapes.get(n)
}

// A cubic span of curve 0, or a piece of one, control points c: the parity of its crossings of the ray from (qx, qy)
// towards +x, or -1 if it comes within far of that point. Halved until each half is either clear of the point (its
// box further than far from it) or small (under far / 16 across, so that no point much further than far is taken for
// one within it) and near it. A piece clear of the point crosses the ray as often as it goes from one side of height qy
// to the other if it lies wholly to the right of the point (an odd number of times iff its ends lie on either side),
// and never otherwise.
function piece(c, qx, qy, far, depth) {
  const x0 = Math.min(c[0], c[2], c[4], c[6]), x1 = Math.max(c[0], c[2], c[4], c[6])
  const y0 = Math.min(c[1], c[3], c[5], c[7]), y1 = Math.max(c[1], c[3], c[5], c[7])
  if (Math.hypot(Math.max(x0 - qx, 0, qx - x1), Math.max(y0 - qy, 0, qy - y1)) > far) return Number(x0 > qx && (c[1] > qy) !== (c[7] > qy))
  if (Math.max(x1 - x0, y1 - y0) < far / 16) return -1
  assert(depth < 60, `a span of curve 0 halved 60 times near (${qx}, ${qy})`)
  const h = (i, j) => (c[i] + c[j]) / 2, [x01, y01, x12, y12, x23, y23] = [h(0, 2), h(1, 3), h(2, 4), h(3, 5), h(4, 6), h(5, 7)]
  const xa = (x01 + x12) / 2, ya = (y01 + y12) / 2, xb = (x12 + x23) / 2, yb = (y12 + y23) / 2, xm = (xa + xb) / 2, ym = (ya + yb) / 2
  const p = piece([c[0], c[1], x01, y01, xa, ya, xm, ym], qx, qy, far, depth + 1)
  const q = piece([xm, ym, xb, yb, x23, y23, c[6], c[7]], qx, qy, far, depth + 1)
  return p < 0 || q < 0 ? -1 : p ^ q
}

// The label of page point (x, y) in drawing sh, or -1 if some curve comes within far page units of it: of the curves
// given, all of them unless said. The point is inside curve i iff, turned back by use i's angle about the page's
// centre, it is inside curve 0: iff a ray from it crosses curve 0 an odd number of times. A run of spans whose box,
// widened by far, misses the point settles that as a piece does (piece()), its ends the run's ends; any other is split,
// down to single spans, then halved.
function label({ side, xy, lo, hi, kids, boxes, angles }, x, y, far, curves = angles.keys()) {
  let L = 0
  for (const i of curves) {
    const a = -angles[i] * Math.PI / 180, cos = Math.cos(a), sin = Math.sin(a), mid = side / 2
    const qx = mid + (x - mid) * cos - (y - mid) * sin, qy = mid + (x - mid) * sin + (y - mid) * cos
    let odd = 0
    for (const stack = [0]; stack.length;) {
      const k = stack.pop(), b = 4 * k
      if (qx < boxes[b] - far || qy < boxes[b + 1] - far || qx > boxes[b + 2] + far || qy > boxes[b + 3] + far)
        odd ^= boxes[b] > qx && (xy[6 * lo[k] + 1] > qy) !== (xy[6 * hi[k] + 1] > qy)
      else if (kids[2 * k] >= 0) stack.push(kids[2 * k], kids[2 * k + 1])
      else {
        const p = piece(xy.subarray(6 * lo[k], 6 * lo[k] + 8), qx, qy, far, 0)
        if (p < 0) return -1
        odd ^= p
      }
    }
    L |= odd << i
  }
  return L
}

// How near the curves a probe of drawing n may be: half a line's width (as wide on screen at any zoom as at fit: see
// qual_viewer_fit) plus NEAR pixels, from a curve's centreline
async function near(page, n) {
  const { page: side, stroke } = await drawing(n), a = await area(page)
  return stroke * a.side / side / 2 + NEAR
}
// The controls' boxes: of everything outside the stage that takes the pointer, with the window's size
const controlBoxes = page => page.evaluate(() => ({ w: innerWidth, h: innerHeight, boxes: [...document.body.querySelectorAll('*')]
  .filter(e => !e.closest('#stage') && e.checkVisibility() && getComputedStyle(e).pointerEvents !== 'none')
  .map(e => { const r = e.getBoundingClientRect(); return [r.left, r.top, r.right, r.bottom] }) }))
// Whether the centre of pixel (x, y) is clear of controls c: 6 pixels inside the window and 6 from every control's box
// (beyond its shadow or focus ring)
const clear = ({ w, h, boxes }, x, y) => x + 0.5 >= 6 && y + 0.5 >= 6 && x + 0.5 <= w - 6 && y + 0.5 <= h - 6 &&
  boxes.every(([l, t, r, b]) => x + 0.5 <= l - 6 || x + 0.5 >= r + 6 || y + 0.5 <= t - 6 || y + 0.5 >= b + 6)
// The probes of drawing n at mapping m (page point (m.x, m.y) at the window's top left, m.s page units to a CSS
// pixel): the pixels of a grid, every grid pixels across and down the window, whose centres are at least near()
// pixels from every curve and clear of the controls, with their labels
async function probes(page, n, m, grid = GRID) {
  const sh = await shape(n), far = await near(page, n), c = await controlBoxes(page), pixels = []
  for (let y = grid >> 1; y < c.h; y += grid) for (let x = grid >> 1; x < c.w; x += grid) pixels.push([x, y])
  return pixels.filter(([x, y]) => clear(c, x, y)).flatMap(([x, y]) => {
    const L = label(sh, m.x + (x + 0.5) * m.s, m.y + (y + 0.5) * m.s, far * m.s)
    return L < 0 ? [] : [{ x, y, label: L }]
  })
}
// The pixels of drawing n at mapping m that a curve's line covers wholly: those whose centres lie within half the
// line's width less a pixel of curve i (of its tangent at a point of it, the points a quarter of a pixel apart), so
// that the line covers them with 0.29 pixel to spare (a pixel's corners are 0.71 from its centre); at least FAR pixels
// from every other curve and clear of the controls. Each with its curve, i, and colour, and the label of the region
// beside it outside curve i (its bit is 0). All of curve 0's spans are tried, so this is for views near fit.
async function covered(page, n, m) {
  const sh = await shape(n), { page: side, stroke } = await drawing(n), { colours } = await source(n), a = await area(page)
  const reach = stroke * a.side / side / 2 - 1, c = await controlBoxes(page), found = new Map(), mid = side / 2
  for (let k = 0; 6 * k + 8 <= sh.xy.length; k++) {
    const [x0, y0, x1, y1, x2, y2, x3, y3] = sh.xy.subarray(6 * k, 6 * k + 8)
    const steps = Math.ceil(4 * (Math.hypot(x1 - x0, y1 - y0) + Math.hypot(x2 - x1, y2 - y1) + Math.hypot(x3 - x2, y3 - y2)) / m.s)
    for (let j = 0; j < steps; j++) {
      const t = j / steps, u = 1 - t, bez = (p0, p1, p2, p3) => u * u * u * p0 + 3 * u * u * t * p1 + 3 * u * t * t * p2 + t * t * t * p3
      const tan = (p0, p1, p2, p3) => u * u * (p1 - p0) + 2 * u * t * (p2 - p1) + t * t * (p3 - p2)
      const [px, py, dx, dy] = [bez(x0, x1, x2, x3), bez(y0, y1, y2, y3), tan(x0, x1, x2, x3), tan(y0, y1, y2, y3)]
      sh.angles.forEach((deg, i) => {   // curve i: curve 0 turned by use i's angle about the page's centre
        const r = deg * Math.PI / 180, cos = Math.cos(r), sin = Math.sin(r)
        const sx = (mid + (px - mid) * cos - (py - mid) * sin - m.x) / m.s, sy = (mid + (px - mid) * sin + (py - mid) * cos - m.y) / m.s
        const ex = dx * cos - dy * sin, ey = dx * sin + dy * cos, X = Math.floor(sx), Y = Math.floor(sy)
        if (Math.abs((X + 0.5 - sx) * ey - (Y + 0.5 - sy) * ex) / Math.hypot(ex, ey) <= reach && clear(c, X, Y)) found.set(`${X} ${Y}`, [X, Y, i])
      })
    }
  }
  return [...found.values()].flatMap(([x, y, i]) => {
    const L = label(sh, m.x + (x + 0.5) * m.s, m.y + (y + 0.5) * m.s, FAR * m.s, [...sh.angles.keys()].filter(j => j !== i))
    return L < 0 ? [] : [{ x, y, curve: i, colour: rgb(colours[i]).match(/\d+/g).map(Number), label: L }]
  })
}
const commonest = ps => [...Map.groupBy(ps, p => p.label)].reduce((a, b) => b[1].length > a[1].length ? b : a)[0]

// Expect a screenshot to show exactly the probes ps of label want shaded, and every other unshaded (and some of
// want's to be among them); and each of the pixels lines (covered()) beside the region of label want, if any are
// given, in its curve's colour, each channel within 8: the shading beneath the curves
async function shows(page, ps, want, what, problem, lines = []) {
  const { w, h, rgba } = png(await page.screenshot())
  const size = await page.evaluate(() => [innerWidth, innerHeight])
  if (String([w, h]) !== String(size)) problem(`${what}: a screenshot of ${w} by ${h} pixels for a window of ${size}`)
  const colour = ({ x, y }) => [...rgba.subarray(4 * (y * w + x), 4 * (y * w + x) + 3)]
  const wrong = ps.filter(p => colour(p).some((v, i) => Math.abs(v - (p.label === want ? SHADED : UNSHADED)[i]) > 8))
  const of = ps.filter(p => p.label === want).length
  if (!of) problem(`${what}: none of the ${ps.length} probes in view has label ${want}`)
  if (wrong.length) problem(`${what}: ${wrong.length} of ${ps.length} probes wrong (${of} of label ${want}, to be shaded), e.g. ` +
                            wrong.slice(0, 3).map(p => `(${p.x}, ${p.y}), label ${p.label}: rgb(${colour(p)})`).join('; '))
  const beside = lines.filter(p => p.label === want || (p.label | 1 << p.curve) === want)
  const hidden = beside.filter(p => colour(p).some((v, i) => Math.abs(v - p.colour[i]) > 8))
  if (lines.length && !beside.length) problem(`${what}: none of the ${lines.length} pixels a line covers is beside the shaded region`)
  if (hidden.length) problem(`${what}: ${hidden.length} of the ${beside.length} pixels a line covers beside the shaded region not in its curve's ` +
                             `colour, e.g. ${hidden.slice(0, 3).map(p => `(${p.x}, ${p.y}) on curve ${p.curve}: rgb(${colour(p)}), not rgb(${p.colour})`).join('; ')}`)
}

// The mapping the SVG's curves are drawn at, from their screen CTM
const mapping = async page => {
  const m = await ctm(page)
  return { s: 1 / m.a, x: -m.e / m.a, y: -m.f / m.d }
}
const checkboxes = page => page.locator('#curves input[type=checkbox]')
// The label of the curves checked
const checked = page => page.evaluate(() => [...document.querySelectorAll('#curves input[type=checkbox]')].reduce((L, c, i) => L | c.checked << i, 0))
// Check exactly the curves of label L, of the n, and wait for the shading's drawing (spy() installed): every checkbox
// that differs but the last is set without an event, and the last clicked, which asks for one drawing. (Asks in a row
// can have a drawing posted before the worker saw the last ask arrive after it, which drawnSince() would take for the
// last ask's.) qual_viewer_checks clicks, presses and taps the checkboxes themselves.
async function check(page, n, L) {
  const count = await checkboxes(page).count()
  if (count !== n) throw new Error(`${count} checkboxes for ${n} curves`)
  const last = await page.evaluate(L => {
    const all = [...document.querySelectorAll('#curves input[type=checkbox]')], differ = all.filter((c, i) => c.checked !== Boolean(L >> i & 1))
    differ.slice(0, -1).forEach(c => { c.checked = !c.checked })
    return all.indexOf(differ.at(-1))
  }, L)
  if (last >= 0) await redrawn(page, () => checkboxes(page).nth(last).click())
}
// Open the viewer for n with spy() installed, and wait until it is ready and its first drawing (the shading) is shown
async function openShaded(page, n) {
  await page.addInitScript(spy)
  await open(page, n)
  await drawnSince(page, 0)
}
// Do act() and wait for the drawing it asks for (spy() installed)
async function redrawn(page, act) {
  const t = await now(page)
  await act()
  await drawnSince(page, t)
}
// The curve each curve lands on when the drawing turns by -360/n degrees (see turn, in quals.py), from the uses' angles
function landing(angles) {
  const n = angles.length, gap = (a, b) => Math.abs(((a - b) % 360 + 540) % 360 - 180)
  return angles.map(a => {
    const j = angles.reduce((best, b, k) => gap(b, a - 360 / n) < gap(angles[best], a - 360 / n) ? k : best, 0)
    assert(gap(angles[j], a - 360 / n) < 1e-6, `no use turns curve 0 by ${a} - 360/${n} degrees: ${angles}`)
    return j
  })
}
// Where qual_viewer_turn and qual_viewer_canvas_turn say curve i lands: on curve LANDS[n](i) (mod n)
const LANDS = { 3: i => i - 1, 7: i => i + 1, 23: i => i + 1 }
// Expect lands, landing()'s, to be those
function stated(lands, n, problem) {
  const want = lands.map((_, i) => (LANDS[n](i) + n) % n)
  if (String(lands) !== String(want)) problem(`n=${n}: curve i lands on curve lands[i], lands = [${lands}], not [${want}] as the qual says`)
}
const landed = (L, lands) => lands.reduce((M, j, i) => M | (L >> i & 1) << j, 0)   // label L, every curve turned
// The turns act() sets off (spy() installed), k of them: a log of every animation frame, every ask for a drawing
// (postMessage) and every drawing shown (transferFromImageBitmap), from just before act() until k asks have each been
// followed by a drawing shown and a frame has passed after the last (or a minute has). Each entry has its kind, the
// angle #region is turned by (degrees, clockwise on screen) and its transform's entries (a turn has a = d, b = -c,
// e = f = 0 and a² + b² = 1), its transform-origin, the label checked, and whether the turn button is enabled and has
// the focus; and where the curves are: #picture's transform, and the boxes on the screen of the SVG, its paths and the
// curves' canvas (every canvas in #stage outside #region), and whether #region holds its canvas alone.
async function turns(page, k, act) {
  await page.evaluate(k => {
    const region = document.getElementById('region'), button = document.getElementById('turn'), log = []
    const boxes = [...document.querySelectorAll('#curves input[type=checkbox]')], picture = document.getElementById('picture')
    const curves = [...document.querySelectorAll('#stage svg, #stage path, #stage canvas')].filter(e => !region.contains(e))
    const note = kind => {
      const s = getComputedStyle(region), m = s.transform === 'none' ? new DOMMatrix() : new DOMMatrix(s.transform)
      log.push({ kind, angle: Math.atan2(m.b, m.a) * 180 / Math.PI, m: [m.a, m.b, m.c, m.d, m.e, m.f], origin: s.transformOrigin,
                 label: boxes.reduce((L, c, i) => L | c.checked << i, 0), enabled: !button.disabled, focus: document.activeElement === button,
                 picture: getComputedStyle(picture).transform,
                 curves: curves.flatMap(e => { const r = e.getBoundingClientRect(); return [r.left, r.top, r.width, r.height] }),
                 alone: region.childElementCount === 1 && region.firstElementChild instanceof HTMLCanvasElement })
    }
    const wrap = (proto, name, kind) => {   // log each call of proto[name], until the returned function puts it back
      const f = proto[name]
      proto[name] = function (...args) {
        note(kind)
        return f.apply(this, args)
      }
      return () => { proto[name] = f }
    }
    const unwrap = [wrap(Worker.prototype, 'postMessage', 'ask'), wrap(ImageBitmapRenderingContext.prototype, 'transferFromImageBitmap', 'shown')]
    const t0 = performance.now()
    window.__turns = new Promise(done => {
      const frame = () => {
        note('frame')
        const asks = log.flatMap((e, i) => e.kind === 'ask' ? [i] : [])
        const last = asks.length < k ? -1 : log.findIndex((e, i) => i > asks[k - 1] && e.kind === 'shown')
        if ((last >= 0 && last < log.length - 1) || performance.now() - t0 > 60000) {
          unwrap.forEach(put => put())
          return done(log)
        }
        requestAnimationFrame(frame)
      }
      requestAnimationFrame(frame)
    })
  }, k)
  await act()
  return page.evaluate(() => window.__turns)
}
// Expect a log of turns() to show labels.length - 1 turns of the shading by 1/n of a full turn anticlockwise about the
// page's centre (window point o2), turn j taking the label checked from labels[j - 1] to labels[j]: until it changes the
// checkboxes, when it asks for a drawing (one ask a turn), #region turned by angles from 0 to -360/n degrees, some
// strictly between, and labels[j - 1] checked; from that ask until a drawing is shown after it, turned by exactly
// -360/n degrees, and labels[j] checked; after the last turn's drawing, not turned. Throughout, the turn button enabled,
// and if keys, with the focus; the curves where they were at the first entry (#picture's transform the same, and the
// boxes to 0.01 pixel); and #region holding its canvas alone. (Angles to 1e-3 degrees: the computed transform gives
// six digits.)
function turnedWell(log, n, o2, labels, keys, what, problem) {
  const count = labels.length - 1, asks = log.flatMap((e, i) => e.kind === 'ask' ? [i] : [])
  // shown[j]: the end of the drawing shown first after ask j, the last of the drawings shown with it (the page shows
  // its canvases' drawings together)
  const shown = asks.map(a => {
    const first = log.findIndex((e, i) => i > a && e.kind === 'shown')
    return first < 0 ? -1 : log.findIndex((e, i) => i > first && e.kind !== 'shown') - 1
  })
  if (asks.length !== count || shown.some(i => i < 0))
    return problem(`${what}: ${asks.length} drawings asked for and ${shown.filter(i => i >= 0).length} shown after their asks, not ${count}`)
  const flagged = new Set(), spun = Array(count).fill(false)
  log.forEach((e, i) => {
    // j: the turns whose checkboxes have changed; held: the last of them still waiting for its drawing; moved: how far
    // the curves' boxes are from the first entry's
    const j = asks.filter(a => a <= i).length, held = j > 0 && i <= shown[j - 1], [a, b, c, d, x, y] = e.m
    const moved = Math.max(...e.curves.map((v, k) => Math.abs(v - log[0].curves[k])), e.curves.length === log[0].curves.length ? 0 : Infinity)
    const [when, lo, hi] = held ? [`from turn ${j}'s ask for a drawing until one was shown`, -360 / n, -360 / n]
      : j === count ? ['after the last turn\'s drawing', 0, 0] : [`as turn ${j + 1} spun`, -360 / n, 0]
    if (!held && j < count && e.kind === 'frame' && e.angle > -360 / n + 0.5 && e.angle < -0.5) spun[j] = true
    for (const [flaw, bad, says] of [
      ['turn', !(Math.abs(a - d) < 1e-4 && Math.abs(b + c) < 1e-4 && Math.abs(a * a + b * b - 1) < 1e-4 && Math.abs(x) < 1e-4 && Math.abs(y) < 1e-4),
       `#region's transform is matrix(${e.m}), not a turn`],
      ['angle', !(e.angle >= lo - 1e-3 && e.angle <= hi + 1e-3), `#region turned by ${e.angle.toFixed(4)} degrees, not ${lo === hi ? lo.toFixed(4) : `${lo.toFixed(4)} to 0`}`],
      ['label', e.label !== labels[j], `curves ${curvesIn(e.label)} checked, not ${curvesIn(labels[j])}`],
      ['origin', e.origin.split(' ').some((v, k) => !(Math.abs(parseFloat(v) - o2[k]) <= 0.5)),
       `#region turned about ${e.origin}, not the page's centre at (${o2.map(v => v.toFixed(1))})`],
      ['enabled', !e.enabled, 'the turn button disabled'],
      ['focus', keys && !e.focus, 'the turn button without the focus'],
      ['curves', e.picture !== log[0].picture || !(moved <= 0.01),
       `the curves moved: #picture's transform ${e.picture}, first ${log[0].picture}; their boxes up to ${moved} pixels from the first`],
      ['region', !e.alone, '#region holds more than its canvas'],
    ]) {
      if (bad && !flagged.has(`${when} ${flaw}`)) problem(`${what}, ${when} (${e.kind}, entry ${i} of ${log.length}): ${says}`)
      if (bad) flagged.add(`${when} ${flaw}`)
    }
  })
  spun.forEach((s, j) => { if (!s) problem(`${what}: turn ${j + 1} not animated: #region turned by no angle strictly between 0 and -360/${n} degrees`) })
}
// Expect the turn button's face to say τ/n, n's value, to fit inside the button, and its τ to be a glyph, under 0.7
// em wide, not the box a browser draws for a character its font lacks, an em wide (Firefox drew one with Google Fonts
// blocked, as here, when the fallback was Georgia)
async function faced(page, n, problem) {
  const [face, text, box, tau] = await page.evaluate(() => {
    const b = document.getElementById('turn'), r = document.createRange(), first = document.createRange()
    r.selectNodeContents(b)
    first.setStart(b.firstChild, 0)
    first.setEnd(b.firstChild, 1)
    return [b.textContent, ...[r, b].map(e => { const q = e.getBoundingClientRect(); return [q.left, q.top, q.right, q.bottom] }),
            first.getBoundingClientRect().width / parseFloat(getComputedStyle(b).fontSize)]
  })
  if (face !== `τ/${n}`) problem(`n=${n}: the turn button's face says ${JSON.stringify(face)}, not "τ/${n}"`)
  if (!(text[0] >= box[0] && text[1] >= box[1] && text[2] <= box[2] && text[3] <= box[3]))
    problem(`n=${n}: the turn button's face, at ${text.map(Math.round)}, spills out of it, at ${box.map(Math.round)}`)
  if (!(tau < 0.7)) problem(`n=${n}: the turn button's τ is ${tau.toFixed(3)} em wide, not under 0.7: a missing glyph's box`)
}

const CHECKS = {
  async fit(page, problem) {
    for (const n of PATHS) {
      await (async () => {
        await open(page, n)
        const { page: side, stroke } = await drawing(n)
        const m = await ctm(page)
        const a = await area(page), k = a.side / side
        holds(problem, m, [a.x, a.y], [side / 2, side / 2], k, `n=${n}, the page's centre`)
        ;(await strokes(page)).forEach(([effect, width], i) => {
          if (effect !== 'non-scaling-stroke') problem(`n=${n}: curve ${i} has vector-effect ${effect}`)
          if (Math.abs(width / (stroke * k) - 1) > 1e-3) problem(`n=${n}: curve ${i} is ${width}px wide, not ${stroke * k}px`)
        })
        // The paths drawn are the file's: path i is the one path turned as use i says, in use i's colour (compared in
        // the page: 19's paths are megabytes of text)
        const wrong = await page.evaluate(async file => {
          const src = new DOMParser().parseFromString(await (await fetch(file)).text(), 'image/svg+xml')
          const num = s => s.match(/-?\d+(?:\.\d+)?/g).map(Number)
          const base = num(src.querySelector('path').getAttribute('d'))
          const drawn = [...document.querySelectorAll('#stage path')]
          return [...src.querySelectorAll('use')].flatMap((u, i) => {
            const [a, cx, cy] = num(u.getAttribute('transform')), r = a * Math.PI / 180, c = Math.cos(r), s = Math.sin(r)
            const p = drawn[i], xy = num(p.getAttribute('d'))
            let off = xy.length === base.length ? 0 : Infinity   // a loop: 19's 330,000 numbers overflow Math.max(...)
            for (let j = 0; j < xy.length && off < Infinity; j += 2) {
              const x = base[j] - cx, y = base[j + 1] - cy
              off = Math.max(off, Math.abs(xy[j] - (cx + x * c - y * s)), Math.abs(xy[j + 1] - (cy + x * s + y * c)))
            }
            return off <= 0.001 && p.id === u.id && p.getAttribute('stroke') === u.getAttribute('stroke') ? [] :
              [`${p.id}: ${off} units off the file's curve ${u.id}, stroke ${p.getAttribute('stroke')} for ${u.getAttribute('stroke')}`]
          }).concat(drawn.length === src.querySelectorAll('use').length ? [] : [`${drawn.length} paths drawn`])
        }, `img/venn-${nn(n)}.svg`)
        wrong.forEach(w => problem(`n=${n}: ${w}`))
      })().catch(e => problem(`n=${n}: ${e.name}: ${e.message.split('\n')[0]}`))
    }
  },

  async curves(page, problem) {
    await open(page, SMALL)
    const state = () => page.evaluate(() => ({
      shown: [...document.querySelectorAll('#stage path')].map(p => getComputedStyle(p).display !== 'none'),
      pressed: [...document.querySelectorAll('#curves button')].map(b => b.getAttribute('aria-pressed') === 'true'),
      colours: [...document.querySelectorAll('#curves button')].map(b => getComputedStyle(b).backgroundColor),
      opacity: [...document.querySelectorAll('#curves button')].map(b => getComputedStyle(b).opacity),
      strokes: [...document.querySelectorAll('#stage path')].map(p => getComputedStyle(p).stroke) }))
    const swatch = k => page.locator('#curves button').nth(k)
    const expect = (s, k, what) => {   // curves 0 to k shown, and exactly their swatches pressed
      const want = s.shown.map((_, i) => i <= k)
      if (String(s.shown) !== String(want)) problem(`${what}: curves shown ${s.shown}, not ${want}`)
      if (String(s.pressed) !== String(want)) problem(`${what}: swatches pressed ${s.pressed}, not ${want}`)
      // a shown curve's swatch is its colour; a hidden one's is faded, by its fill and not its opacity, which would
      // fade its focus ring too
      const fill = s.colours.map((c, i) => (c === s.strokes[i]) === (i <= k))
      if (fill.includes(false)) problem(`${what}: swatch fills ${s.colours} against curves ${s.strokes}`)
      if (s.opacity.some(o => o !== '1')) problem(`${what}: swatch opacities ${s.opacity}`)
    }
    const s0 = await state()
    if (s0.colours.length !== SMALL) problem(`${s0.colours.length} swatches for ${SMALL} curves`)
    if (String(s0.colours) !== String(s0.strokes)) problem(`swatches ${s0.colours}, curves ${s0.strokes}`)
    expect(s0, SMALL - 1, 'on opening')
    await swatch(0).click()
    expect(await state(), 0, 'after clicking the first swatch')
    await swatch(2).click()
    expect(await state(), 2, 'after clicking the third swatch')
    await swatch(2).click()
    expect(await state(), 2, 'after clicking the third swatch again')
    await swatch(SMALL - 1).click()
    expect(await state(), SMALL - 1, 'after clicking the last swatch')
    await swatch(1).click()
    await page.keyboard.press('Escape')
    expect(await state(), SMALL - 1, 'after clicking the second swatch and pressing Escape')
  },

  async wheel(page, problem) {
    await open(page, SMALL)
    const s = [W * 0.3, H * 0.4]
    const m0 = await ctm(page), p = under(m0, s)
    await page.mouse.move(...s)
    await page.mouse.wheel(0, -400)
    await frames(page)
    holds(problem, await ctm(page), s, p, m0.a * Math.E, 'wheel 400px up')
    const fitWidths = await strokes(page)
    const m1 = await ctm(page)
    await page.keyboard.down('Control')
    await page.mouse.wheel(0, 100)
    await page.keyboard.up('Control')
    await frames(page)
    holds(problem, await ctm(page), s, p, m1.a / Math.E, 'ctrl+wheel 100px down')
    // Wheels that count in lines (16 pixels each here) or pages (the window's height), as some mice report
    for (const [deltaMode, deltaY, what] of [[1, -25, 'wheel 25 lines up'], [2, -0.5, 'wheel half a page up']]) {
      const m = await ctm(page)
      await page.evaluate(([deltaMode, deltaY, [x, y]]) => document.getElementById('stage').dispatchEvent(
        new WheelEvent('wheel', { deltaMode, deltaY, clientX: x, clientY: y, bubbles: true, cancelable: true })), [deltaMode, deltaY, s])
      holds(problem, await ctm(page), s, p, m.a * Math.E, what)
    }
    await page.mouse.wheel(0, -4000)
    const deep = await strokes(page)
    if (String(deep) !== String(fitWidths)) problem(`zoomed in, the lines are ${deep}, not ${fitWidths} as before`)
  },

  async drag(page, problem) {
    await open(page, SMALL)
    const s0 = [W * 0.4, H * 0.45], s1 = [s0[0] + 120, s0[1] + 80]
    const m0 = await ctm(page), p = under(m0, s0)
    await page.mouse.move(...s0)
    await page.mouse.down()
    await page.mouse.move(...s1, { steps: 6 })
    await page.mouse.up()
    holds(problem, await ctm(page), s1, p, m0.a, 'drag')
    const hit = await page.evaluate(() => {
      const path = document.getElementById('curve-0'), m = path.getScreenCTM(), q = path.getPointAtLength(0)
      return document.elementFromPoint(m.a * q.x + m.e, m.d * q.y + m.f).id
    })
    if (hit !== 'stage') problem(`the pointer over curve 0 hits #${hit}, not #stage`)
    // the top bar's middle, between its two groups, and the swatches' first end (the left of a row, the top of a
    // column), beside the swatches, which are centred along it
    for (const [sel, what, f] of [['#top', 'the top bar', 0.5], ['#curves', 'the swatches', 0.02]]) {
      const box = await page.locator(sel).boundingBox(), long = box.width >= box.height
      const s = [Math.round(box.x + box.width * (long ? f : 0.5)), Math.round(box.y + box.height * (long ? 0.5 : f))]
      const target = await page.evaluate(([x, y]) => document.elementFromPoint(x, y).id, s)
      if (target !== 'stage') problem(`${what}, between its controls, hits #${target}, not the drawing`)
      // inward: Playwright's Firefox drops mouse events outside the window, and a column's drag starts near its edge
      const m = await ctm(page), q = under(m, s), s2 = [s[0] + (s[0] > W / 2 ? -60 : 60), s[1] + 30]
      await page.mouse.move(...s)
      await page.mouse.down()
      await page.mouse.move(...s2, { steps: 4 })
      await page.mouse.up()
      holds(problem, await ctm(page), s2, q, m.a, `drag from ${what}, between its controls`)
    }
  },

  async pinch(page, problem) {
    await open(page, SMALL)
    const a = [W * 0.3, H * 0.5], b = [W * 0.4, H * 0.5], b2 = [W * 0.5, H * 0.5]
    const m0 = await ctm(page), p = under(m0, a)
    // Two touch pointers, as a phone reports two fingers: one stays at a, the other moves from b to b2, doubling
    // their distance apart. (Synthetic events: Playwright drives one touch at a time.)
    const touch = (id, [x, y], buttons) => ({ pointerId: id, pointerType: 'touch', isPrimary: id === 1, clientX: x, clientY: y, buttons })
    await pointers(page, [['pointerdown', touch(1, a, 1)], ['pointerdown', touch(2, b, 1)], ['pointermove', touch(2, b2, 1)],
                          ['pointerup', touch(2, b2, 0)], ['pointerup', touch(1, a, 0)]])
    holds(problem, await ctm(page), a, p, m0.a * 2, 'pinch')
    const action = await page.evaluate(() => getComputedStyle(document.documentElement).touchAction)
    if (action !== 'none') problem(`the page has touch-action ${action}, so a pinch over a control zooms the whole page`)
  },

  async mouse(page, problem) {
    await open(page, SMALL)
    const s0 = [W * 0.4, H * 0.45], s1 = [s0[0] + 120, s0[1] + 80]
    const m0 = await ctm(page), p = under(m0, s0)
    const mouse = (button, [x, y], buttons) => ({ pointerId: 1, pointerType: 'mouse', isPrimary: true, button, buttons, clientX: x, clientY: y })
    // A right-button drag (which opens a context menu) and a middle-button drag
    for (const [button, buttons, what] of [[2, 2, 'right-button drag'], [1, 4, 'middle-button drag']]) {
      await pointers(page, [['pointerdown', mouse(button, s0, buttons)], ['pointermove', mouse(-1, s1, buttons)],
                            ['pointerup', mouse(button, s1, 0)]])
      holds(problem, await ctm(page), s0, p, m0.a, what)
    }
    // A left press whose release never arrives (after a context menu, say), then the mouse moving with no button down
    await pointers(page, [['pointerdown', mouse(0, s0, 1)], ['pointermove', mouse(-1, s1, 0)]])
    holds(problem, await ctm(page), s0, p, m0.a, 'mouse moved with no button down after a lost release')
  },

  async controls(page, problem) {
    await open(page, SMALL)
    // The wheel, and a trackpad pinch (the wheel with ctrl held), over the controls zoom the drawing too
    for (const [sel, ctrl, delta, f] of [['#in', false, -400, Math.E], ['#curves button', true, 100, 1 / Math.E], ['#n', false, -400, Math.E]]) {
      const box = await page.locator(sel).first().boundingBox()
      // a whole pixel near the control's centre: browsers report a wheel's position in whole pixels
      const s = [Math.round(box.x + box.width / 2), Math.round(box.y + box.height / 2)]
      const m = await ctm(page), p = under(m, s)
      await page.mouse.move(...s)
      if (ctrl) await page.keyboard.down('Control')
      await page.mouse.wheel(0, delta)
      if (ctrl) await page.keyboard.up('Control')
      await frames(page)
      holds(problem, await ctm(page), s, p, m.a * f, `${ctrl ? 'ctrl+' : ''}wheel over ${sel}`)
    }
  },


  async cancel(page, problem) {
    await open(page, SMALL)
    // The viewer cancels every wheel and gesture event, which stops the browser zooming or scrolling the page itself.
    // A listener added after the page's own, on the same target, sees its verdict.
    const r = await page.evaluate(() => {
      const seen = []
      addEventListener('wheel', e => seen.push(e.defaultPrevented))
      for (const [id, ctrlKey] of [['stage', false], ['in', true], ['curves', false]]) document.getElementById(id).dispatchEvent(
        new WheelEvent('wheel', { deltaY: -10, ctrlKey, clientX: 300, clientY: 300, bubbles: true, cancelable: true }))
      const gesture = type => {
        const e = new Event(type, { bubbles: true, cancelable: true })
        Object.assign(e, { scale: 1.1, clientX: 300, clientY: 300 })
        return document.getElementById('in').dispatchEvent(e)   // false if cancelled
      }
      return { wheels: seen, gestures: [gesture('gesturestart'), gesture('gesturechange')] }
    })
    if (String(r.wheels) !== 'true,true,true') problem(`wheel events cancelled: ${r.wheels} (over the drawing, ctrl over +, over the swatches)`)
    if (String(r.gestures) !== 'false,false') problem(`gesturestart and gesturechange over + not cancelled: ${r.gestures}`)
  },

  async gesture(page, problem) {
    await open(page, SMALL)
    // Safari reports a trackpad pinch as gesturestart and gesturechange events carrying the scale so far
    const gesture = (events) => page.evaluate(events => {
      for (const [type, scale, x, y] of events) {
        const e = new Event(type, { bubbles: true, cancelable: true })
        Object.assign(e, { scale, clientX: x, clientY: y })
        document.getElementById('stage').dispatchEvent(e)
      }
    }, events)
    const s = [W * 0.35, H * 0.6]
    const m0 = await ctm(page), p = under(m0, s)
    await gesture([['gesturestart', 1, ...s], ['gesturechange', 1.5, ...s], ['gesturechange', 2, ...s], ['gestureend', 2, ...s]])
    holds(problem, await ctm(page), s, p, m0.a * 2, 'trackpad pinch to scale 2')
    await gesture([['gesturestart', 1, ...s], ['gesturechange', 1.05, ...s], ['gesturechange', 2, ...s], ['gestureend', 2, ...s]])
    holds(problem, await ctm(page), s, p, m0.a * 4, 'a second trackpad pinch to scale 2 (Safari starts each at 1)')
    // A touchscreen pinch in Safari sends gesture events as well as the pointers, which already zoom: no second zoom
    const m1 = await ctm(page)
    await pointers(page, [['pointerdown', { pointerId: 5, pointerType: 'touch', clientX: s[0], clientY: s[1], buttons: 1 }]])
    await gesture([['gesturestart', 1, ...s], ['gesturechange', 2, ...s]])
    await pointers(page, [['pointerup', { pointerId: 5, pointerType: 'touch', clientX: s[0], clientY: s[1], buttons: 0 }]])
    holds(problem, await ctm(page), s, p, m1.a, 'gesture events during a touch')
  },

  async settle(page, problem) {
    await open(page, Math.max(...PATHS))
    // A drag, a run of wheel turns and a two-finger pinch as a hand makes them, an event every 16 ms (60 a second),
    // driven from inside the page so that they come that fast however slowly this harness could step them
    const r = await page.evaluate(async () => {
      const svg = document.querySelector('#stage svg'), picture = document.getElementById('picture'), stage = document.getElementById('stage')
      const state = () => {
        const m = svg.getScreenCTM(), s = getComputedStyle(picture)
        return { viewBox: svg.getAttribute('viewBox'), transform: s.transform, willChange: s.willChange, m: [m.a, m.d, m.e, m.f],
                 width: getComputedStyle(svg.querySelector('path')).strokeWidth }
      }
      const ptr = (type, id, x, y, buttons, pointerType) => stage.dispatchEvent(new PointerEvent(type,
        { pointerId: id, pointerType, isPrimary: id === 1, button: 0, buttons, clientX: x, clientY: y, bubbles: true }))
      const wait = ms => new Promise(ok => setTimeout(ok, ms))
      const before = state(), during = []
      ptr('pointerdown', 1, 400, 300, 1, 'mouse')
      for (let i = 1; i <= 15; i++) { ptr('pointermove', 1, 400 + 5 * i, 300 + 3 * i, 1, 'mouse'); during.push(state()); await wait(16) }
      ptr('pointerup', 1, 475, 345, 0, 'mouse')
      for (let i = 0; i < 10; i++) {
        dispatchEvent(new WheelEvent('wheel', { deltaY: -40, clientX: 600, clientY: 400, bubbles: true, cancelable: true }))
        during.push(state()); await wait(16)
      }
      ptr('pointerdown', 1, 500, 400, 1, 'touch'); ptr('pointerdown', 2, 560, 400, 1, 'touch')
      for (let i = 1; i <= 10; i++) { ptr('pointermove', 2, 560 + 6 * i, 400, 1, 'touch'); during.push(state()); await wait(16) }
      ptr('pointerup', 2, 620, 400, 0, 'touch'); ptr('pointerup', 1, 500, 400, 0, 'touch')
      const moved = state()
      const t0 = performance.now()
      while (svg.getAttribute('viewBox') === before.viewBox && performance.now() - t0 < 2000) await wait(10)
      await wait(50)
      return { before, during, moved, after: state() }
    })
    const IDENTITY = 'matrix(1, 0, 0, 1, 0, 0)'
    if (r.before.transform !== IDENTITY) problem(`on opening, the picture's transform is ${r.before.transform}, not the identity`)
    if (r.before.willChange !== 'transform') problem(`the picture has will-change ${r.before.willChange}, so moving it may redraw it`)
    const redrawn = r.during.filter(s => s.viewBox !== r.before.viewBox).length
    if (redrawn) problem(`drawn anew in ${redrawn} of the 35 events of the gestures`)
    const unmoved = r.during.filter(s => s.transform === IDENTITY).length
    if (unmoved) problem(`the picture not moved by a transform in ${unmoved} of the 35 events`)
    if (r.after.viewBox === r.before.viewBox) problem('not drawn anew within 2 seconds of the gestures ending')
    if (r.after.transform !== IDENTITY) problem(`once drawn anew, the picture's transform is ${r.after.transform}, not the identity`)
    // Drawn anew, the drawing is where the moved picture showed it, at the same scale, with lines as wide as at fit
    const [a, d, e, f] = r.moved.m, [a2, d2, e2, f2] = r.after.m
    if (Math.abs(a2 / a - 1) > 1e-6 || Math.abs(d2 / d - 1) > 1e-6 || Math.abs(e2 - e) > 0.5 || Math.abs(f2 - f) > 0.5)
      problem(`drawn anew at ${r.after.m}, not where the moved picture was, ${r.moved.m}`)
    if (r.after.width !== r.before.width) problem(`lines ${r.after.width} wide once drawn anew, not ${r.before.width}`)
  },

  async slow(page, problem) {
    await open(page, SMALL)
    const r = await page.evaluate(async () => {
      const stage = document.getElementById('stage'), note = document.getElementById('slow')
      const ptr = (type, x, buttons) => stage.dispatchEvent(new PointerEvent(type,
        { pointerId: 1, pointerType: 'mouse', isPrimary: true, button: 0, buttons, clientX: x, clientY: 300, bubbles: true }))
      const frame = () => new Promise(ok => requestAnimationFrame(ok)), shown = () => note.checkVisibility()
      const quiet = shown()
      ptr('pointerdown', 400, 1)
      for (let i = 1; i <= 6; i++) { ptr('pointermove', 400 + 5 * i, 1); await frame() }
      const fast = shown()
      ptr('pointermove', 440, 1)
      const t0 = performance.now()
      while (performance.now() - t0 < 400) {}   // a frame that takes 400 ms, as moving 19 does in Firefox
      ptr('pointermove', 445, 1)                // and the hand still moving, as it would be
      await frame(); await frame()
      const slow = shown()
      ptr('pointerup', 440, 0)
      await new Promise(ok => setTimeout(ok, 800))
      return { quiet, fast, slow, after: shown() }
    })
    const want = { quiet: false, fast: false, slow: true, after: false }
    if (JSON.stringify(r) !== JSON.stringify(want)) problem(`the slow note shown: ${JSON.stringify(r)}, not ${JSON.stringify(want)}`)
  },

  async dblclick(page, problem) {
    await open(page, SMALL)
    const s = [W * 0.6, H * 0.35]
    const m0 = await ctm(page), p = under(m0, s)
    await page.mouse.dblclick(...s)
    holds(problem, await ctm(page), s, p, m0.a * 2, 'double-click')
  },

  async buttons(page, problem) {
    await open(page, SMALL)
    const a = await area(page), c = [a.x, a.y]
    const m0 = await ctm(page), p = under(m0, c)
    await page.click('#in')
    holds(problem, await ctm(page), c, p, m0.a * 2, '+ button')
    await page.click('#out')
    await page.click('#out')
    holds(problem, await ctm(page), c, p, m0.a / 2, '+ then − twice')
    await page.mouse.move(W * 0.2, H * 0.3)
    await page.mouse.down()
    await page.mouse.move(W * 0.3, H * 0.2, { steps: 4 })
    await page.mouse.up()
    await page.click('#fit')
    holds(problem, await ctm(page), c, p, m0.a, 'fit button after a drag')
  },

  async keys(page, problem) {
    await open(page, SMALL)
    const a = await area(page), c = [a.x, a.y], STEP = a.side / 10
    const m0 = await ctm(page), p = under(m0, c)
    await page.keyboard.press('+')
    holds(problem, await ctm(page), c, p, m0.a * 2, '+ key')
    await page.keyboard.press('Control+0')
    await page.keyboard.press('Meta+0')
    holds(problem, await ctm(page), c, p, m0.a * 2, 'ctrl+0 and cmd+0, the browser\'s own zoom keys')
    await page.keyboard.press('-')
    await page.keyboard.press('-')
    holds(problem, await ctm(page), c, p, m0.a / 2, '+ key then - key twice')
    await page.keyboard.press('0')
    holds(problem, await ctm(page), c, p, m0.a, '0 key')
    await page.keyboard.press('=')
    holds(problem, await ctm(page), c, p, m0.a * 2, '= key (+ without shift)')
    await page.keyboard.press('Alt+0')
    holds(problem, await ctm(page), c, p, m0.a * 2, 'alt+0')
    await page.keyboard.press('0')
    for (const [key, dx, dy] of [['ArrowRight', STEP, 0], ['ArrowLeft', -STEP, 0], ['ArrowDown', 0, STEP], ['ArrowUp', 0, -STEP]]) {
      const q = under(await ctm(page), [c[0] + dx, c[1] + dy])
      await page.keyboard.press(key)
      holds(problem, await ctm(page), c, q, m0.a, `${key} key`)
    }
  },

  async limits(page, problem) {
    await open(page, SMALL)
    const m0 = await ctm(page)
    for (let i = 0; i < 6; i++) await page.click('#out')
    const lo = await ctm(page)
    if (Math.abs(lo.a / (m0.a / 2) - 1) > 1e-3) problem(`zoomed out as far as it goes: scale ${lo.a}, not ${m0.a / 2}`)
    await page.mouse.move(W / 2, H / 2)
    for (let i = 0; i < 12; i++) await page.mouse.wheel(0, -4000)
    await frames(page)
    const hi = await ctm(page)
    if (Math.abs(hi.a / (m0.a * 1000) - 1) > 1e-3) problem(`zoomed in as far as it goes: scale ${hi.a}, not ${m0.a * 1000}`)
  },

  async resize(page, problem) {
    await openShaded(page, SMALL)
    await page.click('#in')
    const a0 = await area(page), c = [a0.x, a0.y], m0 = await ctm(page), p = under(m0, c)
    await page.setViewportSize({ width: 800, height: 600 })
    await frames(page)
    const a1 = await area(page)
    holds(problem, await ctm(page), [a1.x, a1.y], p, m0.a * a1.side / a0.side, 'window resized to 800 by 600')
    // Too short for the controls: fitted, the drawing is still there, half the window's shorter side or more (an
    // invalid viewBox would leave the identity, which a mere lower bound on the scale would pass)
    await page.setViewportSize({ width: 1200, height: 100 })
    await page.keyboard.press('0')
    await frames(page)
    const a2 = await area(page)
    if (a2.side < 50) problem(`in a 1200 by 100 window the drawing would be ${a2.side} pixels, under half the window's shorter side`)
    holds(problem, await ctm(page), [a2.x, a2.y], [25600, 25600], a2.side / 51200, 'fitted in a 1200 by 100 window')
    // No pixels high, then none wide (a pixel in WebKit, whose Playwright refuses a window of none), then as it was:
    // each time drawn anew (spy()), with no error
    const none = page.context().browser().browserType().name() === 'webkit' ? 1 : 0
    for (const [w, h] of [[W, none], [none, H], [W, H]]) {
      const t = await now(page)
      await page.setViewportSize({ width: w, height: h })
      await page.waitForFunction(t => !document.getElementById('error').hidden ||
                                      (window.__seen.asked.at(-1) > t && window.__seen.shown.at(-1) > window.__seen.asked.at(-1)), t, { timeout: 60000 })
      const error = await page.evaluate(() => document.getElementById('error').hidden ? null : document.getElementById('error').textContent)
      if (error !== null) problem(`in a ${w} by ${h} window: the error "${error}"`)
    }
  },

  async links(page, problem) {
    await open(page, SMALL)
    const got = await page.evaluate(() => ({ title: document.title, back: document.getElementById('back').href,
                                             raw: document.getElementById('raw').href,
                                             role: document.querySelector('#stage svg').getAttribute('role'),
                                             label: document.querySelector('#stage svg').getAttribute('aria-label') }))
    const want = { title: `${SMALL} · Diagrammata Venniana Symmetrica`, back: `${BASE}/index.html#n${SMALL}`,
                   raw: `${BASE}/img/venn-${nn(SMALL)}.svg`, role: 'img' }
    for (const k in want) if (got[k] !== want[k]) problem(`${k} is ${got[k]}, not ${want[k]}`)
    if (!(got.label || '').includes(String(SMALL))) problem(`the drawing's label is ${JSON.stringify(got.label)}, without ${SMALL}`)
  },

  async loading(page, problem) {
    let release
    const gate = new Promise(ok => { release = ok })
    await page.route(`**/img/venn-${nn(SMALL)}.svg`, async route => { await gate; await route.continue() })
    await page.goto(`${BASE}/view.html?n=${SMALL}`)
    await page.waitForSelector('#curves button')
    const state = async () => ({ ...(await page.evaluate(() => ({
      image: [...document.querySelectorAll('#stage image')].map(i => i.getAttribute('href')),
      curves: document.querySelectorAll('#stage path').length,
      enabled: document.querySelectorAll('#curves button:enabled').length,
      swatches: document.querySelectorAll('#curves button').length,
      turn: [document.getElementById('turn').disabled, getComputedStyle(document.getElementById('turn')).color] }))),
      status: await page.locator('#status').isVisible() })
    const colour = name => `rgb(${hex(name).join(', ')})`   // site.css's colour --name, as getComputedStyle() gives it
    const s0 = await state()
    const want0 = { image: [`img/venn-${nn(SMALL)}.png`], curves: 0, enabled: 0, swatches: SMALL, turn: [true, colour('muted')], status: true }
    if (JSON.stringify(s0) !== JSON.stringify(want0)) problem(`while the SVG loads: ${JSON.stringify(s0)}, not ${JSON.stringify(want0)}`)
    // The disabled turn button has no hover look either
    await page.hover('#turn')
    const border = await page.evaluate(() => getComputedStyle(document.getElementById('turn')).borderTopColor)
    if (border !== colour('line')) problem(`while the SVG loads, the turn button, hovered over, has border ${border}, not ${colour('line')}`)
    const box = () => page.evaluate(() => {
      const r = document.querySelector('#stage image').getBoundingClientRect()
      return [r.left, r.top, r.width, r.height]
    })
    const { x, y, side } = await area(page)
    for (const [want, what] of [[[x - side / 2, y - side / 2, side, side], 'fitting the window'],
                                [[x - side, y - side, 2 * side, 2 * side], 'after the + button']]) {
      if (what !== 'fitting the window') await page.click('#in')
      const got = await box()
      if (got.some((v, i) => Math.abs(v - want[i]) > 0.5)) problem(`the stand-in PNG ${what}: ${got}, not ${want}`)
    }
    release()
    await ready(page, SMALL)
    const s1 = await state()
    const want1 = { image: [], curves: SMALL, enabled: SMALL, swatches: SMALL, turn: [false, colour('ink')], status: false }
    if (JSON.stringify(s1) !== JSON.stringify(want1)) problem(`once it has loaded: ${JSON.stringify(s1)}, not ${JSON.stringify(want1)}`)
    await page.unroute(`**/img/venn-${nn(SMALL)}.svg`)
  },

  async error(page, problem) {
    await page.goto(`${BASE}/view.html?n=4`)
    await page.waitForSelector('#error', { state: 'visible' })
    const got = await page.evaluate(() => ({ text: document.getElementById('error').textContent,
                                             status: getComputedStyle(document.getElementById('status')).display,
                                             swatches: document.querySelectorAll('#curves button').length,
                                             enabled: document.querySelectorAll('#curves button:enabled').length }))
    if (!got.text.includes('img/venn-04.svg') || !got.text.endsWith('(404)')) problem(`the error says "${got.text}"`)
    if (got.swatches !== 4 || got.enabled !== 0) problem(`${got.swatches} swatches, ${got.enabled} of them enabled`)
    if (got.status !== 'none') problem(`the loading line is still shown (display ${got.status})`)
    const pictures = await page.evaluate(() => document.querySelectorAll('#stage image').length)
    if (pictures) problem(`${pictures} broken pictures left in the drawing area`)
    for (const bad of ['abc', '', '10000000']) {
      await page.goto(`${BASE}/view.html?n=${bad}`)
      await page.waitForSelector('#error', { state: 'visible', timeout: 3000 })
        .catch(() => problem(`n=${bad}: no error shown within 3 seconds`))
      const swatches = await page.evaluate(() => document.querySelectorAll('#curves button').length)
      if (swatches) problem(`n=${bad}: ${swatches} swatches`)
    }
    // A drawing whose use 3 turns its curve a degree more than the file's own does: no curve lands on curve 3
    const { text } = await source(SMALL), use = text.match(/<use id="curve-3" [^\n]*\n/)[0]
    const turned = use.replace(/rotate\(([^ ]+)/, (_, deg) => `rotate(${Number(deg) + 1}`)
    await page.route(`**/img/venn-${nn(SMALL)}.svg`, route => route.fulfill({ status: 200, contentType: 'image/svg+xml', body: text.replace(use, turned) }))
    await page.goto(`${BASE}/view.html?n=${SMALL}`)
    await page.waitForSelector('#error', { state: 'visible', timeout: 60000 })
    const got2 = await page.evaluate(() => ({ text: document.getElementById('error').textContent,
                                              swatches: document.querySelectorAll('#curves button').length,
                                              enabled: document.querySelectorAll('#curves button:enabled').length }))
    const said = got2.text.match(/^Couldn't load (\S+) \((.+)\)$/)
    if (!said || said[1] !== `img/venn-${nn(SMALL)}.svg` || /[A-Za-z]/.test(said[2])) problem(`use 3 turned a degree more: the error says "${got2.text}"`)
    if (got2.swatches !== SMALL || got2.enabled) problem(`use 3 turned a degree more: ${got2.swatches} swatches, ${got2.enabled} of them enabled`)
    await page.unroute(`**/img/venn-${nn(SMALL)}.svg`)
    // A turn that fails, each way in a fresh load of the page: the worker unable to draw the view the turn asks for
    // (each view the page asks for once window.__spoil is set has inside null, which draw() can't read), and the turn's
    // animation cancelled while it turns (so that its finished promise rejects)
    await page.addInitScript(() => {
      const post = Worker.prototype.postMessage
      Worker.prototype.postMessage = function (data, ...rest) { return post.call(this, window.__spoil ? { ...data, inside: null } : data, ...rest) }
    })
    for (const [what, fail] of [['the worker unable to draw the turn\'s view', () => {
                                  window.__spoil = true
                                  document.getElementById('turn').click()
                                }],
                                ['the turn\'s animation cancelled', async () => {
                                  document.getElementById('turn').click()
                                  await new Promise(ok => requestAnimationFrame(ok))
                                  document.getElementById('region').getAnimations().forEach(a => a.cancel())
                                }]]) {
      await page.goto(`${BASE}/view.html?n=${SMALL}`, { waitUntil: 'commit' })
      await ready(page, SMALL)
      await page.waitForFunction(() => !document.getElementById('turn').disabled)
      await page.evaluate(fail)
      const text = await page.waitForSelector('#error', { state: 'visible', timeout: 10000 })
        .then(() => page.locator('#error').textContent(), () => null)
      if (!text?.startsWith(`Couldn't load img/venn-${nn(SMALL)}.svg (`)) problem(`a turn failing, ${what}: the error says ${JSON.stringify(text)}`)
    }
  },

  async phone(page, problem) {
    // Every n, each opened as the viewer draws it: as SVG paths, or on a canvas; on phones upright and on their side,
    // each with the least side the drawing may have there (0 for none)
    for (const [n, opened] of [...PATHS.map(n => [n, open]), ...CANVAS.map(n => [n, openCanvas])]) {
      for (const [w, h, least] of [[375, 667, 0], [320, 568, 0], [844, 390, 300], [568, 320, 0], [667, 375, 0]]) {
        const phone = await page.context().browser().newContext({ viewport: { width: w, height: h }, hasTouch: true })
        try {
          const p = await phone.newPage()
          p.setDefaultTimeout(10000)
          await p.route(/fonts\.(googleapis|gstatic)\.com/, r => r.abort())
          await opened(p, n)
          const boxes = await p.evaluate(() => ['#where', '#tools', '#curves'].map(sel => {
            const r = document.querySelector(sel).getBoundingClientRect()
            return [sel, r.left, r.top, r.right, r.bottom]
          }).concat([['scroll', 0, 0, document.documentElement.scrollWidth, document.documentElement.scrollHeight]]))
          for (const [sel, l, t, r, b] of boxes) {
            if (l < 0 || t < 0 || r > w || b > h) problem(`${w} wide, n=${n}: ${sel} spans (${l}, ${t}) to (${r}, ${b}), outside ${w} by ${h}`)
          }
          const controls = boxes.slice(0, 3)
          controls.forEach(([s1, l1, t1, r1, b1], i) => controls.slice(i + 1).forEach(([s2, l2, t2, r2, b2]) => {
            if (l1 < r2 && l2 < r1 && t1 < b2 && t2 < b1) problem(`${w} wide, n=${n}: ${s1} and ${s2} overlap`)
          }))
          // Apple's guideline for a touch target is 44 points: 44 CSS pixels. A checkbox's target is its label.
          const small = await p.evaluate(() => [...document.querySelectorAll('button, a, .stop label')].map(e => {
            const r = e.getBoundingClientRect()
            return [e.id || e.title || e.textContent, Math.round(r.width), Math.round(r.height)]
          }).filter(([, w, h]) => w < 44 || h < 44))
          if (small.length) problem(`${w} wide, n=${n}: on a touch screen these are under 44 by 44 pixels: ${JSON.stringify(small)}`)
          // The drawing's square page, fitted, lies in the window
          const [l, t, r, b] = await p.evaluate(() => {
            const m = document.querySelector('#stage svg').getScreenCTM()
            return [m.e, m.f, m.e + m.a * 51200, m.f + m.d * 51200]
          })
          if (l < -0.5 || t < -0.5 || r > w + 0.5 || b > h + 0.5) problem(`${w} by ${h}, n=${n}: the drawing's square spans (${l}, ${t}) to (${r}, ${b}), outside the window`)
          if (r - l < least) problem(`${w} by ${h}, n=${n}: the drawing fits in ${r - l} pixels, under ${least}`)
          // On a phone on its side, the swatches stand in a column (vertical writing: see view.html) along the right
          // edge, as near it as #curves's margin, 1rem at most
          const [mode, right] = await p.evaluate(() => [getComputedStyle(document.getElementById('curves')).writingMode,
                                                        document.getElementById('curves').getBoundingClientRect().right])
          if (w > h && (mode === 'horizontal-tb' || w - right > 16.5)) problem(`${w} by ${h}, n=${n}: the swatches in ${mode}, ending ${w - right} pixels from the right edge`)
          // A tapped button looks as it did: a touch screen's tap leaves no hover look behind
          const look = () => p.evaluate(() => getComputedStyle(document.getElementById('in')).borderTopColor)
          const was = await look()
          await p.tap('#in')
          await p.waitForTimeout(300)
          if (await look() !== was) problem(`${w} wide, n=${n}: after a tap, + has border ${await look()}, not ${was} as before`)
        } catch (e) {
          problem(`${w} by ${h}, n=${n}: ${e.name}: ${e.message.split('\n')[0]}`)
        } finally {
          await phone.close()   // even after a failure: one drawing of 23 in memory at a time
        }
      }
    }
  },

  async download(page, problem) {
    // Every n, each opened as the viewer draws it and left until its first drawing has been shown, by which time the
    // worker has the file, however it got it
    for (const [n, opened] of [...PATHS.map(n => [n, openShaded]), ...CANVAS.map(n => [n, openCanvas])]) {
      await (async () => {
        const from = served.length
        await opened(page, n)
        const got = served.slice(from).filter(p => p === `/img/venn-${nn(n)}.svg`).length
        if (got !== 1) problem(`n=${n}: img/venn-${nn(n)}.svg requested ${got} times`)
      })().catch(e => problem(`n=${n}: ${e.name}: ${e.message.split('\n')[0]}`))
    }
  },

  // ---- The shading (see probes())

  async shading(page, problem) {
    // n = 3, whose lines cover whole pixels (covered(), which must find some, wide = true); n = 7 and 13, whose lines
    // are too thin to. At 13 an outline() less exact than it is (with a tolerance of 4 pixels) showed furthest from the
    // curves: 1.8 pixels beyond a line's edge, 1.3 at 7
    for (const [n, labels, wide] of [[3, [0, 1, 2, 3, 4, 5, 6, 7], true], [SMALL, [0, 0b1, 0b110, 0b10101, 0b111111, 0b1111111], false],
                                     [13, [0], false]]) {
      await (async () => {
        assert(PATHS.includes(n), `n = ${n} is not among the n given: ${PATHS}`)
        await openShaded(page, n)
        const m = await mapping(page), ps = await probes(page, n, m, FINE), lines = await covered(page, n, m)
        if (wide && !lines.length) problem(`n=${n}: no pixel that a line covers wholly, at least ${FAR} pixels from every other curve`)
        for (const L of labels) {
          await check(page, n, L)
          await shows(page, ps, L, `n=${n}, curves ${curvesIn(L)} checked`, problem, lines)
        }
      })().catch(e => problem(`n=${n}: ${e.name}: ${e.message.split('\n')[0]}`))
    }
  },

  async checks(page, problem) {
    // While the drawing loads, and once it has: one checkbox per curve, unchecked, disabled until it has
    let release
    const gate = new Promise(ok => { release = ok })
    await page.route(`**/img/venn-${nn(SMALL)}.svg`, async route => { await gate; await route.continue() })
    await page.addInitScript(spy)
    await page.goto(`${BASE}/view.html?n=${SMALL}`, { waitUntil: 'commit' })
    await page.waitForSelector('#curves button')
    const state = () => page.evaluate(() => [...document.querySelectorAll('#curves input[type=checkbox]')].map(c => [c.checked, c.disabled]))
    for (const [disabled, what] of [[true, 'while the drawing loads'], [false, 'once it has arrived']]) {
      if (!disabled) {
        release()
        await ready(page, SMALL)
        await drawnSince(page, 0)
      }
      const got = JSON.stringify(await state()), want = JSON.stringify(Array(SMALL).fill([false, disabled]))
      if (got !== want) problem(`${what}, the checkboxes (checked, disabled) are ${got}, not ${want}`)
    }
    await page.unroute(`**/img/venn-${nn(SMALL)}.svg`)
    const names = [...(await page.locator('#curves').ariaSnapshot()).matchAll(/- checkbox "([^"]*)"/g)].map(m => m[1])
    if (names.length !== SMALL || new Set(names).size !== SMALL || names.some((s, i) => !new RegExp(`(^|\\D)${i + 1}(\\D|$)`).test(s)))
      problem(`the checkboxes' accessible names are ${JSON.stringify(names)}`)
    // Checkbox i beside swatch i, to its right (this window is landscape, so the swatches stand in a column), or, in
    // a portrait window, under it; centred on it either way, and nearer it than a swatch's side
    const placed = async (where, w, h) => {
      await page.setViewportSize({ width: w, height: h })
      await frames(page)
      const boxes = await page.evaluate(() => [...document.querySelectorAll('#curves button')].map((b, i) => {
        const s = b.getBoundingClientRect(), c = document.querySelectorAll('#curves input[type=checkbox]')[i]?.getBoundingClientRect()
        return [s.left, s.top, s.right, s.bottom, ...c ? [c.left, c.top, c.right, c.bottom] : []]
      }))
      boxes.forEach(([sl, st, sr, sb, cl, ct, cr, cb], i) => {
        const side = sb - st, [gap, off] = where === 'beside' ? [cl - sr, (ct + cb - st - sb) / 2] : [ct - sb, (cl + cr - sl - sr) / 2]
        if (!(gap >= 0 && gap < side && Math.abs(off) <= 1))
          problem(`in a ${w} by ${h} window, checkbox ${i} is at ${[cl, ct, cr, cb]}, not ${where} swatch ${i}, at ${[sl, st, sr, sb]}`)
      })
    }
    await placed('beside', W, H)
    // A click, another, and Space: each toggles a checkbox, and the shading follows, while the curves' SVG stays as it
    // is (a MutationObserver sees no attribute, child or descendant of it change)
    const ps = await probes(page, SMALL, await mapping(page))
    await page.evaluate(() => {
      const seen = window.__mutations = []
      new MutationObserver(records => seen.push(...records.map(r => `${r.type} of <${r.target.nodeName}> ${r.attributeName}`)))
        .observe(document.querySelector('#stage svg'), { attributes: true, childList: true, subtree: true })
    })
    for (const [act, L, what] of [[() => checkboxes(page).nth(0).click(), 0b1, 'a click on curve 0\'s checkbox'],
                                  [() => checkboxes(page).nth(3).click(), 0b1001, 'then one on curve 3\'s'],
                                  [async () => { await checkboxes(page).nth(0).focus(); await page.keyboard.press('Space') }, 0b1000, 'then Space on curve 0\'s']]) {
      await redrawn(page, act)
      const got = await checked(page)
      if (got !== L) problem(`after ${what}, curves ${curvesIn(got)} are checked, not ${curvesIn(L)}`)
      await shows(page, ps, L, `after ${what}`, problem)
    }
    const mutations = await page.evaluate(() => window.__mutations)
    if (mutations.length) problem(`the clicks and Space changed the curves' SVG ${mutations.length} times: ${mutations.slice(0, 3).join('; ')}`)
    // Hiding curves changes neither the checkboxes nor the shading: the third swatch hides curves 3 to 6, curve 3
    // checked; then the fit button, which has the shading drawn anew
    await page.locator('#curves button').nth(2).click()
    await redrawn(page, () => page.click('#fit'))
    const hid = await checked(page)
    if (hid !== 0b1000) problem(`after the third swatch hid curves 3 to 6, curves ${curvesIn(hid)} are checked, not ${curvesIn(0b1000)}`)
    await shows(page, ps, 0b1000, 'after the third swatch hid curves 3 to 6, and the fit button', problem)
    await placed('under', 600, 800)
    await page.setViewportSize({ width: W, height: H })
    // A phone with a touch screen: a tap toggles, and the target is 44 by 44 pixels or more
    const phone = await page.context().browser().newContext({ viewport: { width: 375, height: 667 }, hasTouch: true })
    try {
      const p = await phone.newPage()
      p.setDefaultTimeout(10000)
      await p.route(/fonts\.(googleapis|gstatic)\.com/, r => r.abort())
      await openShaded(p, SMALL)
      const ps2 = await probes(p, SMALL, await mapping(p))
      for (const [L, what] of [[0b1000000, 'a tap on curve 6\'s checkbox'], [0, 'a second tap']]) {
        await redrawn(p, () => checkboxes(p).nth(6).tap())
        const got = await checked(p)
        if (got !== L) problem(`375 by 667, touch screen: after ${what}, curves ${curvesIn(got)} are checked, not ${curvesIn(L)}`)
        await shows(p, ps2, L, `375 by 667, touch screen: after ${what}`, problem)
      }
      const small = await p.evaluate(() => [...document.querySelectorAll('#curves input[type=checkbox]')].map((c, i) => {
        const r = (c.labels[0] ?? c).getBoundingClientRect()
        return [i, Math.round(r.width), Math.round(r.height)]
      }).filter(([, w, h]) => w < 44 || h < 44))
      if (small.length) problem(`375 by 667, touch screen: these checkboxes' targets are under 44 by 44 pixels: ${JSON.stringify(small)}`)
    } finally {
      await phone.close()
    }
  },

  async slider(page, problem) {
    await open(page, SMALL)
    const m0 = await ctm(page)
    const centres = await page.evaluate(() => [...document.querySelectorAll('#curves button')].map(b => {
      const r = b.getBoundingClientRect()
      return [r.left + r.width / 2, r.top + r.height / 2]
    }))
    const at = async (k, what) => {   // curves 0 to k shown, exactly their swatches pressed
      const s = await page.evaluate(() => ({
        shown: [...document.querySelectorAll('#stage path')].map(p => getComputedStyle(p).display !== 'none'),
        pressed: [...document.querySelectorAll('#curves button')].map(b => b.getAttribute('aria-pressed') === 'true') }))
      const want = s.pressed.map((_, i) => i <= k)
      if (String(s.shown) !== String(want) || String(s.pressed) !== String(want))
        problem(`${what}: curves shown ${s.shown}, swatches pressed ${s.pressed}, not those up to curve ${k}`)
    }
    const past = (a, b) => [b[0] + 2 * (b[0] - a[0]), b[1] + 2 * (b[1] - a[1])]   // two swatches on from b, away from a
    // A mouse, from the first swatch to the fifth a swatch at a time, then past the last; from the third back past the first
    for (const [from, path, what] of [[0, [[1, 1], [2, 2], [3, 3], [4, 4], [past(centres[SMALL - 2], centres[SMALL - 1]), SMALL - 1]], 'dragging from the first swatch'],
                                      [2, [[1, 1], [0, 0], [past(centres[1], centres[0]), 0]], 'dragging from the third swatch']]) {
      await page.mouse.move(...centres[from])
      await page.mouse.down()
      await at(from, `${what}, pressed`)
      for (const [to, k] of path) {
        await page.mouse.move(...(Array.isArray(to) ? to : centres[to]), { steps: 4 })
        await at(k, `${what}, at ${Array.isArray(to) ? `(${to.map(Math.round)}), past an end` : `swatch ${to}`}`)
      }
      await page.mouse.up()
      await at(path.at(-1)[1], `${what}, released`)
      // The slide ends with the press: the mouse moving on unpressed, over a swatch or the drawing, changes nothing
      for (const [to, where] of [[centres[5], 'the sixth swatch'], [[W * 0.4, H * 0.5], 'the drawing']]) {
        await page.mouse.move(...to, { steps: 4 })
        await at(path.at(-1)[1], `${what}, released, then the mouse moved on unpressed over ${where}`)
      }
    }
    // A finger, from the second swatch to the fourth (synthetic touch pointers, as a phone sends them, at the swatch
    // pressed, which keeps the pointer)
    const touch = (events) => page.evaluate(events => {
      const b = document.querySelectorAll('#curves button')[1]
      for (const [type, [x, y], buttons] of events) b.dispatchEvent(new PointerEvent(type, { pointerId: 9, pointerType: 'touch',
        isPrimary: true, button: type === 'pointermove' ? -1 : 0, buttons, clientX: x, clientY: y, bubbles: true }))
    }, events)
    await touch([['pointerdown', centres[1], 1], ['pointermove', centres[2], 1]])
    await at(2, 'a finger dragged from the second swatch to the third')
    await touch([['pointermove', centres[3], 1], ['pointerup', centres[3], 0]])
    await at(3, 'then on to the fourth, and lifted')
    // Keys, each on a swatch focused first: the fourth, where the finger left the slider, then each the swatch the key
    // before moved the focus to; then, all shown, the third, not the last curve shown, from which a key doesn't move
    for (const [on, key, k] of [[3, 'ArrowRight', 4], [4, 'ArrowDown', 5], [5, 'ArrowLeft', 4], [4, 'ArrowUp', 3], [3, 'ArrowUp', 2],
                                [2, 'Home', 0], [0, 'End', SMALL - 1], [2, 'ArrowLeft', SMALL - 2]]) {
      await page.locator('#curves button').nth(on).focus()
      await page.keyboard.press(key)
      await at(k, `${key} on swatch ${on}`)
      const focus = await page.evaluate(() => [...document.querySelectorAll('#curves button')].indexOf(document.activeElement))
      if (focus !== k) problem(`after ${key} on swatch ${on}, the focus is on swatch ${focus}, not ${k}`)
    }
    holds(problem, await ctm(page), [m0.e, m0.f], [0, 0], m0.a, 'after dragging along the swatches and pressing keys on them')
  },

  async turn(page, problem) {
    await page.addInitScript(holdable)
    for (const [n, L0] of [[3, 0b1], [SMALL, 0b101]]) {
      await (async () => {
        await openShaded(page, n)
        await faced(page, n, problem)
        const { angles, side } = await shape(n), lands = landing(angles)
        stated(lands, n, problem)
        const m = await mapping(page), ps = await probes(page, n, m)
        const curves = () => page.evaluate(() => [...document.querySelectorAll('#stage path')].map(p => [p.getAttribute('d'), p.getAttribute('stroke')]))
        const before = await curves(), centre = [(side / 2 - m.x) / m.s, (side / 2 - m.y) / m.s]
        const click = () => page.evaluate(() => document.getElementById('turn').click())
        // Enter on the button, focused, then again; a click, and another a frame later, while the first turn spins;
        // with every curve checked, a click. Each: what it is, how many turns it makes, whether the button is to keep
        // the focus throughout, the act itself, and the label to check before it, given the label the act before left
        let L = L0
        await check(page, n, L)
        await page.focus('#turn')
        for (const [what, k, keys, act, start] of [['Enter on the turn button', 1, true, () => page.keyboard.press('Enter'), L => L],
                                                   ['Enter on it again', 1, true, () => page.keyboard.press('Enter'), L => L],
                                                   ['a click and another while it turns', 2, false, () => page.evaluate(async () => {
                                                     const button = document.getElementById('turn')
                                                     button.click()
                                                     await new Promise(ok => requestAnimationFrame(ok))
                                                     button.click()
                                                   }), L => L],
                                                   ['a click with every curve checked', 1, false, click, () => 2 ** n - 1]]) {
          L = start(L)
          await check(page, n, L)   // which does nothing when L is checked already
          const labels = [L]
          for (let j = 0; j < k; j++) labels.push(landed(labels[j], lands))
          turnedWell(await turns(page, k, act), n, centre, labels, keys, `n=${n}, ${what}`, problem)
          L = labels[k]
          const got = await checked(page)
          if (got !== L) problem(`n=${n}, after ${what}: curves ${curvesIn(got)} checked, not ${curvesIn(L)}`)
          await shows(page, ps, L, `n=${n}, after ${what}`, problem)
        }
        // The race shade()'s numbers guard against: a drawing asked for before a turn's arriving after the turn has
        // asked for its own. With L0 checked again, every message from the worker held back (holdable()) from a resize
        // event on, which has the page draw anew; the turn button clicked once that drawing has come; and it delivered
        // once the turn has asked for its own. #region stays turned until the turn's own drawing is shown.
        await check(page, n, L0)
        await page.evaluate(() => {
          window.__held = []
          dispatchEvent(new Event('resize'))
        })
        await page.waitForFunction(() => window.__held.length === 1)
        const asked = await page.evaluate(() => window.__seen.asked.length)
        await click()
        await page.waitForFunction(k => window.__seen.asked.length > k, asked)
        const angle = await page.evaluate(async () => {
          window.__held.shift()()
          await new Promise(ok => requestAnimationFrame(ok))
          const m = new DOMMatrix(getComputedStyle(document.getElementById('region')).transform)
          return Math.atan2(m.b, m.a) * 180 / Math.PI
        })
        if (!(Math.abs(angle + 360 / n) <= 1e-3))
          problem(`n=${n}, a drawing asked for before a turn's, arriving after the turn asked for its own: #region turned by ${angle.toFixed(4)} degrees, not ${(-360 / n).toFixed(4)}`)
        await page.evaluate(() => {
          const held = window.__held
          window.__held = null
          held.forEach(deliver => deliver())
        })
        await page.waitForFunction(() => getComputedStyle(document.getElementById('region')).transform === 'none')
        L = landed(L0, lands)
        const got = await checked(page)
        if (got !== L) problem(`n=${n}, after the turn with a drawing held back: curves ${curvesIn(got)} checked, not ${curvesIn(L)}`)
        await shows(page, ps, L, `n=${n}, after the turn with a drawing held back`, problem)
        if (JSON.stringify(await curves()) !== JSON.stringify(before)) problem(`n=${n}: the curves' paths or colours changed in the turns`)
        holds(problem, await ctm(page), [m.x, m.y].map(v => -v / m.s), [0, 0], 1 / m.s, `n=${n}, after the turns`)
      })().catch(e => problem(`n=${n}: ${e.name}: ${e.message.split('\n')[0]}`))
    }
  },

  async follow(page, problem) {
    await openShaded(page, SMALL)
    await check(page, SMALL, 0b101)
    const p = (await probes(page, SMALL, await mapping(page))).find(q => q.label === 0b101)
    if (!p) throw new Error('no probe of label 5 at fit')
    // The gestures of settle, about p: a drag from it, then the wheel and a pinch where the drag left it, which keep
    // it there. At every event, how far the shading's canvas is from where the picture's transform puts the box it had.
    const [x, y] = [p.x + 0.5 + 75, p.y + 0.5 + 45], t = await now(page)   // where the drag leaves p
    const off = await page.evaluate(async ([x, y]) => {
      const stage = document.getElementById('stage'), shade = document.querySelector('#region canvas')
      const ptr = (type, id, x, y, buttons, pointerType) => stage.dispatchEvent(new PointerEvent(type,
        { pointerId: id, pointerType, isPrimary: id === 1, button: 0, buttons, clientX: x, clientY: y, bubbles: true }))
      const wait = ms => new Promise(ok => setTimeout(ok, ms))
      const box = () => { const b = shade.getBoundingClientRect(); return [b.left, b.top, b.width, b.height] }
      const B0 = box(), off = []
      const track = () => {
        const m = new DOMMatrix(getComputedStyle(document.getElementById('picture')).transform)
        off.push(Math.max(...[m.a * B0[0] + m.e, m.d * B0[1] + m.f, m.a * B0[2], m.d * B0[3]].map((v, i) => Math.abs(v - box()[i]))))
      }
      ptr('pointerdown', 1, x - 75, y - 45, 1, 'mouse')
      for (let i = 1; i <= 15; i++) { ptr('pointermove', 1, x - 75 + 5 * i, y - 45 + 3 * i, 1, 'mouse'); track(); await wait(16) }
      ptr('pointerup', 1, x, y, 0, 'mouse')
      for (let i = 0; i < 10; i++) {
        dispatchEvent(new WheelEvent('wheel', { deltaY: -40, clientX: x, clientY: y, bubbles: true, cancelable: true }))
        track(); await wait(16)
      }
      ptr('pointerdown', 1, x, y, 1, 'touch'); ptr('pointerdown', 2, x + 60, y, 1, 'touch')
      for (let i = 1; i <= 10; i++) { ptr('pointermove', 2, x + 60 + 6 * i, y, 1, 'touch'); track(); await wait(16) }
      ptr('pointerup', 2, x + 120, y, 0, 'touch'); ptr('pointerup', 1, x, y, 0, 'touch')
      // Then until the new drawing arrives, drawn anew SETTLE ms after the gestures, how far the old one moves from
      // where the gestures left it: every 5 ms, and as the curves are drawn anew (#picture's transform set back to
      // the identity), seen by a MutationObserver, whose callback runs before the worker's next message can (in
      // Chromium the new shading arrived within 5 ms)
      const B1 = box(), seen = window.__seen, t1 = performance.now()
      let pending = 0
      const picture = document.getElementById('picture'), gap = () => Math.max(...box().map((v, i) => Math.abs(v - B1[i])))
      const observer = new MutationObserver(() => {
        if (getComputedStyle(picture).transform === 'matrix(1, 0, 0, 1, 0, 0)') pending = Math.max(pending, gap())
      })
      observer.observe(picture, { attributes: true, attributeFilter: ['style'] })
      while (!(seen.asked.some(t => t > t1) && seen.shown.at(-1) > seen.asked.at(-1)) && performance.now() - t1 < 60000) {
        pending = Math.max(pending, gap())
        await wait(5)
      }
      observer.disconnect()
      return [Math.max(...off), pending]
    }, [x, y])
    if (!(off[0] <= 0.5)) problem(`during the gestures the shading's canvas was up to ${off[0].toFixed(1)} pixels from where the picture's transform put it`)
    if (!(off[1] <= 0.5)) problem(`waiting for the shading drawn anew, the old one moved up to ${off[1].toFixed(1)} pixels from where the gestures left it`)
    await drawnSince(page, t)
    await shows(page, await probes(page, SMALL, await mapping(page)), 0b101, 'drawn anew after the gestures', problem)
    await redrawn(page, () => page.mouse.dblclick(x, y))
    await shows(page, await probes(page, SMALL, await mapping(page)), 0b101, 'drawn anew after a double-click', problem)
  },

  // ---- The canvas (CANVAS); see spy() and compare()

  async canvasFit(page, problem) {
    for (const n of CANVAS) {
      const { page: side } = await drawing(n), { knots } = await source(n)
      await openCanvas(page, n)
      const fit = fitted(await area(page), side)
      await matches(page, n, fit, n - 1, `n=${n} at fit`, problem)
      // Zoom about a point on curve 0, to the pixel (browsers report a wheel's position in whole pixels)
      const s = knots[1].map((v, i) => Math.round((v - [fit.x, fit.y][i]) / fit.s))
      let m = fit
      for (const f of [4, 16, 1000 / 64]) {
        const t = await now(page)
        await page.evaluate(([x, y, deltaY]) => document.getElementById('stage').dispatchEvent(
          new WheelEvent('wheel', { deltaY, clientX: x, clientY: y, bubbles: true, cancelable: true })), [...s, -400 * Math.log(f)])
        m = zoomed(m, fit, s, f)
        await drawnSince(page, t)
        await matches(page, n, m, n - 1, `n=${n} zoomed in by ${(fit.s / m.s).toPrecision(4)} about ${s}`, problem)
      }
      await page.goto('about:blank')   // one drawing of 23 in memory at a time
      const p = await sized(page, W, H, 2)
      try {
        await openCanvas(p, n)
        await matches(p, n, fitted(await area(p), side), n - 1, `n=${n} at fit, 2 device pixels to a CSS pixel`, problem)
      } finally {
        await p.context().close()   // even after a failure: one drawing of 23 in memory at a time
      }
    }
  },

  async canvasCurves(page, problem) {
    for (const n of CANVAS) {
      const { page: side } = await drawing(n), { colours } = await source(n)
      await openCanvas(page, n)
      const fit = fitted(await area(page), side)
      const swatches = await page.evaluate(() => [...document.querySelectorAll('#curves button')].map(b => getComputedStyle(b).backgroundColor))
      if (String(swatches) !== String(colours.map(rgb))) problem(`n=${n}: swatches ${swatches}, not the curves' ${colours}`)
      for (const [act, k, what] of [[() => page.locator('#curves button').nth(0).click(), 0, 'clicking the first swatch'],
                                    [() => page.locator('#curves button').nth(2).click(), 2, 'clicking the third swatch'],
                                    [() => page.keyboard.press('Escape'), n - 1, 'pressing Escape']]) {
        const t = await now(page)
        await act()
        await drawnSince(page, t)
        await matches(page, n, fit, k, `n=${n}, after ${what}`, problem)
        const pressed = await page.evaluate(() => [...document.querySelectorAll('#curves button')].map(b => b.getAttribute('aria-pressed') === 'true'))
        const want = pressed.map((_, i) => i <= k)
        if (String(pressed) !== String(want)) problem(`n=${n}, after ${what}: swatches pressed ${pressed}, not ${want}`)
      }
    }
  },

  async canvasSettle(page, problem) {
    for (const n of CANVAS) {
      const { page: side } = await drawing(n), { knots } = await source(n)
      await openCanvas(page, n)
      const fit = fitted(await area(page), side)
      // A drag, a run of wheel turns and a two-finger pinch as a hand makes them, an event every 16 ms, as in settle,
      // starting from a point on curve 0, (x, y), so that the view they end in shows curves. At every event, how far the
      // canvases' boxes on the screen (the curves' and the shading's) are from where the picture's transform puts the
      // boxes they had before (off); after the last, how far they move from there until the new drawing arrives (pending)
      const [x, y] = knots[1].map((v, i) => Math.round((v - [fit.x, fit.y][i]) / fit.s))
      const r = await page.evaluate(async ([x, y]) => {
        const stage = document.getElementById('stage'), picture = () => getComputedStyle(document.getElementById('picture')).transform
        const ptr = (type, id, x, y, buttons, pointerType) => stage.dispatchEvent(new PointerEvent(type,
          { pointerId: id, pointerType, isPrimary: id === 1, button: 0, buttons, clientX: x, clientY: y, bubbles: true }))
        const wait = ms => new Promise(ok => setTimeout(ok, ms))
        const box = () => [...document.querySelectorAll('#stage canvas')].flatMap(c => {
          const b = c.getBoundingClientRect()
          return [b.left, b.top, b.width, b.height]
        })
        const B0 = box(), off = []
        const at = (B, m) => B.map((v, i) => [m.a * v + m.e, m.d * v + m.f, m.a * v, m.d * v][i % 4])
        const gap = (b, c) => Math.max(...b.map((v, i) => Math.abs(v - c[i])))
        const track = () => off.push(gap(box(), at(B0, new DOMMatrix(picture()))))
        const before = picture(), during = [], t0 = performance.now()
        ptr('pointerdown', 1, x, y, 1, 'mouse')
        for (let i = 1; i <= 15; i++) { ptr('pointermove', 1, x + 5 * i, y + 3 * i, 1, 'mouse'); during.push(picture()); track(); await wait(16) }
        ptr('pointerup', 1, x + 75, y + 45, 0, 'mouse')
        for (let i = 0; i < 10; i++) {
          dispatchEvent(new WheelEvent('wheel', { deltaY: -40, clientX: x + 75, clientY: y + 45, bubbles: true, cancelable: true }))
          during.push(picture()); track(); await wait(16)
        }
        ptr('pointerdown', 1, x + 75, y + 45, 1, 'touch'); ptr('pointerdown', 2, x + 135, y + 45, 1, 'touch')
        for (let i = 1; i <= 10; i++) { ptr('pointermove', 2, x + 135 + 6 * i, y + 45, 1, 'touch'); during.push(picture()); track(); await wait(16) }
        ptr('pointerup', 2, x + 195, y + 45, 0, 'touch'); ptr('pointerup', 1, x + 75, y + 45, 0, 'touch')
        const t1 = performance.now(), moved = picture(), seen = window.__seen, B1 = box()
        const meanwhile = list => list.filter(t => t >= t0 && t <= t1).length
        let pending = 0
        while (!seen.asked.some(t => t > t1) && performance.now() - t1 < 2000) await wait(10)
        while (!(seen.shown.at(-1) > seen.asked.at(-1)) && performance.now() - t1 < 60000) {
          pending = Math.max(pending, gap(box(), B1))
          await wait(10)
        }
        return { before, during, moved, t1, off: Math.max(...off), pending, asked: seen.asked.find(t => t > t1) - t1,
                 meanwhile: [meanwhile(seen.asked), meanwhile(seen.shown), meanwhile(seen.drawn)] }
      }, [x, y])
      const IDENTITY = 'matrix(1, 0, 0, 1, 0, 0)'
      if (r.before !== IDENTITY) problem(`n=${n}: drawn, the picture's transform is ${r.before}, not the identity`)
      if (String(r.meanwhile) !== '0,0,0') problem(`n=${n}: during the gestures the page asked its worker ${r.meanwhile[0]} times, showed ${r.meanwhile[1]} new drawings and drew on or resized a canvas ${r.meanwhile[2]} times`)
      const unmoved = r.during.filter(t => t === IDENTITY).length
      if (unmoved) problem(`n=${n}: the picture not moved by a transform in ${unmoved} of the 35 events`)
      if (!(r.off <= 0.5)) problem(`n=${n}: during the gestures the canvas was up to ${r.off.toFixed(1)} pixels from where the picture's transform put the drawing`)
      if (!(r.pending <= 0.5)) problem(`n=${n}: waiting for the new drawing, the old one moved up to ${r.pending.toFixed(1)} pixels from where the gestures left it`)
      if (!(r.asked <= 2000)) problem(`n=${n}: no new drawing asked for within 2 seconds of the gestures ending`)
      await drawnSince(page, r.t1)
      // Where the moved picture showed the drawing: the fit, under the picture's transform matrix(k, 0, 0, k, tx, ty)
      const [k, , , , tx, ty] = r.moved.slice(7, -1).split(',').map(Number)
      await matches(page, n, { s: fit.s / k, x: fit.x - tx * fit.s / k, y: fit.y - ty * fit.s / k }, n - 1, `n=${n}, drawn anew after the gestures`, problem)
      const after = await page.evaluate(() => getComputedStyle(document.getElementById('picture')).transform)
      if (after !== IDENTITY) problem(`n=${n}: once drawn anew, the picture's transform is ${after}, not the identity`)
      // A drawing asked for before a drag and arriving during it: curve 0 alone, then all of them (Escape), then a drag
      // at once, a move every 16 ms, until 10 moves after the drawing arrives. At every move, how far the canvases (the
      // curves' and the shading's) are from where the picture's transform puts the drawings
      const t2 = await now(page)
      await page.click('#curves button')
      await drawnSince(page, t2)
      const a = await page.evaluate(async ([x, y]) => {
        const stage = document.getElementById('stage'), wait = ms => new Promise(ok => setTimeout(ok, ms))
        const ptr = (type, x, y, buttons) => stage.dispatchEvent(new PointerEvent(type,
          { pointerId: 1, pointerType: 'mouse', isPrimary: true, button: 0, buttons, clientX: x, clientY: y, bubbles: true }))
        const box = () => [...document.querySelectorAll('#stage canvas')].flatMap(c => {
          const b = c.getBoundingClientRect()
          return [b.left, b.top, b.width, b.height]
        })
        const B0 = box(), seen = window.__seen, off = []
        dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }))
        const t = performance.now()
        ptr('pointerdown', x, y, 1)
        let i = 0, after = 0
        while (after < 10 && performance.now() - t < 60000) {
          i++
          ptr('pointermove', x + (i % 200), y + (i % 120) / 2, 1)
          const m = new DOMMatrix(getComputedStyle(document.getElementById('picture')).transform), b = box()
          if (seen.shown.at(-1) > t) {
            after++
            off.push(Math.max(...B0.map((v, j) => Math.abs([m.a * v + m.e, m.d * v + m.f, m.a * v, m.d * v][j % 4] - b[j]))))
          }
          await wait(16)
        }
        ptr('pointerup', x, y, 0)
        return { after, off: Math.max(...off) }
      }, [x, y])
      if (a.after < 10) problem(`n=${n}: the drawing asked for before the drag didn't arrive during it`)
      else if (!(a.off <= 0.5)) problem(`n=${n}: a drawing arriving during a drag was up to ${a.off.toFixed(1)} pixels from where the picture's transform put it`)
    }
  },

  async canvasResize(page, problem) {
    for (const n of CANVAS) {
      const { page: side } = await drawing(n)
      await page.addInitScript(() => {   // keep the page's resolution media queries, to tell them of a change below
        const matchMedia = window.matchMedia.bind(window)
        window.__resolution = []
        window.matchMedia = q => {
          const m = matchMedia(q)
          if (q.includes('resolution')) window.__resolution.push(m)
          return m
        }
      })
      await openCanvas(page, n)
      const t = await now(page)
      await page.setViewportSize({ width: 1400, height: 900 })
      await drawnSince(page, t)
      await matches(page, n, fitted(await area(page), side), n - 1, `n=${n}, after a resize to 1400 by 900`, problem)
      // A new devicePixelRatio with no resize, as when the window moves to another screen: only Chromium lets a page's
      // be changed, through the DevTools protocol, and then it doesn't send the change event a browser sends the
      // resolution media queries when that happens, so this sends it
      if (page.context().browser().browserType().name() === 'chromium') {
        const cdp = await page.context().newCDPSession(page), t2 = await now(page)
        await cdp.send('Emulation.setDeviceMetricsOverride', { width: 1400, height: 900, deviceScaleFactor: 2, mobile: false })
        await page.evaluate(() => window.__resolution.at(-1)?.dispatchEvent(new Event('change')))
        await drawnSince(page, t2, 60000)
        await matches(page, n, fitted(await area(page), side), n - 1, `n=${n}, after a change to 2 device pixels to a CSS pixel`, problem)
      }
    }
  },

  async canvasLoading(page, problem) {
    for (const n of CANVAS) {
      const { page: side } = await drawing(n)
      let release
      const gate = new Promise(ok => { release = ok })
      await page.route(`**/img/venn-${nn(n)}.svg`, async route => { await gate; await route.continue() })
      await page.addInitScript(spy)
      await page.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
      await page.waitForSelector('#stage canvas', { state: 'attached', timeout: 5000 })
      await page.waitForSelector('#curves button')
      const state = async () => ({ ...(await page.evaluate(() => ({
        image: [...document.querySelectorAll('#stage image')].map(i => i.getAttribute('href')),
        enabled: document.querySelectorAll('#curves button:enabled').length,
        swatches: document.querySelectorAll('#curves button').length,
        shown: window.__seen.shown.length }))),
        status: await page.locator('#status').isVisible() })
      const s0 = await state()
      const want0 = { image: [`img/venn-${nn(n)}.png`], enabled: 0, swatches: n, shown: 0, status: true }
      if (JSON.stringify(s0) !== JSON.stringify(want0)) problem(`n=${n}, while the SVG loads: ${JSON.stringify(s0)}, not ${JSON.stringify(want0)}`)
      const box = () => page.evaluate(() => {
        const r = document.querySelector('#stage image')?.getBoundingClientRect() ?? {}
        return [r.left, r.top, r.width, r.height]
      })
      const a = await area(page), { x, y, side: px } = a, t = await now(page)
      for (const [want, what] of [[[x - px / 2, y - px / 2, px, px], 'fitting the window'],
                                  [[x - px, y - px, 2 * px, 2 * px], 'after the + button']]) {
        if (what !== 'fitting the window') await page.click('#in')
        const got = await box()
        if (!got.every((v, i) => Math.abs(v - want[i]) <= 0.5)) problem(`n=${n}: the stand-in PNG ${what}: ${got}, not ${want}`)
      }
      release()
      await drawnSince(page, t)
      await page.waitForFunction(n => document.querySelectorAll('#curves button:enabled').length === n, n)
      const s1 = await state()
      const want1 = { image: [], enabled: n, swatches: n, shown: s1.shown, status: false }
      if (JSON.stringify(s1) !== JSON.stringify(want1)) problem(`n=${n}, once drawn: ${JSON.stringify(s1)}, not ${JSON.stringify(want1)}`)
      const fit = fitted(a, side)
      await matches(page, n, zoomed(fit, fit, [a.x, a.y], 2), n - 1, `n=${n}, drawn after the + button`, problem)
      await page.unroute(`**/img/venn-${nn(n)}.svg`)
    }
  },

  async canvasError(page, problem) {
    for (const n of CANVAS) {
      // A small drawing in venn.py's format: the file's own, with curve 0 cut to its first span and one back to its start
      const { text } = await source(n), d = text.indexOf(' d="') + 4, z = text.indexOf(' Z"', d)
      const span = text.slice(d, text.indexOf(' C', text.indexOf(' C', d) + 1))   // "Mx0,y0 Cx,y x,y x1,y1"
      const start = span.slice(1, span.indexOf(' ')), end = span.slice(span.lastIndexOf(' ') + 1)
      const small = `${text.slice(0, d)}${span} C${end} ${start} ${start}${text.slice(z)}`
      const use = i => small.match(new RegExp(`<use id="curve-${i}" [^\\n]*\\n`))[0]
      const broken = [
        ['an angle of NaN', small.replace(use(5), use(5).replace(/rotate\([^ ]+/, 'rotate(NaN'))],
        ['a stroke-width of Infinity', small.replace(use(0), use(0).replace(/stroke-width="[^"]+"/, 'stroke-width="Infinity"'))],
        ['a 24th use', small.replace('</svg>', use(n - 1).replace(`curve-${n - 1}`, `curve-${n}`) + '</svg>')],
        ['the last use gone', small.replace(use(n - 1), '')],
        ['another viewBox', small.replace(/viewBox="0 0 (\d+) \d+"/, 'viewBox="0 0 $1 1"')],
        ['an L command', small.replace(`C${end} ${start}`, `L${end} ${start}`)],
        ['a use of another href', small.replace(use(3), use(3).replace('href="#curve"', 'href="#other"'))],
        ['cut short', small.slice(0, d + span.length / 2)],
      ]
      broken.filter(([, body]) => body === small).forEach(([what]) => problem(`n=${n}: ${what}: nothing changed`))
      // Each error shown, none left uncaught: the errors and rejections no code caught, as each engine reports a
      // worker's (Chromium as a page error, WebKit as "Unhandled Promise Rejection", Firefox as "JavaScript Error")
      const uncaught = []
      page.on('pageerror', e => uncaught.push(e.message))
      page.on('console', m => { if (m.type() === 'error' && /Uncaught|Unhandled|JavaScript Error/.test(m.text())) uncaught.push(m.text()) })
      let body = small
      await page.route(`**/img/venn-${nn(n)}.svg`, route => route.fulfill(
        body === null ? { status: 404, body: '' } : { status: 200, contentType: 'image/svg+xml', body }))
      await page.addInitScript(spy)
      await page.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
      await page.waitForSelector('#stage canvas', { state: 'attached', timeout: 5000 })
      await drawnSince(page, 0, 30000).catch(() => problem(`n=${n}, the small drawing: not drawn within 30 seconds`))
      if (await page.locator('#error').isVisible()) problem(`n=${n}, the small drawing: ${await page.locator('#error').textContent()}`)
      for (const [what, b] of [['404', null], ...broken]) {
        body = b
        await page.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
        await page.waitForSelector('#error', { state: 'visible', timeout: 30000 })
        const got = await page.evaluate(() => ({ text: document.getElementById('error').textContent,
                                                 status: getComputedStyle(document.getElementById('status')).display,
                                                 swatches: document.querySelectorAll('#curves button').length,
                                                 enabled: document.querySelectorAll('#curves button:enabled').length,
                                                 shown: window.__seen.shown.length,
                                                 image: [...document.querySelectorAll('#stage image')].map(i => i.getAttribute('href')) }))
        const said = got.text.match(/^Couldn't load (\S+) \((.+)\)$/)
        if (!said || said[1] !== `img/venn-${nn(n)}.svg` || (body === null && said[2] !== '404')) problem(`n=${n}, ${what}: the error says "${got.text}"`)
        if (got.status !== 'none') problem(`n=${n}, ${what}: the loading line is still shown (display ${got.status})`)
        if (got.swatches !== n || got.enabled !== 0) problem(`n=${n}, ${what}: ${got.swatches} swatches, ${got.enabled} of them enabled`)
        if (got.shown) problem(`n=${n}, ${what}: ${got.shown} drawings shown`)
        if (String(got.image) !== `img/venn-${nn(n)}.png`) problem(`n=${n}, ${what}: the picture is ${got.image}, not the PNG`)
      }
      if (uncaught.length) problem(`n=${n}: ${uncaught.length} errors left uncaught besides those shown, e.g. ${uncaught[0].slice(0, 200)}`)
      await page.unroute(`**/img/venn-${nn(n)}.svg`)
      // The viewer's own failures, each with the real file: no Worker to be had, canvas.js not found, and the worker
      // failing after the first drawing (an error event 100 ms after it). Each must show the error, saying what failed.
      const failures = [
        ['no Worker', 'no workers here', p => p.addInitScript(() => {
          window.Worker = function () { throw new Error('no workers here') }
        })],
        ['canvas.js not found', 'canvas.js', p => p.route(/\/canvas\.js/, r => r.fulfill({ status: 404, body: '' }))],
        ['a failure after the first drawing', 'a later failure', p => p.addInitScript(() => {
          const W = window.Worker
          window.Worker = class extends W {
            constructor(...args) {
              super(...args)
              let seen = 0
              this.addEventListener('message', () => {
                seen += 1
                if (seen === 1) setTimeout(() => this.dispatchEvent(new ErrorEvent('error', { message: 'a later failure' })), 100)
              })
            }
          }
        })],
      ]
      for (const [what, want, setup] of failures) {
        const p = await sized(page, W, H, 1)
        await setup(p)
        await p.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
        const text = await p.waitForSelector('#error', { state: 'visible', timeout: 60000 })
          .then(() => p.locator('#error').textContent(), () => null)
        if (!text?.startsWith(`Couldn't load img/venn-${nn(n)}.svg (`) || !text.includes(want) || text.includes('undefined'))
          problem(`n=${n}, ${what}: the error says ${JSON.stringify(text)}, not that it couldn't load img/venn-${nn(n)}.svg (${want}..., nothing undefined)`)
        await p.context().close()
      }
    }
  },

  async canvasFrames(page, problem) {
    for (const n of CANVAS) {
      const p = await sized(page, 2560, 1440, 2)
      try {
        await openCanvas(p, n)
        const t0 = await now(p)
        for (let i = 0; i < 3; i++) {
          const t = await now(p)
          await p.click('#in')
          await drawnSince(p, t)
        }
        await p.waitForTimeout(1000)
        const [at, longest] = await p.evaluate(t0 => {
          const f = window.__seen.frames.filter(t => t > t0)
          return f.slice(1).map((t, i) => [t, t - f[i]]).reduce((worst, gap) => gap[1] > worst[1] ? gap : worst, [0, 0])
        }, t0)
        if (longest > 100) problem(`n=${n}: a frame of ${longest.toFixed(0)} ms, ending ${(at - t0).toFixed(0)} ms after the first click`)
      } finally {
        await p.context().close()
      }
    }
  },

  async canvasBig(page, problem) {
    const LIMIT = 20000                   // ms from opening to the first drawing (see qual_viewer_canvas_big)
    for (const n of CANVAS) {
      const { page: side } = await drawing(n)
      const p = await sized(page, 2560, 1440, 2)
      try {
        await p.addInitScript(spy)
        await p.goto(`${BASE}/view.html?n=${n}`, { waitUntil: 'commit' })
        await p.waitForSelector('#stage canvas', { state: 'attached', timeout: 5000 })
        const first = await drawnSince(p, 0, LIMIT).then(() => p.evaluate(() => window.__seen.shown[0]), () => Infinity)
        if (first > LIMIT) problem(`n=${n}: the first drawing took ${first.toFixed(0)} ms, over ${LIMIT}`)
        await matches(p, n, fitted(await area(p), side), n - 1, `n=${n} at fit in 2560 by 1440, 2 device pixels to a CSS pixel`, problem)
      } finally {
        await p.context().close()
      }
    }
  },

  async canvasShading(page, problem) {
    for (const n of CANVAS) {
      const { side } = await shape(n), { knots } = await source(n)
      await openCanvas(page, n)
      const fit = fitted(await area(page), side)
      // Expect the drawing at mapping m, with label L shaded
      const look = async (m, L, what) => {
        await shows(page, await probes(page, n, m), L, `n=${n}, ${what}`, problem)
        await matches(page, n, m, n - 1, `n=${n}, ${what}`, problem)
      }
      // Wait for the drawing of whatever act() changes, then look()
      const after = async (act, m, L, what) => {
        const t = await now(page)
        await act()
        await drawnSince(page, t)
        await look(m, L, what)
      }
      await look(fit, 0, 'at fit, nothing checked')
      await after(() => check(page, n, 2 ** n - 1), fit, 2 ** n - 1, 'at fit, all checked')
      // Zoomed in by 64 about a point on curve 0, to the pixel (browsers report a wheel's position in whole pixels)
      const s = knots[1].map((v, i) => Math.round((v - [fit.x, fit.y][i]) / fit.s)), m = zoomed(fit, fit, s, 64)
      let t = await now(page)
      await page.evaluate(([x, y, deltaY]) => document.getElementById('stage').dispatchEvent(
        new WheelEvent('wheel', { deltaY, clientX: x, clientY: y, bubbles: true, cancelable: true })), [...s, -400 * Math.log(64)])
      await drawnSince(page, t)
      const L = commonest(await probes(page, n, m))
      await after(() => check(page, n, L), m, L, `zoomed in by 64 about (${s}), curves ${curvesIn(L)} checked`)
      await after(async () => {
        await page.mouse.move(...s)
        await page.mouse.down()
        await page.mouse.move(s[0] - 100, s[1], { steps: 5 })
        await page.mouse.up()
      }, { ...m, x: m.x + 100 * m.s }, L, `then dragged 100 pixels left`)
    }
  },

  async canvasTurn(page, problem) {
    for (const n of CANVAS) {
      const { side, angles } = await shape(n), { knots } = await source(n), lands = landing(angles)
      stated(lands, n, problem)
      await openCanvas(page, n)
      const fit = fitted(await area(page), side)
      const s = knots[1].map((v, i) => Math.round((v - [fit.x, fit.y][i]) / fit.s)), m = zoomed(fit, fit, s, 64)
      let t = await now(page)
      await page.evaluate(([x, y, deltaY]) => document.getElementById('stage').dispatchEvent(
        new WheelEvent('wheel', { deltaY, clientX: x, clientY: y, bubbles: true, cancelable: true })), [...s, -400 * Math.log(64)])
      await drawnSince(page, t)
      const L = commonest(await probes(page, n, m))
      t = await now(page)
      await check(page, n, L)
      await drawnSince(page, t)
      await faced(page, n, problem)
      const L2 = landed(L, lands), log = await turns(page, 1, () => page.evaluate(() => document.getElementById('turn').click()))
      turnedWell(log, n, [(side / 2 - m.x) / m.s, (side / 2 - m.y) / m.s], [L, L2], false, `n=${n}, zoomed in by 64 about (${s})`, problem)
      const got = await checked(page)
      if (got !== L2) problem(`n=${n}: after the turn, curves ${curvesIn(got)} checked, not ${curvesIn(L2)}`)
      // Drag P, the page point at s, turned by -360/n about the centre, to where P was: synthetic pointers, since the
      // drag may be longer than the window (where Playwright's Firefox drops mouse events)
      const a = -2 * Math.PI / n, [px, py] = [m.x + s[0] * m.s, m.y + s[1] * m.s], mid = side / 2
      const q = [mid + (px - mid) * Math.cos(a) - (py - mid) * Math.sin(a), mid + (px - mid) * Math.sin(a) + (py - mid) * Math.cos(a)]
      const d = [(px - q[0]) / m.s, (py - q[1]) / m.s]
      t = await now(page)
      await page.evaluate(([[x, y], [dx, dy]]) => {
        const stage = document.getElementById('stage')
        const ptr = (type, k, buttons) => stage.dispatchEvent(new PointerEvent(type, { pointerId: 1, pointerType: 'mouse', isPrimary: true,
          button: 0, buttons, clientX: x + dx * k / 20, clientY: y + dy * k / 20, bubbles: true }))
        ptr('pointerdown', 0, 1)
        for (let k = 1; k <= 20; k++) ptr('pointermove', k, 1)
        ptr('pointerup', 20, 0)
      }, [s, d])
      const m2 = { s: m.s, x: m.x - d[0] * m.s, y: m.y - d[1] * m.s }
      await drawnSince(page, t)
      await shows(page, await probes(page, n, m2), L2, `n=${n}, turned and dragged to P turned`, problem)
      await matches(page, n, m2, n - 1, `n=${n}, turned and dragged to P turned`, problem)
    }
  },
}

const results = Object.fromEntries(Object.keys(CHECKS).map(k => [k, []]))
for (const [name, engine] of [['chromium', chromium], ['webkit', webkit], ['firefox', firefox]]) {
  const browser = await engine.launch()
  for (const [check, run] of Object.entries(CHECKS)) {
    const page = await browser.newPage({ viewport: { width: W, height: H } })
    page.setDefaultTimeout(10000)   // every check takes under a second once the page has loaded
    await page.route(/fonts\.(googleapis|gstatic)\.com/, r => r.abort())   // no check depends on the font
    const problem = msg => results[check].push(`${name}: ${msg}`)
    // A check that throws (a timeout, say) fails with what it threw, and the other checks still run
    await run(page, problem).catch(e => problem(`${e.name}: ${e.message.split('\n')[0]}`))
    await page.close()
  }
  await browser.close()
}
server.close()
console.log(JSON.stringify(results))
