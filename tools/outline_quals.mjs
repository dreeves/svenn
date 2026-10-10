// A qual of canvas.js's outline() without a browser (quals.py: qual_outline). quals.py runs this and reads its
// output: it runs canvas.js in a node vm, with a Path2D that records its pieces and stand-ins for what else canvas.js
// touches (canvases that draw nothing, a setTimeout that calls at once, a postMessage that keeps what it is given), and
// prints {n: [problem, ...]} as JSON for each drawing n given.
//
// Usage: node tools/outline_quals.mjs N ...
import assert from 'node:assert/strict'
import path from 'node:path'
import vm from 'node:vm'
import { readFile } from 'node:fs/promises'
import { fileURLToPath } from 'node:url'

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const PAGE = 51200, MID = PAGE / 2    // the side of every drawing's square page, and its centre (venn.py's PAGE)
const FIT = PAGE / 700                // page units to a pixel at fit: the page 700 pixels across, about as in a 1200 by
                                      // 800 window (744 for n = 7)
const W = 1200, H = 800               // the window, in pixels
const SAMPLES = 16                    // points of a span tried, evenly spaced in its parameter from its start

// A Path2D that records its pieces, each [command, ...numbers]
class Path2D {
  constructor() { this.pieces = [] }
  moveTo(...p) { this.pieces.push(['M', ...p]) }
  lineTo(...p) { this.pieces.push(['L', ...p]) }
  bezierCurveTo(...p) { this.pieces.push(['C', ...p]) }
  closePath() {}
}
// A 2D context that draws nothing: what is set on it reads back (draw() reads its lineWidth), and every method does
// nothing (getImageData() gives a pixel)
const nothing = new Proxy({}, { get: (o, k) => k in o ? o[k] : k === 'getImageData' ? () => ({ data: [0, 0, 0, 0] }) : () => {} })
class OffscreenCanvas {
  getContext() { return nothing }
  transferToImageBitmap() { return {} }
}
const posted = []                     // what canvas.js posts the page
const context = vm.createContext({ Path2D, OffscreenCanvas, location: { search: '' }, addEventListener() {},
                                   postMessage: m => posted.push(m), setTimeout: f => f(), performance: { now: () => 0 },
                                   URLSearchParams, TextEncoder, TextDecoder })
vm.runInContext(await readFile(path.join(ROOT, 'canvas.js'), 'utf8'), context)
const { parse, tree, outline, draw } = vm.runInContext('({ parse, tree, outline, draw })', context)
// draw()'s calls of outline() go through this, which keeps the view and the tol of each (canvas.js's outline is the
// vm's global)
const views = [], tols = []
context.outline = (xy, t, view, tol) => {
  views.push(view)
  tols.push(tol)
  return outline(xy, t, view, tol)
}

// Point t of the cubic span whose control points are c
const bezier = (c, t) => [0, 1].map(o => (1 - t) ** 3 * c[o] + 3 * (1 - t) ** 2 * t * c[2 + o] + 3 * (1 - t) * t * t * c[4 + o] + t ** 3 * c[6 + o])

// The problems with outline() for drawing n, d as parse() gives it: for the window at fit about the page's centre, and
// zoomed in by 4, 16 and 64 about five knots of curve 0 (a tenth, three tenths, ... of the way along it), with tol half a
// pixel, each chord outline() puts in place of a run of spans whose box meets the window strays at most tol from the run
// (outline() replaces only runs whose flatness, a bound on that, is under tol): no point of the run tried (SAMPLES a
// span) further than tol from the chord. And draw(), for the view at fit with dpr 1 and 2 device pixels to a CSS pixel,
// and for the view zoomed in by 16 about the page's centre with 2 (no curves, the shading outside every curve), passes
// outline() a finite view, and tol half a pixel of its shading's canvas: s / rs / 2, s page units to a CSS pixel at
// that view and rs the canvas's pixels to a CSS pixel, as draw() posts it.
function problems(n, d) {
  const xy = d.xy, t = tree(xy), spans = (xy.length - 2) / 6, bad = []
  for (const [dpr, z, where] of [[1, 1, 'at fit'], [2, 1, 'at fit'], [2, 16, 'zoomed in by 16']]) {
    const s = FIT / z
    posted.length = views.length = tols.length = 0
    draw({ ...d, tree: t, cells: { paths: [], boxes: [], spans: [] } }, { x: MID - W / 2 * s, y: MID - H / 2 * s, s, fit: FIT,
          w: W, h: H, dpr, k: -1, inside: d.angles.map(() => false), colour: '#e2e5ea', seq: 1 })
    const want = posted.length === 1 ? s / posted[0].rs / 2 : NaN, wrong = tols.filter(tol => !(Math.abs(tol / want - 1) < 1e-12))
    if (posted.length !== 1 || tols.length !== n || wrong.length)
      bad.push(`${where}, at devicePixelRatio ${dpr}, draw() passed outline() ${tols.length} tols of ${[...new Set(tols.map(tol => (tol / s).toPrecision(6)))]} CSS pixels and posted rs ${posted.map(m => m.rs).join(' and ')}, not ${n} tols of half a pixel of its shading's canvas, ${(want / s).toPrecision(6)}`)
    const unbounded = views.filter(v => !v.every(Number.isFinite))
    if (unbounded.length) bad.push(`${where}, at devicePixelRatio ${dpr}, draw() passed outline() ${unbounded.length} views not finite, e.g. [${unbounded[0]}]`)
  }
  const knot = new Map()   // "x,y" of each knot, from the second to the last (the first's again), to its number
  for (let k = 1; k <= spans; k++) knot.set(`${xy[6 * k]},${xy[6 * k + 1]}`, k)
  const along = [0.1, 0.3, 0.5, 0.7, 0.9].map(f => Math.floor(f * spans)).map(k => [xy[6 * k], xy[6 * k + 1]])
  for (const [z, centres] of [[1, [[MID, MID]]], [4, along], [16, along], [64, along]]) {
    const s = FIT / z, tol = s / 2
    for (const [cx, cy] of centres) {
      const [x0, y0, x1, y1] = [cx - W / 2 * s, cy - H / 2 * s, cx + W / 2 * s, cy + H / 2 * s]
      const [path] = outline(xy, t, [x0, y0, x1, y1], tol)
      const [move, ...pieces] = path.pieces
      assert(move[0] === 'M' && move[1] === xy[0] && move[2] === xy[1], `n=${n}: outline() starts ${move}, not at curve 0's start`)
      let a = 0, worst = [0, 0, 0]   // the span the next piece starts at; the worst chord: tol strayed, its run's spans
      for (const [command, ...p] of pieces) {
        const b = knot.get(`${p.at(-2)},${p.at(-1)}`)
        assert(b > a && (command === 'L' || b === a + 1), `n=${n}: outline()'s ${command} from knot ${a} ends at (${p.at(-2)}, ${p.at(-1)}), knot ${b}`)
        let [bx0, by0, bx1, by1] = [Infinity, Infinity, -Infinity, -Infinity]   // the box of the run's control points
        for (let q = 6 * a; q <= 6 * b; q += 2) {
          bx0 = Math.min(bx0, xy[q])
          by0 = Math.min(by0, xy[q + 1])
          bx1 = Math.max(bx1, xy[q])
          by1 = Math.max(by1, xy[q + 1])
        }
        if (command === 'L' && bx0 <= x1 && bx1 >= x0 && by0 <= y1 && by1 >= y0) {
          const [ax, ay, dx, dy] = [xy[6 * a], xy[6 * a + 1], xy[6 * b] - xy[6 * a], xy[6 * b + 1] - xy[6 * a + 1]], l = dx * dx + dy * dy
          for (let j = a; j < b; j++) for (let i = 0; i < SAMPLES; i++) {
            const [px, py] = bezier(xy.subarray(6 * j, 6 * j + 8), i / SAMPLES)
            const u = Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / (l || 1)))
            const off = Math.hypot(px - ax - u * dx, py - ay - u * dy) / tol
            if (off > worst[0]) worst = [off, a, b - 1]
          }
        }
        a = b
      }
      assert(a === spans, `n=${n}: outline()'s pieces end at knot ${a} of ${spans}`)
      if (worst[0] > 1) bad.push(`zoomed in by ${z} about (${cx}, ${cy}): the chord of spans ${worst[1]} to ${worst[2]} strays ${worst[0].toFixed(3)} tol from them, over 1`)
    }
  }
  return bad.map(p => `n=${n}, ${p}`)
}

const results = {}
for (const n of process.argv.slice(2).map(Number)) {
  results[n] = problems(n, parse(new Uint8Array(await readFile(path.join(ROOT, 'img', `venn-${String(n).padStart(2, '0')}.svg`))), n))
}
console.log(JSON.stringify(results))
