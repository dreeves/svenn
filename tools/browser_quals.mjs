// Browser quals for view.html, the viewer. quals.py runs this and reads its output: it serves the repo over HTTP,
// opens the viewer in Chromium, WebKit and Firefox with Playwright, and prints {check: [problem, ...]} as JSON, each
// problem one line naming the browser and what went wrong. quals.py holds each check's replicata and expectata.
//
// Usage: node tools/browser_quals.mjs N ...   (every n whose drawing the viewer shows; quals.py passes them)
import assert from 'node:assert/strict'
import http from 'node:http'
import path from 'node:path'
import { readFile } from 'node:fs/promises'
import { fileURLToPath } from 'node:url'
import { chromium, firefox, webkit } from 'playwright'

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const NS = process.argv.slice(2).map(Number)
const SMALL = 7                       // the n most checks use: quick to load, with curves enough to tell apart
const W = 1200, H = 800               // the window
const STEP = Math.min(W, H) / 10      // what an arrow key pans by
const TYPES = { '.html': 'text/html', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
                '.ico': 'image/x-icon', '.webmanifest': 'application/manifest+json' }
assert(NS.includes(SMALL), `n = ${SMALL} is not among the n given: ${NS}`)
const nn = n => String(n).padStart(2, '0')   // as in the drawings' file names

// A static file server for the repo, answering 404 for what is not there, as GitHub Pages does
const server = http.createServer(async (req, res) => {
  const file = path.join(ROOT, new URL(req.url, 'http://localhost').pathname)
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
const ready = (page, n) => page.waitForFunction(
  n => document.querySelectorAll('#curves button:enabled').length === n && document.querySelectorAll('#stage path').length === n, n)

async function open(page, n) {
  await page.goto(`${BASE}/view.html?n=${n}`)
  await ready(page, n)
}

// Expect the screen point s to still show page point p (to half a pixel), and the scale to be want
function holds(problem, m, s, p, want, what) {
  if (far(at(m, p), s) > 0.5) problem(`${what}: page point ${fmt(p)} moved from ${fmt(s)} to ${fmt(at(m, p))}`)
  if (Math.abs(m.a / want - 1) > 1e-3 || Math.abs(m.d / want - 1) > 1e-3) problem(`${what}: scale ${m.a}, ${m.d}, not ${want}`)
}

const CHECKS = {
  async fit(page, problem) {
    for (const n of NS) {
      await open(page, n)
      const { page: side, stroke } = await drawing(n)
      const m = await ctm(page)
      const k = Math.min(W, H) / side
      holds(problem, m, [W / 2, H / 2], [side / 2, side / 2], k, `n=${n}, the page's centre`)
      const css = await page.evaluate(() => [...document.querySelectorAll('#stage path')].map(p => {
        const s = getComputedStyle(p)
        return [s.vectorEffect, parseFloat(s.strokeWidth)]
      }))
      css.forEach(([effect, width], i) => {
        if (effect !== 'non-scaling-stroke') problem(`n=${n}: curve ${i} has vector-effect ${effect}`)
        if (Math.abs(width / (stroke * k) - 1) > 1e-3) problem(`n=${n}: curve ${i} is ${width}px wide, not ${stroke * k}px`)
      })
    }
  },

  async curves(page, problem) {
    await open(page, SMALL)
    const state = () => page.evaluate(() => ({
      shown: [...document.querySelectorAll('#stage path')].map(p => getComputedStyle(p).display !== 'none'),
      pressed: [...document.querySelectorAll('#curves button')].map(b => b.getAttribute('aria-pressed') === 'true'),
      colours: [...document.querySelectorAll('#curves button')].map(b => getComputedStyle(b).backgroundColor),
      strokes: [...document.querySelectorAll('#stage path')].map(p => getComputedStyle(p).stroke) }))
    const swatch = k => page.locator('#curves button').nth(k)
    const expect = (s, k, what) => {   // curves 0 to k shown, and exactly their swatches pressed
      const want = s.shown.map((_, i) => i <= k)
      if (String(s.shown) !== String(want)) problem(`${what}: curves shown ${s.shown}, not ${want}`)
      if (String(s.pressed) !== String(want)) problem(`${what}: swatches pressed ${s.pressed}, not ${want}`)
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
    const m1 = await ctm(page)
    await page.keyboard.down('Control')
    await page.mouse.wheel(0, 100)
    await page.keyboard.up('Control')
    await frames(page)
    holds(problem, await ctm(page), s, p, m1.a / Math.E, 'ctrl+wheel 100px down')
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
  },

  async pinch(page, problem) {
    await open(page, SMALL)
    const a = [W * 0.3, H * 0.5], b = [W * 0.4, H * 0.5], b2 = [W * 0.5, H * 0.5]
    const m0 = await ctm(page), p = under(m0, a)
    // Two touch pointers, as a phone reports two fingers: one stays at a, the other moves from b to b2, doubling
    // their distance apart. (Synthetic events: Playwright drives one touch at a time.)
    await page.evaluate(([a, b, b2]) => {
      const stage = document.getElementById('stage')
      const ev = (type, id, [x, y]) => stage.dispatchEvent(new PointerEvent(type,
        { pointerId: id, pointerType: 'touch', isPrimary: id === 1, clientX: x, clientY: y, bubbles: true }))
      ev('pointerdown', 1, a); ev('pointerdown', 2, b); ev('pointermove', 2, b2); ev('pointerup', 2, b2); ev('pointerup', 1, a)
    }, [a, b, b2])
    holds(problem, await ctm(page), a, p, m0.a * 2, 'pinch')
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
    const c = [W / 2, H / 2]
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
    const c = [W / 2, H / 2]
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
    const q = under(await ctm(page), [c[0] + STEP, c[1]])
    await page.keyboard.press('ArrowRight')
    holds(problem, await ctm(page), c, q, m0.a, 'right arrow key')
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
    await open(page, SMALL)
    await page.click('#in')
    const c = [W / 2, H / 2], m0 = await ctm(page), p = under(m0, c)
    await page.setViewportSize({ width: 800, height: 600 })
    await frames(page)
    holds(problem, await ctm(page), [400, 300], p, m0.a * 600 / Math.min(W, H), 'window resized to 800 by 600')
    await page.setViewportSize({ width: W, height: H })
  },

  async links(page, problem) {
    await open(page, SMALL)
    const got = await page.evaluate(() => ({ title: document.title, back: document.getElementById('back').href,
                                             raw: document.getElementById('raw').href }))
    const want = { title: `${SMALL} · Diagrammata Venniana Symmetrica`, back: `${BASE}/index.html#n${SMALL}`,
                   raw: `${BASE}/img/venn-${nn(SMALL)}.svg` }
    for (const k in want) if (got[k] !== want[k]) problem(`${k} is ${got[k]}, not ${want[k]}`)
  },

  async loading(page, problem) {
    let release
    const gate = new Promise(ok => { release = ok })
    await page.route(`**/img/venn-${nn(SMALL)}.svg`, async route => { await gate; await route.continue() })
    await page.goto(`${BASE}/view.html?n=${SMALL}`)
    await page.waitForSelector('#curves button')
    const state = () => page.evaluate(() => ({
      image: [...document.querySelectorAll('#stage image')].map(i => i.getAttribute('href')),
      paths: document.querySelectorAll('#stage path').length,
      enabled: document.querySelectorAll('#curves button:enabled').length,
      swatches: document.querySelectorAll('#curves button').length }))
    const s0 = await state()
    const want0 = { image: [`img/venn-${nn(SMALL)}.png`], paths: 0, enabled: 0, swatches: SMALL }
    if (JSON.stringify(s0) !== JSON.stringify(want0)) problem(`while the SVG loads: ${JSON.stringify(s0)}, not ${JSON.stringify(want0)}`)
    release()
    await ready(page, SMALL)
    const s1 = await state()
    const want1 = { image: [], paths: SMALL, enabled: SMALL, swatches: SMALL }
    if (JSON.stringify(s1) !== JSON.stringify(want1)) problem(`once it has loaded: ${JSON.stringify(s1)}, not ${JSON.stringify(want1)}`)
    await page.unroute(`**/img/venn-${nn(SMALL)}.svg`)
  },

  async error(page, problem) {
    await page.goto(`${BASE}/view.html?n=4`)
    await page.waitForSelector('#error', { state: 'visible' })
    const got = await page.evaluate(() => ({ text: document.getElementById('error').textContent,
                                             swatches: document.querySelectorAll('#curves button').length,
                                             enabled: document.querySelectorAll('#curves button:enabled').length }))
    if (!got.text.includes('img/venn-04.svg') || !got.text.includes('404')) problem(`the error says "${got.text}"`)
    if (got.swatches !== 4 || got.enabled !== 0) problem(`${got.swatches} swatches, ${got.enabled} of them enabled`)
  },

  async phone(page, problem) {
    const n = Math.max(...NS)
    await page.setViewportSize({ width: 375, height: 667 })
    await open(page, n)
    const boxes = await page.evaluate(() => ['#top', '#raw', '#curves', '#zoom'].map(sel => {
      const r = document.querySelector(sel).getBoundingClientRect()
      return [sel, r.left, r.top, r.right, r.bottom]
    }).concat([['scroll', 0, 0, document.documentElement.scrollWidth, document.documentElement.scrollHeight]]))
    for (const [sel, l, t, r, b] of boxes) {
      if (l < 0 || t < 0 || r > 375 || b > 667) problem(`n=${n}: ${sel} spans (${l}, ${t}) to (${r}, ${b}), outside 375 by 667`)
    }
    const controls = boxes.slice(0, 4)
    controls.forEach(([s1, l1, t1, r1, b1], i) => controls.slice(i + 1).forEach(([s2, l2, t2, r2, b2]) => {
      if (l1 < r2 && l2 < r1 && t1 < b2 && t2 < b1) problem(`n=${n}: ${s1} and ${s2} overlap`)
    }))
    await page.setViewportSize({ width: W, height: H })
  },
}

const results = Object.fromEntries(Object.keys(CHECKS).map(k => [k, []]))
for (const [name, engine] of [['chromium', chromium], ['webkit', webkit], ['firefox', firefox]]) {
  const browser = await engine.launch()
  for (const [check, run] of Object.entries(CHECKS)) {
    const page = await browser.newPage({ viewport: { width: W, height: H } })
    page.setDefaultTimeout(10000)   // every check takes under a second once the page has loaded
    const problem = msg => results[check].push(`${name}: ${msg}`)
    // A check that throws (a timeout, say) fails with what it threw, and the other checks still run
    await run(page, problem).catch(e => problem(`${e.name}: ${e.message.split('\n')[0]}`))
    await page.close()
  }
  await browser.close()
}
server.close()
console.log(JSON.stringify(results))
