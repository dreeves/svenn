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
const VIEWED = process.argv.slice(2).map(Number)
const SMALL = 7                       // the n most checks use: quick to load, with curves enough to tell apart
const W = 1200, H = 800               // the window
const TYPES = { '.html': 'text/html', '.css': 'text/css', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
                '.ico': 'image/x-icon', '.webmanifest': 'application/manifest+json' }
assert(VIEWED.includes(SMALL), `n = ${SMALL} is not among the n given: ${VIEWED}`)
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
// Each curve's line on screen: how it scales, and how wide it is
const strokes = page => page.evaluate(() => [...document.querySelectorAll('#stage path')].map(p => {
  const s = getComputedStyle(p)
  return [s.vectorEffect, parseFloat(s.strokeWidth)]
}))
// Where the page goes at zoom 1: the square that fits below the top controls and clear of the swatches (a row along
// the bottom, or in a landscape window a column along the right edge), centred there, but never less than half the
// window's shorter side; side is that square's side in pixels, (x, y) its centre
const area = page => page.evaluate(() => {
  const t = document.getElementById('top').getBoundingClientRect().bottom
  const c = document.getElementById('curves'), r = c.getBoundingClientRect()
  const column = getComputedStyle(c).writingMode !== 'horizontal-tb'
  const right = column ? r.left : innerWidth, bottom = column ? innerHeight : r.top
  return { x: right / 2, y: (t + bottom) / 2, side: Math.max(Math.min(right, bottom - t), Math.min(innerWidth, innerHeight) / 2) }
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

const CHECKS = {
  async fit(page, problem) {
    for (const n of VIEWED) {
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
    await open(page, Math.max(...VIEWED))
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
    await open(page, SMALL)
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
    await page.setViewportSize({ width: W, height: H })
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
      swatches: document.querySelectorAll('#curves button').length }))),
      status: await page.locator('#status').isVisible() })
    const s0 = await state()
    const want0 = { image: [`img/venn-${nn(SMALL)}.png`], curves: 0, enabled: 0, swatches: SMALL, status: true }
    if (JSON.stringify(s0) !== JSON.stringify(want0)) problem(`while the SVG loads: ${JSON.stringify(s0)}, not ${JSON.stringify(want0)}`)
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
    const want1 = { image: [], curves: SMALL, enabled: SMALL, swatches: SMALL, status: false }
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
  },

  async phone(page, problem) {
    const n = Math.max(...VIEWED)
    for (const [w, h] of [[375, 667], [320, 568], [844, 390]]) {
      const phone = await page.context().browser().newContext({ viewport: { width: w, height: h }, hasTouch: true })
      const p = await phone.newPage()
      p.setDefaultTimeout(10000)
      await p.route(/fonts\.(googleapis|gstatic)\.com/, r => r.abort())
      await open(p, n)
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
      // Apple's guideline for a touch target is 44 points: 44 CSS pixels
      const small = await p.evaluate(() => [...document.querySelectorAll('button, a')].map(e => {
        const r = e.getBoundingClientRect()
        return [e.id || e.title || e.textContent, Math.round(r.width), Math.round(r.height)]
      }).filter(([, w, h]) => w < 44 || h < 44))
      if (small.length) problem(`${w} wide, n=${n}: on a touch screen these are under 44 by 44 pixels: ${JSON.stringify(small)}`)
      const side = await p.evaluate(() => document.querySelector('#stage svg').getScreenCTM().a * 51200)
      if (w > h && side < 300) problem(`${w} by ${h}, n=${n}: the drawing fits in ${side} pixels, under 300`)
      // A tapped button looks as it did: a touch screen's tap leaves no hover look behind
      const look = () => p.evaluate(() => getComputedStyle(document.getElementById('in')).borderTopColor)
      const was = await look()
      await p.tap('#in')
      await p.waitForTimeout(300)
      if (await look() !== was) problem(`${w} wide: after a tap, + has border ${await look()}, not ${was} as before`)
      await phone.close()
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
