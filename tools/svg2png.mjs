// Rasterize an SVG to a PNG of the given width with resvg (transparent background).
// Usage: node svg2png.mjs IN.svg OUT.png WIDTH
import assert from 'node:assert/strict'
import { readFileSync, writeFileSync } from 'node:fs'
import { Resvg } from '@resvg/resvg-js'

const [inp, out, width] = process.argv.slice(2)
assert.ok(inp.endsWith('.svg') && out.endsWith('.png') && Number.isInteger(Number(width)), process.argv.join(' '))
const png = new Resvg(readFileSync(inp), { fitTo: { mode: 'width', value: Number(width) } }).render().asPng()
writeFileSync(out, png)
