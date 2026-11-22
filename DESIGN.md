# Inkproof.Export design

## Lowering

`lowerShape` turns each Scene shape into a short list of primitives (filled polygon, round-capped stroke, disc, text, clip scope) in grid coordinates, and commands are taken in Scene's `DisplayList.paintOrder` (ascending layer, list order within a layer), which is the raster model's own order by Scene's `pixelColor_eq_paintOver`. SVG and PDF are two writers over the same primitives, so they cover the same commands. A strip run is one stroke, so nothing is drawn across a gap; a lone value is a disc. Strokes are at least one unit wide, so a zero half-width strip stays visible. Envelopes and areas become one quadrilateral per adjacent pair of values, or a one-unit line for a lone value. Text is drawn in Helvetica at the box's height, since the model fixes only the box. Vector output blends partial alpha, where the raster model replaces colour outright.

## PNG

`png` renders with Scene's `render` and encodes the image as 8-bit RGBA. The deflate stream uses stored blocks, so the file is uncompressed and needs no compressor; there is nothing to reimplement of the rasterizer. A grid with no pixels has no PNG.

## Core declarations

Colour hex digits, PDF xref offsets and the distinct opacities use `Nat.toDigits`, `List.leftpad` and `List.eraseDups`. They are structural list functions over `Nat` and `Char` with no runtime string primitives (unlike `BitVec.toHex`), so nothing in them is specific to native code.
