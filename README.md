# Inkproof.Export

Static output of Inkproof display lists as SVG, PDF and PNG, written in Lean. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## What it does

- Render a display list as an SVG document: `svg`, or a PDF file: `pdf` (`svgOf` and `pdfOf` take already lowered primitives).
- Render a display list as a PNG image through Scene's reference rasterizer, `none` if the image cannot be encoded: `png`; encode an existing raster image as PNG: `encodePng`, `encodable`.
- Lower a display list or one shape to drawing primitives (fills, strokes, discs, text, clips) shared by the SVG and PDF writers: `lowerAll`, `lowerShape`, `Prim`, `hairline`.
- Format a rational number as a trimmed decimal string, with a theorem of the value it denotes: `decimal`.
- Checksums for the PNG and zlib streams: `crc32`, `adler32`.

## Requiring it

```lean
require «inkproof-export» from git "https://github.com/paulbutcher/inkproof-export" @ "v0.3.1"
```
