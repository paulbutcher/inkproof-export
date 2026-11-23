# Changelog

## v0.5.2

- README's require example no longer names a version.

## v0.5.1

- Internal padding, hex and de-duplication use Core's `List.leftpad`, `Nat.toDigits` and `List.eraseDups`; no public declaration changes.

## v0.5.0

- `decimal` rounds and trims with Core's `Decimal.roundScaled` and `Decimal.trimZeros`; `thousandths`, `trimZeros` and their theorems are removed.

## v0.4.0

- Lowering uses Scene's `Item.fold` and `Item.runs`; `runs` and `links` are removed, and envelope and area columns are now drawn as lines as well as joined.

## v0.3.2

- README lists what the library does.

## v0.3.1

- Lasm tests run under @lasm/cli 0.8.0.

## v0.3.0

- `decimal` is built on Core's decimal formatter, with `decimal_spec` stating the value its output denotes and that trimming zeros preserves it.
- Painting order is Scene's `DisplayList.paintOrder`; the local `paintOrder` and its theorems are removed.

## v0.1.0

- SVG and one-page PDF output for every Scene display list command kind, in painting order.
- PNG output of a display list rasterized by Scene's reference rasterizer.
