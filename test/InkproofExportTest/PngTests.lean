/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofExportTest.Common
import InkproofTools.Test.Harness

open Inkproof.Scene Inkproof.Export InkproofTools.Test

namespace InkproofExportTest

def be32 (b : ByteArray) (i : Nat) : Nat :=
  ((b[i]?.getD 0)).toNat * 16777216 + (b[i + 1]?.getD 0).toNat * 65536 + (b[i + 2]?.getD 0).toNat * 256 + (b[i + 3]?.getD 0).toNat

/-- The chunks of a PNG file as (type, body), or an error if a length or checksum is wrong. -/
def chunks (b : ByteArray) : Except String (List (String × ByteArray)) := do
  let mut pos := 8
  let mut out := []
  for _ in [0:8] do
    if pos + 12 > b.size then break
    let n := be32 b pos
    let kind := (String.fromUTF8? (b.extract (pos + 4) (pos + 8))).getD ""
    let body := b.extract (pos + 8) (pos + 8 + n)
    if (crc32 (b.extract (pos + 4) (pos + 8 + n))).toNat != be32 b (pos + 8 + n) then
      throw s!"bad checksum in {kind}"
    out := out ++ [(kind, body)]
    pos := pos + 12 + n
  return out

/-- The payload of a zlib stream of stored blocks, checking its framing and checksum. -/
def unstore (z : ByteArray) : Except String ByteArray := do
  let mut pos := 2
  let mut out := ByteArray.empty
  for _ in [0:1000] do
    let final := (z[pos]?.getD 0)
    let n := (z[pos + 1]?.getD 0).toNat + 256 * (z[pos + 2]?.getD 0).toNat
    let nn := (z[pos + 3]?.getD 0).toNat + 256 * (z[pos + 4]?.getD 0).toNat
    if n + nn != 65535 then throw "bad block length"
    out := out ++ z.extract (pos + 5) (pos + 5 + n)
    pos := pos + 5 + n
    if final == 1 then break
  if (adler32 out).toNat != be32 z pos then throw "bad adler"
  if pos + 4 != z.size then throw "trailing bytes"
  return out

/-- The pixel at (col, row) of a decoded RGBA image of width `w`. -/
def pixelAt (raw : ByteArray) (w col row : Nat) : List UInt8 :=
  let i := row * (1 + 4 * w) + 1 + 4 * col
  [(raw[i]?.getD 0), (raw[i + 1]?.getD 0), (raw[i + 2]?.getD 0), (raw[i + 3]?.getD 0)]

def decode (b : ByteArray) : Except String (Nat × Nat × ByteArray) := do
  let cs ← chunks b
  let some (_, hdr) := cs.find? (·.1 == "IHDR") | throw "no IHDR"
  let some (_, idat) := cs.find? (·.1 == "IDAT") | throw "no IDAT"
  let raw ← unstore idat
  return (be32 hdr 0, be32 hdr 4, raw)

def pngTests : List TestCase := [
  .mk "published checksum vectors" do
    check (crc32 "123456789".toUTF8 == 0xCBF43926) "crc32"
    check (adler32 "Wikipedia".toUTF8 == 0x11E60398) "adler32",
  .mk "the file has the signature, the grid's dimensions and valid checksums" do
    let some b := png #[] ⟨8, 6⟩ bg | throw "no file"
    check (b.extract 0 8 == ⟨#[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]⟩) "signature"
    let (w, h, raw) ← decode b
    check (w == 8 && h == 6) "dimensions"
    check (raw.size == 6 * (1 + 4 * 8)) "raster size",
  .mk "covered pixels are painted and the rest keep the background" do
    let some b := png #[⟨0, red, .rect ⟨1, 1, 3, 2⟩⟩] ⟨8, 6⟩ bg | throw "no file"
    let (w, _, raw) ← decode b
    check (pixelAt raw w 1 1 == [255, 0, 0, 255] && pixelAt raw w 2 1 == [255, 0, 0, 255]) "rectangle not painted"
    check (pixelAt raw w 6 5 == [255, 255, 255, 255]) "background lost",
  .mk "a raster larger than one stored block round-trips" do
    let some b := png #[⟨0, blue, .rect ⟨150, 80, 199, 99⟩⟩] ⟨200, 100⟩ bg | throw "no file"
    let (w, h, raw) ← decode b
    check (w == 200 && h == 100 && raw.size == 100 * 801) "size"
    check (raw.size > 65535) "test must span blocks"
    check (pixelAt raw w 199 99 == [0, 0, 255, 255] && pixelAt raw w 0 0 == [255, 255, 255, 255]) "pixels",
  .mk "an empty grid has no PNG" do
    check (png #[] ⟨0, 4⟩ bg).isNone "width zero"
    check (png #[] ⟨4, 0⟩ bg).isNone "height zero"
]

end InkproofExportTest
