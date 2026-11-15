/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene

namespace Inkproof.Export

open Inkproof.Scene

private def be32 (n : UInt32) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

private def crcEntry (n : UInt32) : UInt32 := Id.run do
  let mut c := n
  for _ in [0:8] do
    c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
  return c

private def crcTable : Array UInt32 := (Array.range 256).map fun n => crcEntry n.toUInt32

/-- The CRC-32 (IEEE) of `data`, as PNG chunks carry it. Checked against its published test vector;
a theorem would need the polynomial-division specification, which is out of reach here. -/
def crc32 (data : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for b in data do
    c := crcTable.getD ((c ^^^ b.toUInt32) &&& 0xFF).toNat 0 ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

/-- The Adler-32 checksum of `data`, as zlib streams carry it. Checked against published vectors; a
theorem would need the modular-sum specification over the byte fold, which did not close in the time-box. -/
def adler32 (data : ByteArray) : UInt32 := Id.run do
  let mut a : UInt32 := 1
  let mut b : UInt32 := 0
  for x in data do
    a := (a + x.toUInt32) % 65521
    b := (b + a) % 65521
  return (b <<< 16) ||| a

/-- A zlib stream holding `data` in stored (uncompressed) deflate blocks. -/
private def zlibStored (data : ByteArray) : ByteArray := Id.run do
  let mut out : ByteArray := ⟨#[0x78, 0x01]⟩
  let mut pos := 0
  repeat
    let n := min 65535 (data.size - pos)
    let final : UInt8 := if pos + n >= data.size then 1 else 0
    let len := n.toUInt16
    out := out.push final
      |>.push len.toUInt8 |>.push (len >>> 8).toUInt8
      |>.push (~~~len).toUInt8 |>.push ((~~~len) >>> 8).toUInt8
    out := out ++ data.extract pos (pos + n)
    pos := pos + n
    if final == 1 then break
  return out ++ be32 (adler32 data)

private def chunk (kind : String) (body : ByteArray) : ByteArray :=
  let typed := kind.toUTF8 ++ body
  be32 body.size.toUInt32 ++ typed ++ be32 (crc32 typed)

/-- The scanlines of an image, each preceded by filter type 0, as RGBA bytes. -/
private def scanlines (img : Image) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (img.height * (1 + 4 * img.width))
  for h : i in [0:img.pixels.size] do
    if i % img.width == 0 then out := out.push 0
    let c := img.pixels[i]
    out := out.push c.r |>.push c.g |>.push c.b |>.push c.a
  return out

/-- Whether an image can be a PNG: both sides positive and below 2^31. -/
def encodable (img : Image) : Prop :=
  0 < img.width ∧ img.width < 2 ^ 31 ∧ 0 < img.height ∧ img.height < 2 ^ 31

instance (img : Image) : Decidable (encodable img) := by unfold encodable; infer_instance

/-- An image as an 8-bit RGBA PNG file, or `none` when it has no pixels or a side is too large. -/
def encodePng (img : Image) : Option ByteArray :=
  if encodable img then
    some (⟨#[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]⟩
      ++ chunk "IHDR" (be32 img.width.toUInt32 ++ be32 img.height.toUInt32 ++ ⟨#[8, 6, 0, 0, 0]⟩)
      ++ chunk "IDAT" (zlibStored (scanlines img))
      ++ chunk "IEND" ByteArray.empty)
  else none

theorem encodePng_isSome (img : Image) : (encodePng img).isSome ↔ encodable img := by
  unfold encodePng; split <;> simp_all

/-- A display list as a PNG file of the grid's size, rasterized by Scene's reference rasterizer
over the background `bg`; `none` when the grid is empty or too large. -/
def png (dl : DisplayList) (g : Grid) (bg : Color) : Option ByteArray :=
  encodePng (render dl g bg)

theorem png_eq (dl : DisplayList) (g : Grid) (bg : Color) :
    png dl g bg = encodePng (render dl g bg) := rfl

end Inkproof.Export
