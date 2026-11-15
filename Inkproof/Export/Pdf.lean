/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Export.Num
import Inkproof.Export.Order

namespace Inkproof.Export

open Inkproof.Scene

private def unit (v : UInt8) : String := decimal (v.toNat / 255 : Rat)

private def rgb (op : String) (c : Color) : String := s!"{unit c.r} {unit c.g} {unit c.b} {op}"

private def alphaOf (c : Color) : List UInt8 := if c.a = 255 then [] else [c.a]

private def primColor : Prim → Option Color
  | .fill c _ | .stroke c _ _ | .disc c _ _ | .text c _ _ => some c
  | _ => none

/-- The distinct partial opacities that the primitives use. -/
private def alphas (prims : List Prim) : List UInt8 :=
  prims.foldl (fun acc p => match primColor p with
    | some c => (alphaOf c).foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc
    | none => acc) []

private def gs (c : Color) : String := "".intercalate ((alphaOf c).map fun a => s!"/G{a} gs ")

private def point (p : Pt) : String := s!"{decimal p.x} {decimal p.y}"

private def path (pts : List Pt) : String :=
  match pts with
  | [] => ""
  | p :: rest => s!"{point p} m " ++ "".intercalate (rest.map fun q => s!"{point q} l ")

/-- A circle as four Bezier curves. -/
private def circle (c : Pt) (r : Rat) : String :=
  let k := r * 5523 / 10000
  let pt (x y : Rat) := s!"{decimal x} {decimal y}"
  s!"{pt (c.x + r) c.y} m "
    ++ s!"{pt (c.x + r) (c.y + k)} {pt (c.x + k) (c.y + r)} {pt c.x (c.y + r)} c "
    ++ s!"{pt (c.x - k) (c.y + r)} {pt (c.x - r) (c.y + k)} {pt (c.x - r) c.y} c "
    ++ s!"{pt (c.x - r) (c.y - k)} {pt (c.x - k) (c.y - r)} {pt c.x (c.y - r)} c "
    ++ s!"{pt (c.x + k) (c.y - r)} {pt (c.x + r) (c.y - k)} {pt (c.x + r) c.y} c h "

/-- A string literal in Latin-1 as octal escapes, so the stream stays ASCII; other characters become `?`. -/
private def literal (s : String) : String :=
  let esc (c : Char) : String :=
    let n := if c.toNat < 256 then c.toNat else '?'.toNat
    s!"\\{n / 64}{n / 8 % 8}{n % 8}"
  "(" ++ "".intercalate (s.toList.map esc) ++ ")"

private def operation : Prim → String
  | .fill c pts => s!"q {gs c}{rgb "rg" c} {path pts}h f Q\n"
  | .stroke c w pts => s!"q {gs c}{rgb "RG" c} 1 J 1 j {decimal w} w {path pts}S Q\n"
  | .disc c p r => s!"q {gs c}{rgb "rg" c} {circle p r}f Q\n"
  | .text c b s =>
    let h := max b.y0 b.y1 - min b.y0 b.y1
    s!"q {rgb "rg" c} BT /F1 {decimal h} Tf 1 0 0 -1 {decimal (min b.x0 b.x1)} {decimal (min b.y0 b.y1 + h * 4 / 5)} Tm {literal s} Tj ET Q\n"
  | .clipBegin b =>
    s!"q {decimal (min b.x0 b.x1)} {decimal (min b.y0 b.y1)} {decimal (max b.x0 b.x1 - min b.x0 b.x1)} {decimal (max b.y0 b.y1 - min b.y0 b.y1)} re W n\n"
  | .clipEnd => "Q\n"

/-- The PDF file of a list of primitives on a page of `w` by `h` points. The page is one stream
with the y axis flipped, so primitives keep the grid's orientation. -/
def pdfOf (w h : Nat) (prims : List Prim) : ByteArray := Id.run do
  let content := (s!"1 0 0 -1 0 {h} cm\n" ++ "".intercalate (prims.map operation)).toUTF8
  let extra := alphas prims
  let states := " ".intercalate (extra.map fun a => s!"/G{a} << /ca {decimal (a.toNat / 255 : Rat)} /CA {decimal (a.toNat / 255 : Rat)} >>")
  let objects : List ByteArray :=
    [ "<< /Type /Catalog /Pages 2 0 R >>".toUTF8
    , "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8
    , s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {w} {h}] /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> /ExtGState << {states} >> >> >>".toUTF8
    , s!"<< /Length {content.size} >>\nstream\n".toUTF8 ++ content ++ "endstream".toUTF8
    , "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>".toUTF8 ]
  let mut out := "%PDF-1.4\n".toUTF8
  let mut offsets : Array Nat := #[]
  for (o, i) in objects.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{i + 1} 0 obj\n".toUTF8 ++ o ++ "\nendobj\n".toUTF8
  let xref := out.size
  let pad (n : Nat) : String := let s := toString n; "".pushn '0' (10 - s.length) ++ s
  out := out ++ s!"xref\n0 {objects.length + 1}\n0000000000 65535 f \n".toUTF8
  for off in offsets do
    out := out ++ s!"{pad off} 00000 n \n".toUTF8
  out := out ++ s!"trailer\n<< /Size {objects.length + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8
  return out

/-- A display list as a one-page PDF `w` by `h` points, one point per grid pixel. -/
def pdf (dl : DisplayList) (w h : Nat) : ByteArray := pdfOf w h (lowerAll dl)

theorem pdf_eq (dl : DisplayList) (w h : Nat) :
    pdf dl w h = pdfOf w h (dl.paintOrder.flatMap fun c => lowerShape c.color c.shape) := rfl

end Inkproof.Export
