/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Export.Num
import Inkproof.Export.Order

namespace Inkproof.Export

open Inkproof.Scene

private def hex2 (n : UInt8) : String :=
  String.ofList (List.leftpad 2 '0' (Nat.toDigits 16 n.toNat))

private def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '"' => "&quot;"
    | c => c.toString) ""

private def paint (attr : String) (c : Color) : String :=
  let base := s!"{attr}=\"#{hex2 c.r}{hex2 c.g}{hex2 c.b}\""
  if c.a = 255 then base else s!"{base} {attr}-opacity=\"{decimal (c.a.toNat / 255 : Rat)}\""

private def points (pts : List Pt) : String :=
  " ".intercalate (pts.map fun p => s!"{decimal p.x},{decimal p.y}")

private def lo (a b : Rat) : Rat := min a b
private def hi (a b : Rat) : Rat := max a b

/-- One SVG fragment for a primitive; `n` numbers the clip paths. -/
private def element (n : Nat) : Prim → String × Nat
  | .fill c pts => (s!"<polygon points=\"{points pts}\" {paint "fill" c}/>", n)
  | .stroke c w pts =>
    (s!"<polyline points=\"{points pts}\" fill=\"none\" {paint "stroke" c} stroke-width=\"{decimal w}\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/>", n)
  | .disc c p r => (s!"<circle cx=\"{decimal p.x}\" cy=\"{decimal p.y}\" r=\"{decimal r}\" {paint "fill" c}/>", n)
  | .text c b s =>
    let h := hi b.y0 b.y1 - lo b.y0 b.y1
    (s!"<text x=\"{decimal (lo b.x0 b.x1)}\" y=\"{decimal (lo b.y0 b.y1 + h * 4 / 5)}\" font-family=\"Helvetica, Arial, sans-serif\" font-size=\"{decimal h}\" {paint "fill" c}>{escape s}</text>", n)
  | .clipBegin b =>
    (s!"<clipPath id=\"clip{n}\"><rect x=\"{decimal (lo b.x0 b.x1)}\" y=\"{decimal (lo b.y0 b.y1)}\" width=\"{decimal (hi b.x0 b.x1 - lo b.x0 b.x1)}\" height=\"{decimal (hi b.y0 b.y1 - lo b.y0 b.y1)}\"/></clipPath><g clip-path=\"url(#clip{n})\">", n + 1)
  | .clipEnd => ("</g>", n)

/-- The SVG document of a list of primitives on a canvas of `w` by `h` units. -/
def svgOf (w h : Nat) (prims : List Prim) : String :=
  let (parts, _) := prims.foldl (fun (acc, n) p => let (s, n') := element n p; (s :: acc, n')) ([], 0)
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" viewBox=\"0 0 {w} {h}\">\n"
    ++ "".intercalate (parts.reverse.map (· ++ "\n")) ++ "</svg>\n"

/-- A display list as an SVG document `w` by `h` units, one unit per grid pixel. -/
def svg (dl : DisplayList) (w h : Nat) : String := svgOf w h (lowerAll dl)

theorem svg_eq (dl : DisplayList) (w h : Nat) :
    svg dl w h = svgOf w h (dl.paintOrder.flatMap fun c => lowerShape c.color c.shape) := rfl

end Inkproof.Export
