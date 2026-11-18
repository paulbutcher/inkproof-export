/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene

namespace Inkproof.Export

open Inkproof.Scene

/-- A drawing primitive in grid coordinates (x right, y down, one unit per pixel). Strokes have round
caps and joins; polygons are filled. -/
inductive Prim where
  | fill (color : Color) (pts : List Pt)
  | stroke (color : Color) (width : Rat) (pts : List Pt)
  | disc (color : Color) (center : Pt) (radius : Rat)
  | text (color : Color) (box : Rect) (content : String)
  /-- Everything up to the matching `clipEnd` is restricted to the box. -/
  | clipBegin (box : Rect)
  | clipEnd
  deriving Repr

/-- Narrowest width at which a stroke is still drawn, so a zero half-width strip stays visible. -/
def hairline : Rat := 1

private def corners (b : Rect) : List Pt :=
  [⟨b.x0, b.y0⟩, ⟨b.x1, b.y0⟩, ⟨b.x1, b.y1⟩, ⟨b.x0, b.y1⟩]

/-- The primitives that draw a shape in a colour. -/
def lowerShape (color : Color) : Shape → List Prim
  | .strip hw items =>
    let w := max (2 * hw) hairline
    (Item.runs items |>.filter (· ≠ [])).map fun r => match r with
      | [p] => .disc color p (w / 2)
      | r => .stroke color w r
  | .envelope items =>
    Item.fold
      (fun c => .stroke color hairline [⟨c.x, c.lo⟩, ⟨c.x, c.hi⟩])
      (fun a b => .fill color [⟨a.x, a.lo⟩, ⟨b.x, b.lo⟩, ⟨b.x, b.hi⟩, ⟨a.x, a.hi⟩]) items
  | .area y0 items =>
    Item.fold
      (fun a => .stroke color hairline [⟨a.x, y0⟩, a])
      (fun a b => .fill color [⟨a.x, y0⟩, ⟨b.x, y0⟩, b, a]) items
  | .rect b => [.fill color (corners b)]
  | .marker .square c r => [.fill color (corners ⟨c.x - r, c.y - r, c.x + r, c.y + r⟩)]
  | .marker .circle c r => [.disc color c r]
  | .text b s => [.text color b s]
  | .clipped b inner => .clipBegin b :: lowerShape color inner ++ [.clipEnd]

theorem lowerShape_strip (c : Color) (hw : Rat) (items : List (Item Pt)) :
    lowerShape c (.strip hw items) =
      (Item.runs items |>.filter (· ≠ [])).map fun r => match r with
        | [p] => .disc c p (max (2 * hw) hairline / 2)
        | r => .stroke c (max (2 * hw) hairline) r := rfl

theorem lowerShape_envelope (c : Color) (items : List (Item Column)) :
    lowerShape c (.envelope items) =
      Item.fold
        (fun k => .stroke c hairline [⟨k.x, k.lo⟩, ⟨k.x, k.hi⟩])
        (fun a b => .fill c [⟨a.x, a.lo⟩, ⟨b.x, b.lo⟩, ⟨b.x, b.hi⟩, ⟨a.x, a.hi⟩]) items := rfl

theorem lowerShape_area (c : Color) (y0 : Rat) (items : List (Item Pt)) :
    lowerShape c (.area y0 items) =
      Item.fold
        (fun a => .stroke c hairline [⟨a.x, y0⟩, a])
        (fun a b => .fill c [⟨a.x, y0⟩, ⟨b.x, y0⟩, b, a]) items := rfl

theorem lowerShape_square (c : Color) (p : Pt) (r : Rat) :
    lowerShape c (.marker .square p r) =
      [.fill c [⟨p.x - r, p.y - r⟩, ⟨p.x + r, p.y - r⟩, ⟨p.x + r, p.y + r⟩, ⟨p.x - r, p.y + r⟩]] := rfl

theorem lowerShape_rect (c : Color) (b : Rect) :
    lowerShape c (.rect b) = [.fill c [⟨b.x0, b.y0⟩, ⟨b.x1, b.y0⟩, ⟨b.x1, b.y1⟩, ⟨b.x0, b.y1⟩]] := rfl

theorem lowerShape_circle (c : Color) (p : Pt) (r : Rat) :
    lowerShape c (.marker .circle p r) = [.disc c p r] := rfl

theorem lowerShape_text (c : Color) (b : Rect) (s : String) :
    lowerShape c (.text b s) = [.text c b s] := rfl

theorem lowerShape_clipped (c : Color) (b : Rect) (inner : Shape) :
    lowerShape c (.clipped b inner) = .clipBegin b :: lowerShape c inner ++ [.clipEnd] := rfl

end Inkproof.Export
