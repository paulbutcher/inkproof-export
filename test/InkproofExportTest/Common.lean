/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Export

open Inkproof.Scene

namespace InkproofExportTest

def red : Color := ⟨255, 0, 0, 255⟩
def blue : Color := ⟨0, 0, 255, 255⟩
def bg : Color := ⟨255, 255, 255, 255⟩

def pt (x y : Rat) : Pt := ⟨x, y⟩

def count (s sub : String) : Nat := (s.splitOn sub).length - 1

/-- Where `sub` first occurs in `s`, as the length of the text before it. -/
def indexOf (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | before :: _ :: _ => some before.length
  | _ => none

/-- One command of every kind, the strip with a gap in it. -/
def everyKind : DisplayList := #[
  ⟨0, red, .strip 1 [.val (pt 1 1), .val (pt 3 2), .gap, .val (pt 5 4), .val (pt 6 5)]⟩,
  ⟨0, red, .envelope [.val ⟨1, 1, 3⟩, .val ⟨2, 0, 4⟩]⟩,
  ⟨0, red, .area 5 [.val (pt 1 2), .val (pt 2 3)]⟩,
  ⟨1, blue, .rect ⟨0, 0, 2, 2⟩⟩,
  ⟨1, blue, .marker .square (pt 4 4) 1⟩,
  ⟨1, blue, .marker .circle (pt 5 2) 1⟩,
  ⟨2, red, .text ⟨0, 4, 4, 6⟩ "a<b"⟩,
  ⟨2, blue, .clipped ⟨0, 0, 3, 3⟩ (.rect ⟨1, 1, 5, 5⟩)⟩]

end InkproofExportTest
