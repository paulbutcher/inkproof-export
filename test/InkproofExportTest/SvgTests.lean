/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofExportTest.Common
import InkproofTools.Test.Harness

open Inkproof.Scene Inkproof.Export InkproofTools.Test

namespace InkproofExportTest

def svgTests : List TestCase := [
  .mk "the canvas has the grid's extents" do
    let s := svg #[] 8 6
    check (count s "width=\"8\" height=\"6\" viewBox=\"0 0 8 6\"" == 1) "wrong extents",
  .mk "every command kind draws, and a gap splits a strip" do
    let s := svg everyKind 8 6
    check (count s "<polyline" == 6) "two strip runs, and a line for each envelope and area column"
    check (count s "<polygon" == 5) "envelope and area pair, rectangle, square marker and clipped rectangle"
    check (count s "<circle" == 1) "circle marker"
    check (count s "<text" == 1) "text"
    check (count s "<clipPath" == 1 && count s "<g " == count s "</g>") "clip is not balanced",
  .mk "a lone envelope column is drawn as a line" do
    let s := svg #[⟨0, red, .envelope [.val ⟨1, 1, 3⟩]⟩] 4 4
    check (count s "<polyline" == 1) "column missing",
  .mk "layers paint in ascending order whatever the list order" do
    let s := svg #[⟨2, blue, .rect ⟨0, 0, 1, 1⟩⟩, ⟨1, red, .rect ⟨2, 2, 3, 3⟩⟩] 4 4
    match indexOf s "#ff0000", indexOf s "#0000ff" with
    | some r, some b => check (r < b) "layer 1 must precede layer 2"
    | _, _ => throw "missing colour",
  .mk "equal layers keep list order" do
    let s := svg #[⟨1, blue, .rect ⟨0, 0, 1, 1⟩⟩, ⟨1, red, .rect ⟨2, 2, 3, 3⟩⟩] 4 4
    match indexOf s "#ff0000", indexOf s "#0000ff" with
    | some r, some b => check (b < r) "list order lost"
    | _, _ => throw "missing colour",
  .mk "text is escaped and partial alpha becomes an opacity" do
    let s := svg #[⟨0, ⟨0, 0, 0, 128⟩, .text ⟨0, 0, 4, 2⟩ "a<b&c"⟩] 4 4
    check (count s "a&lt;b&amp;c" == 1) "not escaped"
    check (count s "fill-opacity=\"0.502\"" == 1) "opacity missing",
  .mk "coordinates are rounded to three places" do
    let s := svg #[⟨0, red, .rect ⟨1 / 3, 0, 2, 1⟩⟩] 4 4
    check (count s "0.333,0" == 1) "wrong rounding"
]

end InkproofExportTest
