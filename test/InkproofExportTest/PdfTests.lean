/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofExportTest.Common
import InkproofTools.Test.Harness

open Inkproof.Scene Inkproof.Export InkproofTools.Test

namespace InkproofExportTest

def text (b : ByteArray) : String := (String.fromUTF8? b).getD ""

/-- The byte offsets in the cross-reference table, in object order. -/
def xrefOffsets (s : String) : List Nat :=
  match s.splitOn "xref\n0 " with
  | _ :: tail :: _ =>
    let lines := (tail.splitOn "\n").drop 2
    (lines.filter (·.endsWith " 00000 n ")).filterMap fun l => (l.take 10).toNat?
  | _ => []

def pdfTests : List TestCase := [
  .mk "the page has the grid's extents and the file is framed" do
    let s := text (pdf #[] 8 6)
    check (count s "/MediaBox [0 0 8 6]" == 1) "wrong page size"
    check (s.startsWith "%PDF-" && s.endsWith "%%EOF\n") "not framed",
  .mk "each cross-reference entry points at its object" do
    let b := pdf everyKind 8 6
    let offs := xrefOffsets (text b)
    check (offs.length == 5) "expected five objects"
    for (o, i) in offs.zipIdx do
      let tag := s!"{i + 1} 0 obj\n"
      check (text (b.extract o (o + tag.length)) == tag) s!"object {i + 1} not at its offset"
    let startxref := (((text b).splitOn "startxref\n").getD 1 "").takeWhile Char.isDigit
    check ((startxref.toNat?.map fun o => text (b.extract o (o + 4))) == some "xref") "startxref wrong",
  .mk "saves and restores balance across every command kind" do
    let s := text (pdf everyKind 8 6)
    let tokens := (s.split Char.isWhitespace).toList.map (·.copy)
    check (tokens.count "q" == tokens.count "Q") "unbalanced graphics state"
    check (tokens.count "BT" == 1 && tokens.count "re" == 1) "text or clip missing",
  .mk "a gap splits a strip into separate paths" do
    let s := text (pdf #[⟨0, red, .strip 1 [.val (pt 1 1), .val (pt 3 2), .gap, .val (pt 5 4), .val (pt 6 5)]⟩] 8 6)
    check (count s " S Q" == 2) "two strokes expected",
  .mk "layers paint in ascending order" do
    let s := text (pdf #[⟨2, blue, .rect ⟨0, 0, 1, 1⟩⟩, ⟨1, red, .rect ⟨2, 2, 3, 3⟩⟩] 4 4)
    match indexOf s "1 0 0 rg", indexOf s "0 0 1 rg" with
    | some r, some b => check (r < b) "layer 1 must precede layer 2"
    | _, _ => throw "missing colour",
  .mk "partial alpha declares a graphics state that the page resources carry" do
    let s := text (pdf #[⟨0, ⟨0, 0, 0, 128⟩, .rect ⟨0, 0, 1, 1⟩⟩] 4 4)
    check (count s "/G128 gs" == 1 && count s "/G128 <<" == 1) "alpha state missing"
]

end InkproofExportTest
