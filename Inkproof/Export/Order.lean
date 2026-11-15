/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Export.Lower

namespace Inkproof.Export

open Inkproof.Scene

/-- The commands in painting order: ascending layer, and list order within a layer. -/
def paintOrder (dl : DisplayList) : List Command :=
  dl.toList.mergeSort (fun a b => decide (a.layer ≤ b.layer))

theorem paintOrder_perm (dl : DisplayList) : (paintOrder dl).Perm dl.toList :=
  List.mergeSort_perm _ _

theorem paintOrder_sorted (dl : DisplayList) :
    (paintOrder dl).Pairwise (fun a b => a.layer ≤ b.layer) := by
  have := List.pairwise_mergeSort (le := fun a b : Command => decide (a.layer ≤ b.layer))
    (by intro a b c; simpa using Nat.le_trans) (by intro a b; simpa using Nat.le_total _ _) dl.toList
  simpa [paintOrder] using this

/-- The primitives that draw a display list, in painting order. -/
def lowerAll (dl : DisplayList) : List Prim :=
  (paintOrder dl).flatMap fun c => lowerShape c.color c.shape

theorem lowerAll_eq (dl : DisplayList) :
    lowerAll dl = (paintOrder dl).flatMap fun c => lowerShape c.color c.shape := rfl

end Inkproof.Export
