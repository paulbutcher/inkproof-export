/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Decimal

namespace Inkproof.Export

open Inkproof.Core.Decimal

/-- `q` rounded to three decimal places, without trailing zeros and without the point if no fraction is left. -/
def decimal (q : Rat) : String := String.ofList (trimZeros (formatDecimal 3 (roundScaled 3 q)))

private theorem trimFrac_getLast (f : List Char) : (trimFrac f).getLast? ≠ some '0' := by
  simp only [trimFrac, List.getLast?_reverse]
  generalize f.reverse = r
  induction r with
  | nil => simp
  | cons c t ih =>
    by_cases h : c = '0'
    · subst h; simpa using ih
    · simp [h]

private theorem digitsValue_append_zeros (l : List Char) (k : Nat) :
    digitsValue (l ++ List.replicate k '0') = digitsValue l * 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simp only [digitsValue, List.foldl_append] at ih ⊢
    rw [ih]
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10]

/-- The characters of `decimal q` are an optional minus sign, the whole digits, and if any fractional digits remain a point and at most three of them, the last not zero. The digits read as `q` rounded to thousandths, so trimming zeros does not change the value; and that value is within half a thousandth of `q`. -/
theorem decimal_spec (q : Rat) : ∃ (neg : Bool) (whole frac : List Char),
    (decimal q).toList = (if neg then ['-'] else []) ++ whole ++ (if frac = [] then [] else '.' :: frac) ∧
    whole ≠ [] ∧ frac.length ≤ 3 ∧ frac.getLast? ≠ some '0' ∧
    (∀ c ∈ whole ++ frac, c.isDigit = true) ∧
    (neg = true ↔ roundScaled 3 q < 0) ∧
    (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length = roundScaled 3 q / 1000 ∧
    q - 1 / 2000 ≤ (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length ∧
    (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length ≤ q + 1 / 2000 := by
  have hc : q - 1 / 2000 ≤ (roundScaled 3 q : Rat) / 1000 ∧ (roundScaled 3 q : Rat) / 1000 ≤ q + 1 / 2000 := by
    have h := roundScaled_close 3 q
    have e : ((10 ^ 3 : Nat) : Rat) = 1000 := by decide +kernel
    rw [e] at h
    constructor <;> grind
  obtain ⟨whole, frac0, hf, hw, hl, hd, hv⟩ := formatNat_spec 3 (roundScaled 3 q).natAbs
  obtain ⟨z, hz, hz0⟩ := trimFrac_prefix frac0
  have hzr : z = List.replicate z.length '0' := List.eq_replicate_iff.2 ⟨rfl, hz0⟩
  have hk : frac0 = trimFrac frac0 ++ List.replicate z.length '0' := by rw [← hzr]; exact hz
  have hlast := trimFrac_getLast frac0
  have hsplit : decimal q = String.ofList ((if roundScaled 3 q < 0 then ['-'] else []) ++ whole ++
      (if trimFrac frac0 = [] then [] else '.' :: trimFrac frac0)) := by
    have hnd : '.' ∉ (if roundScaled 3 q < 0 then ['-'] else []) ++ whole := by
      intro h
      simp only [List.mem_append] at h
      rcases h with h | h
      · by_cases hneg : roundScaled 3 q < 0 <;> simp [hneg] at h
      · have := hd '.' (by simp [h]); simp at this
    have e : formatDecimal 3 (roundScaled 3 q) = ((if roundScaled 3 q < 0 then ['-'] else []) ++ whole) ++ '.' :: frac0 := by
      rw [formatDecimal_spec, hf]; simp [List.append_assoc]
    have hsd : '.' ∉ (if roundScaled 3 q < 0 then ['-'] else []) ++ whole := hnd
    rw [decimal, e, trimZeros_spec _ _ hsd]
    by_cases h : trimFrac frac0 = [] <;> simp [h, List.append_assoc]
  generalize roundScaled 3 q = n at hsplit hc hv ⊢
  generalize trimFrac frac0 = t at hk hlast hsplit
  generalize z.length = k at hk
  have hlen : t.length + k = 3 := by
    have := congrArg List.length hk
    simp at this; omega
  have hdig : ∀ c ∈ whole ++ t, c.isDigit = true := by
    intro c hc
    apply hd
    rw [hk]
    simp only [List.mem_append] at hc ⊢
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  refine ⟨decide (n < 0), whole, t, ?_, hw, by omega, hlast, hdig, by simp, ?_⟩
  · rw [hsplit]; simp
  · have hV : (digitsValue (whole ++ t) : Rat) * 10 ^ k = n.natAbs := by
      have := hv
      rw [hk, ← List.append_assoc, digitsValue_append_zeros] at this
      exact_mod_cast this
    have hn : (n : Rat) = (if n < 0 then -1 else 1) * (n.natAbs : Rat) := by
      by_cases h : n < 0
      · have : n = -(n.natAbs : Int) := by omega
        simp only [h, ite_true]
        have h2 : n = -1 * (n.natAbs : Int) := by omega
        calc (n : Rat) = ((-1 * (n.natAbs : Int) : Int) : Rat) := by rw [← h2]
          _ = -1 * (n.natAbs : Rat) := by push_cast; rfl
      · have : n = (n.natAbs : Int) := by omega
        simp only [h, ite_false]
        have h2 : n = 1 * (n.natAbs : Int) := by omega
        calc (n : Rat) = ((1 * (n.natAbs : Int) : Int) : Rat) := by rw [← h2]
          _ = 1 * (n.natAbs : Rat) := by push_cast; rfl
    have h10 : (10 : Rat) ^ 3 = 10 ^ t.length * 10 ^ k := by
      have : (10 : Nat) ^ 3 = 10 ^ t.length * 10 ^ k := by rw [← Nat.pow_add, hlen]
      exact_mod_cast this
    have ha : (0 : Rat) < 10 ^ t.length := by exact_mod_cast Nat.pow_pos (by decide)
    have hb : (0 : Rat) < 10 ^ k := by exact_mod_cast Nat.pow_pos (by decide)
    have key : (if decide (n < 0) = true then (-1 : Rat) else 1) * (digitsValue (whole ++ t) : Rat) /
        10 ^ t.length = n / 1000 := by
      have h1000 : (1000 : Rat) = 10 ^ t.length * 10 ^ k := by rw [← h10]; decide +kernel
      rw [h1000, hn, ← hV]
      simp only [decide_eq_true_eq]
      grind
    rw [key]
    exact ⟨rfl, hc.1, hc.2⟩
