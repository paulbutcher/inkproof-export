/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Decimal

namespace Inkproof.Export

open Inkproof.Core.Decimal

/-- `q` rounded to thousandths, as a whole number of thousandths. -/
def thousandths (q : Rat) : Int := (q * 1000 + 1 / 2).floor

/-- The fractional digits without their trailing zeros. -/
def trimZeros (frac : List Char) : List Char := (frac.reverse.dropWhile (· == '0')).reverse

/-- `q` rounded to three decimal places, without trailing zeros and without the point if no fraction is left. -/
def decimal (q : Rat) : String :=
  match splitAtChar '.' (formatDecimal 3 (thousandths q)) with
  | (whole, some frac) => String.ofList (whole ++ (if trimZeros frac = [] then [] else '.' :: trimZeros frac))
  | (whole, none) => String.ofList whole

theorem thousandths_close (q : Rat) :
    q - 1 / 2000 ≤ (thousandths q : Rat) / 1000 ∧ (thousandths q : Rat) / 1000 ≤ q + 1 / 2000 := by
  have h1 := Rat.floor_le (q * 1000 + 1 / 2)
  have h2 := Rat.lt_floor_add_one (q * 1000 + 1 / 2)
  unfold thousandths
  constructor <;> grind

theorem trimZeros_spec (frac : List Char) :
    ∃ k, frac = trimZeros frac ++ List.replicate k '0' ∧ (trimZeros frac).getLast? ≠ some '0' := by
  have pre : ∀ r : List Char, ∃ k, r = List.replicate k '0' ++ r.dropWhile (· == '0') := by
    intro r
    induction r with
    | nil => exact ⟨0, rfl⟩
    | cons c t ih =>
      by_cases h : c = '0'
      · obtain ⟨k, hk⟩ := ih
        subst h
        have e : ('0' :: t).dropWhile (· == '0') = t.dropWhile (· == '0') := by simp
        exact ⟨k + 1, by rw [e, List.replicate_succ, List.cons_append, ← hk]⟩
      · exact ⟨0, by simp [h]⟩
  obtain ⟨k, hk⟩ := pre frac.reverse
  refine ⟨k, ?_, ?_⟩
  · have := congrArg List.reverse hk
    simpa [trimZeros] using this
  · simp only [trimZeros, List.getLast?_reverse]
    generalize frac.reverse = r
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
    (neg = true ↔ thousandths q < 0) ∧
    (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length = thousandths q / 1000 ∧
    q - 1 / 2000 ≤ (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length ∧
    (if neg then -1 else 1) * (digitsValue (whole ++ frac) : Rat) / 10 ^ frac.length ≤ q + 1 / 2000 := by
  have hc := thousandths_close q
  obtain ⟨whole, frac0, hf, hw, hl, hd, hv⟩ := formatNat_spec 3 (thousandths q).natAbs
  obtain ⟨k, hk, hlast⟩ := trimZeros_spec frac0
  have hsplit : decimal q = String.ofList ((if thousandths q < 0 then ['-'] else []) ++ whole ++
      (if trimZeros frac0 = [] then [] else '.' :: trimZeros frac0)) := by
    have hnd : '.' ∉ (if thousandths q < 0 then ['-'] else []) ++ whole := by
      intro h
      simp only [List.mem_append] at h
      rcases h with h | h
      · by_cases hneg : thousandths q < 0 <;> simp [hneg] at h
      · have := hd '.' (by simp [h]); simp at this
    have e : formatDecimal 3 (thousandths q) = ((if thousandths q < 0 then ['-'] else []) ++ whole) ++ '.' :: frac0 := by
      rw [formatDecimal_spec, hf]; simp [List.append_assoc]
    rw [decimal, e, splitAtChar_some _ _ _ hnd]
  generalize thousandths q = n at hsplit hc hv ⊢
  generalize trimZeros frac0 = t at hk hlast hsplit
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
