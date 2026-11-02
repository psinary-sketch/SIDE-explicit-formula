/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Growth.lean
THIS PROGRAMME'S WORK (act b733, ruling (R343)(3), relay data/b733_count_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE BOUNDS OF THE count FIELD. On `Re s ≥ 3/2` the series is within `Z_Q(3/2) − 2` of its first term `2`, so `|Z_Q(s)| ≤ Z_Q(3/2)` and `|Z_Q(s)| ≥ 4 − Z_Q(3/2)`, the lower
bound at the centre, which needs no Euler product and rests on `Z_Q(3/2) < 4` alone. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Zeros

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-! ### The lower bound at the centre -/

/-- `Z_Q(3/2)`, the real sum. -/
def totQ : ℝ := ∑' k, wQ k

theorem totQ_lt : totQ < 4 := zq_three_halves_tsum_lt

theorem totQ_nonneg : 0 ≤ totQ := tsum_nonneg wQ_nonneg

theorem norm_two_eq : ‖(2 : ℂ)‖ = 2 := by
  first
    | norm_num
    | simpa using Complex.norm_natCast 2

/-- `|Z_Q(s) − 2| ≤ Z_Q(3/2) − 2` on `Re s ≥ 3/2`. -/
theorem zq_sub_two_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖zqFn s - 2‖ ≤ totQ - 2 := by
  have hs1 : 1 < s.re := by linarith
  have h1 : LSeriesSummable aQ s := zq_summable s hs1
  have hone : LSeries.term aQ s 1 = 2 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    show ((rQ 1 : ℕ) : ℂ) / ((1 : ℕ) : ℂ) ^ s = 2
    rw [rQ_one, Nat.cast_one, Complex.one_cpow]
    norm_num
  have h2 : HasSum (LSeries.term aQ s) (LSeries aQ s) := Summable.hasSum h1
  have hE : HasSum (fun k => LSeries.term aQ s k - if k = 1 then (2 : ℂ) else 0) (LSeries aQ s - 2) :=
    h2.sub (hasSum_ite_eq (1 : ℕ) (2 : ℂ))
  have hG : HasSum (fun k => wQ k - if k = 1 then (2 : ℝ) else 0) (∑' k, wQ k - 2) :=
    wQ_summable.hasSum.sub (hasSum_ite_eq (1 : ℕ) (2 : ℝ))
  have hb : ∀ k, ‖LSeries.term aQ s k - if k = 1 then (2 : ℂ) else 0‖ ≤ wQ k - if k = 1 then (2 : ℝ) else 0 := by
    intro k
    by_cases hk : k = 1
    · subst hk
      refine le_of_eq ?_
      rw [if_pos rfl, if_pos rfl, hone, sub_self, norm_zero, wQ_one, sub_self]
    · rw [if_neg hk, if_neg hk, sub_zero, sub_zero, LSeries.norm_term_eq]
      by_cases h0 : k = 0
      · rw [if_pos h0]
        exact wQ_nonneg k
      · rw [if_neg h0]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        have hp : (k : ℝ) ^ (3 / 2 : ℝ) ≤ (k : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hk1 hs
        have hq : 0 < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
        show ‖((rQ k : ℕ) : ℂ)‖ / (k : ℝ) ^ s.re ≤ (rQ k : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)
        rw [Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hq hp
  have hn : ‖LSeries aQ s - 2‖ ≤ ∑' k, wQ k - 2 := by
    rw [← hE.tsum_eq]
    exact tsum_of_norm_bounded hG hb
  have h4 : zqFn s = LSeries aQ s := zqFn_agrees s hs1
  rw [h4]
  exact hn

/-- `|Z_Q(s)| ≤ Z_Q(3/2)` on `Re s ≥ 3/2`. -/
theorem zq_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖zqFn s‖ ≤ totQ := by
  have h := zq_sub_two_le hs
  have h3 : ‖zqFn s‖ ≤ ‖zqFn s - 2‖ + ‖(2 : ℂ)‖ := by
    calc ‖zqFn s‖ = ‖(zqFn s - 2) + 2‖ := by rw [sub_add_cancel]
      _ ≤ ‖zqFn s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
  rw [norm_two_eq] at h3
  linarith

/-- **THE LOWER BOUND AT THE CENTRE**: `|Z_Q(s)| ≥ 4 − Z_Q(3/2)` on `Re s ≥ 3/2`. -/
theorem zq_norm_ge {s : ℂ} (hs : 3 / 2 ≤ s.re) : 4 - totQ ≤ ‖zqFn s‖ := by
  have h := zq_sub_two_le hs
  have h3 : ‖(2 : ℂ)‖ ≤ ‖zqFn s - 2‖ + ‖zqFn s‖ := by
    calc ‖(2 : ℂ)‖ = ‖(2 - zqFn s) + zqFn s‖ := by rw [sub_add_cancel]
      _ ≤ ‖2 - zqFn s‖ + ‖zqFn s‖ := norm_add_le _ _
      _ = ‖zqFn s - 2‖ + ‖zqFn s‖ := by rw [norm_sub_rev]
  rw [norm_two_eq] at h3
  linarith

/-- `totQ` is `Z_Q(3/2)`: the bound reads `4 − Z_Q(3/2)`. -/
theorem zq_three_halves_eq : zqFn ((3 / 2 : ℝ) : ℂ) = (totQ : ℂ) := by
  have hs1 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have h4 : zqFn ((3 / 2 : ℝ) : ℂ) = LSeries aQ ((3 / 2 : ℝ) : ℂ) := zqFn_agrees _ hs1
  rw [h4]
  unfold LSeries totQ
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    have h0 : wQ 0 = 0 := by
      unfold wQ
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
    rw [LSeries.term_zero, h0, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn]
    show ((rQ n : ℕ) : ℂ) / (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ)) = ((wQ n : ℝ) : ℂ)
    unfold wQ
    rw [Complex.ofReal_div (rQ n : ℝ), Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

end ZQ
end Schema
end SIDEExplicitFormula
