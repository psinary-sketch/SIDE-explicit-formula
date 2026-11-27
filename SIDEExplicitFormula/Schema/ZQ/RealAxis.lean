/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/RealAxis.lean
THIS PROGRAMME'S WORK (act b770, the author's word amending ruling (R380)(4), its (4)(g); relay data/b770_plan.txt (4)(g)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

NO ZERO OF THE CONTROL ON THE REAL AXIS BEYOND 1. For real `x > 1` the control's value at `x` is not zero
(`zq_ne_zero_of_real_one_lt`): by `zqFn_agrees` (Continuation.lean :138) it is the Dirichlet series `∑ r_Q(n) n^(-x)`, which is the
real series `∑ r_Q(n) / n^x` read in ℂ, as `zq_three_halves_eq` (Growth.lean :94-:113) reads it at `3/2`; that real series is summable
(`rQ_term_summable`, Lattice.lean :228, the series `zq_summable` is proved from), each of its terms is at least `0`, and its term at
`n = 1` is `r_Q(1) = 2` (`rQ_one`, LogDeriv.lean :56), so its sum is at least `2`. `zq_ne_zero_of_three_halves_le` (LogDeriv.lean :341)
stands beside it.
-/
import SIDEExplicitFormula.Schema.ZQ.Continuation
import SIDEExplicitFormula.Schema.ZQ.LogDeriv

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- **No zero of the control on the real axis beyond `1`**: `zqFn x ≠ 0` for real `x > 1`. -/
theorem zq_ne_zero_of_real_one_lt (x : ℝ) (hx : 1 < x) : zqFn (x : ℂ) ≠ 0 := by
  have hs1 : 1 < ((x : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hx
  have h4 : zqFn (x : ℂ) = LSeries (fun k => (rQ k : ℂ)) (x : ℂ) := zqFn_agrees _ hs1
  have hsum : LSeries (fun k => (rQ k : ℂ)) (x : ℂ) = ((∑' n : ℕ, (rQ n : ℝ) / (n : ℝ) ^ x : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    by_cases hn : n = 0
    · subst hn
      rw [LSeries.term_zero, Nat.cast_zero, Real.zero_rpow (show (0 : ℝ) < x by linarith).ne', div_zero,
        Complex.ofReal_zero]
    · rw [LSeries.term_of_ne_zero hn]
      show ((rQ n : ℕ) : ℂ) / (n : ℂ) ^ (x : ℂ) = (((rQ n : ℝ) / (n : ℝ) ^ x : ℝ) : ℂ)
      rw [Complex.ofReal_div (rQ n : ℝ), Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
  have hnn : ∀ n : ℕ, 0 ≤ (rQ n : ℝ) / (n : ℝ) ^ x := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) x)
  have h1 : (rQ 1 : ℝ) / ((1 : ℕ) : ℝ) ^ x = 2 := by
    rw [rQ_one, Nat.cast_one, Real.one_rpow]
    norm_num
  have hge : (2 : ℝ) ≤ ∑' n : ℕ, (rQ n : ℝ) / (n : ℝ) ^ x :=
    calc (2 : ℝ) = (rQ 1 : ℝ) / ((1 : ℕ) : ℝ) ^ x := h1.symm
      _ ≤ ∑' n : ℕ, (rQ n : ℝ) / (n : ℝ) ^ x := (rQ_term_summable hx).le_tsum 1 (fun j _ => hnn j)
  have hpos : (0 : ℝ) < ∑' n : ℕ, (rQ n : ℝ) / (n : ℝ) ^ x := by linarith
  rw [h4, hsum]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

end ZQ
end Schema
end SIDEExplicitFormula
