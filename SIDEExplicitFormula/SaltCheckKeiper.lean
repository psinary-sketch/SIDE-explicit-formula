/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckKeiper.lean
THIS PROGRAMME'S WORK (act b601, ruling (R211)(4), H35c) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE KEIPER FACE'S TWO LEMMAS, COMPILED. An identity that held for any summands, or a bound that held for
any table, would say nothing beyond its form.

* LEMMA (1), `Keiper.KeiperTaylor`: **`keiperTaylor_zero_holds`** -- the identity holds at `n = 0`; and each of the three
  summands of Keiper's coefficient is load-bearing there: dropping 1/s (**`split_needs_inv_s`**), the logarithmic
  derivative of (s − 1) ζ(s) (**`split_needs_zeta`**) or that of Γℝ (**`split_needs_gammaR`**) breaks the split at
  `k = 0`.
* LEMMA (2), `KeiperBounds.KeiperBounds`: **`bounds_form_satisfiable`** -- the interval form holds for γ_0 at Mathlib's
  interval; **`bounds_form_refutable`** -- it fails for γ_0 at the interval [1, 2]: the form is decided by the table, not
  by its shape.

These are statements about Mathlib's `riemannZeta`, `Gammaℝ` and γ at `s = 1` and nothing beyond them; nothing here is a
statement about the zeros of ζ. 0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.KeiperBounds

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Keiper
namespace SaltCheck

open KeiperBounds

theorem gamma_pos : (0 : ℝ) < Real.eulerMascheroniConstant :=
  lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant

theorem log_four_pi_pos : (0 : ℝ) < Real.log (4 * Real.pi) :=
  Real.log_pos (by linarith [Real.pi_gt_three])

/-- **H35c, LEMMA (1) AT `n = 0`**: the identity holds. -/
theorem keiperTaylor_zero_holds : LiCriterion.taylorCoeff LiCriterion.riemannXi 0 = keiperSum 0 :=
  keiperTaylor_zero

/-- **H35c, THE 1/s TERM IS LOAD-BEARING**: without it the split fails at `k = 0`. -/
theorem split_needs_inv_s : xiLogCoeff 0 ≠ zetaLogCoeff 0 + gammaRLogCoeff 0 := fun h => by
  have h0 := logDerivSplit_zero
  rw [keiperA, pow_zero] at h0
  have h1 : (1 : ℂ) = 0 := by linear_combination h - h0
  exact one_ne_zero h1

/-- **H35c, THE TERM OF (s − 1) ζ(s) IS LOAD-BEARING**: without it the split fails at `k = 0` (γ ≠ 0). -/
theorem split_needs_zeta : xiLogCoeff 0 ≠ (-1) ^ 0 + gammaRLogCoeff 0 := fun h => by
  have h0 := logDerivSplit_zero
  rw [keiperA] at h0
  have hz : zetaLogCoeff 0 = 0 := by linear_combination h - h0
  rw [zetaLogCoeff_zero, stieltjes_zero] at hz
  exact (ne_of_gt gamma_pos) (Complex.ofReal_eq_zero.mp hz)

/-- **H35c, THE TERM OF Γℝ IS LOAD-BEARING**: without it the split fails at `k = 0` (γ + log 4π ≠ 0). -/
theorem split_needs_gammaR : xiLogCoeff 0 ≠ (-1) ^ 0 + zetaLogCoeff 0 := fun h => by
  have h0 := logDerivSplit_zero
  rw [keiperA] at h0
  have hg : gammaRLogCoeff 0 = 0 := by linear_combination h - h0
  rw [gammaRLogCoeff_zero, log_four_pi_ofReal] at hg
  have hr : (-(Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) / 2 : ℝ) = 0 := by
    exact_mod_cast hg
  linarith [gamma_pos, log_four_pi_pos]

/-- **H35c, LEMMA (2), THE FORM SATISFIABLE**: γ_0 in Mathlib's interval. -/
theorem bounds_form_satisfiable : InInterval (1 / 2) (2 / 3) (stieltjes 0) :=
  stieltjes_zero_coarse

/-- **H35c, LEMMA (2), THE FORM REFUTABLE**: γ_0 is not in [1, 2]. -/
theorem bounds_form_refutable : ¬ InInterval 1 2 (stieltjes 0) := fun h => by
  unfold InInterval at h
  obtain ⟨h1, -, -⟩ := h
  rw [stieltjes_zero, Complex.ofReal_re] at h1
  have h2 := Real.eulerMascheroniConstant_lt_two_thirds
  push_cast at h1
  linarith

end SaltCheck
end Keiper
end SIDEExplicitFormula
