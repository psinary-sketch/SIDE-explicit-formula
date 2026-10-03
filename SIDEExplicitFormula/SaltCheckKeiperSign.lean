/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckKeiperSign.lean
THIS PROGRAMME'S WORK (act b602, ruling (R212)(3), H36a) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE SIGN OF λ_1, COMPILED. A sign that any bound on γ decided would say nothing about the bound used.

* **`coarse_lower_insufficient`** -- at Mathlib's coarse lower bound γ = 1/2 the closed form `1 + γ/2 − ½ log 4π` is
  negative: the coarse interval does not fix the sign, so the index of Mathlib's sequence is load-bearing.
* **`liCoeff_one_lt_tenth`** -- λ_1 < 1/10, from γ < 2/3 and log 4π > 2.52: the rung is placed two-sided, 0 < λ_1 < 1/10.
* **`liCoeff_one_pos_holds`** -- the sign, restated.

These are statements about Mathlib's γ, π, e and log at the pin and the kernel's `LiCoeff 1`, and nothing beyond them.
0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.KeiperSign

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperSign
namespace SaltCheck

/-- `log π ≥ 2 − e/π`, from `1 − 1/x ≤ log x` at `x = π / e`. -/
theorem log_pi_ge : 2 - Real.exp 1 / Real.pi ≤ Real.log Real.pi := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hq : 0 < Real.pi / Real.exp 1 := div_pos Real.pi_pos he
  have h := Real.one_sub_inv_le_log_of_pos hq
  rw [Real.log_div Real.pi_pos.ne' he.ne', Real.log_exp, inv_div] at h
  linarith

/-- `e / π < 0.8653`. -/
theorem e_div_pi_lt : Real.exp 1 / Real.pi < 0.8653 := by
  rw [div_lt_iff₀ Real.pi_pos]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.pi_gt_d4
  linarith

/-- `log 4π > 2.52`. -/
theorem log_four_pi_gt : 2.52 < Real.log (4 * Real.pi) := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have h1 := Real.log_two_gt_d9
  have h2 := log_pi_ge
  have h3 := e_div_pi_lt
  push_cast
  linarith

/-- **H36a, THE INDEX IS LOAD-BEARING**: at γ = 1/2 the closed form is negative. -/
theorem coarse_lower_insufficient : 1 + (1 / 2 : ℝ) / 2 - Real.log (4 * Real.pi) / 2 < 0 := by
  have := log_four_pi_gt
  linarith

/-- **H36a, THE RUNG PLACED TWO-SIDED**: λ_1 < 1/10. -/
theorem liCoeff_one_lt_tenth : LiWeil.LiCoeff 1 < 1 / 10 := by
  rw [Keiper.liCoeff_one_keiper]
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 := log_four_pi_gt
  linarith

/-- **H36a, THE SIGN**, restated. -/
theorem liCoeff_one_pos_holds : 0 < LiWeil.LiCoeff 1 := liCoeff_one_pos

end SaltCheck
end KeiperSign
end SIDEExplicitFormula
