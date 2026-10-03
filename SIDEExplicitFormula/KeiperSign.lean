/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperSign.lean
THIS PROGRAMME'S WORK (act b602, ruling (R212)(3); the sign of λ_1, a finite rung of the Li ladder) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SIGN OF λ_1 AT T0. From the closed form `Keiper.liCoeff_one_keiper` (v0.19), `LiCoeff 1 = 1 + γ/2 − ½ log 4π`, so
`0 < LiCoeff 1` exactly when `γ > log 4π − 2` (≈ 0.5310; `liCoeff_one_pos_iff`). The lower bound on γ is Mathlib's: the
sequence `eulerMascheroniSeq n = harmonic n − log (n + 1)` lies below γ at every index
(`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`), and at the index 15 it is `1195757/360360 − 4 log 2` ≈ 0.54564
(`eulerMascheroniSeq_fifteen`), log 16 being four times Mathlib's `log 2 < 0.6931471808` (`Real.log_two_lt_d9`). The upper
bound on log 4π is `2 log 2 + log π` with `log π ≤ π / e` (from `Real.log_le_sub_one_of_pos` at π/e) and `π / e < 1.1558` from
`Real.pi_lt_d4` and `Real.exp_one_gt_d9`: log 4π < 2.5421 (`log_four_pi_lt`). The index 15 is the first whose `n + 1` is a
power of 2 above the threshold with the margin this upper bound needs (the first index above 0.5310 at all is 10, whose margin
is about 5·10⁻⁵). The salt-check is SIDEExplicitFormula/SaltCheckKeiperSign.lean.

THE CEILING: λ_1 > 0 is a known numerical fact and a single rung. It is not Li's criterion and says nothing about any λ_n
beyond n = 1; nothing here is a statement about the zeros of ζ beyond these theorems' own words.
-/
import SIDEExplicitFormula.Keiper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperSign

/-- **The threshold**: by the closed form at v0.19, `λ_1 > 0` exactly when `γ > log 4π − 2`. -/
theorem liCoeff_one_pos_iff :
    0 < LiWeil.LiCoeff 1 ↔ Real.log (4 * Real.pi) - 2 < Real.eulerMascheroniConstant := by
  rw [Keiper.liCoeff_one_keiper]
  constructor <;> intro h <;> linarith

/-- log 16 is four times log 2. -/
theorem log_sixteen : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num

/-- **Mathlib's lower sequence at the index 15**: `H_15 − log 16 = 1195757/360360 − 4 log 2`. -/
theorem eulerMascheroniSeq_fifteen : Real.eulerMascheroniSeq 15 = 1195757 / 360360 - 4 * Real.log 2 := by
  rw [Real.eulerMascheroniSeq, ← log_sixteen]
  norm_num

/-- **The lower bound on γ**, from Mathlib's sequence at 15. -/
theorem gamma_gt_seq_fifteen : 1195757 / 360360 - 4 * Real.log 2 < Real.eulerMascheroniConstant := by
  rw [← eulerMascheroniSeq_fifteen]
  exact Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15

/-- `log π ≤ π / e`, from `log x ≤ x − 1` at `x = π / e`. -/
theorem log_pi_le_pi_div_e : Real.log Real.pi ≤ Real.pi / Real.exp 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hq : 0 < Real.pi / Real.exp 1 := div_pos Real.pi_pos he
  have h := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div Real.pi_pos.ne' he.ne', Real.log_exp] at h
  linarith

/-- `π / e < 1.1558`, from `π < 3.1416` and `e > 2.7182818283`. -/
theorem pi_div_e_lt : Real.pi / Real.exp 1 < 1.1558 := by
  rw [div_lt_iff₀ (Real.exp_pos 1)]
  have h1 := Real.pi_lt_d4
  have h2 := Real.exp_one_gt_d9
  linarith

/-- **The upper bound on log 4π**: `log 4π < 2.5421`. -/
theorem log_four_pi_lt : Real.log (4 * Real.pi) < 2.5421 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have h1 := Real.log_two_lt_d9
  have h2 := log_pi_le_pi_div_e
  have h3 := pi_div_e_lt
  push_cast
  linarith

/-- **γ exceeds the threshold.** -/
theorem threshold_lt_gamma : Real.log (4 * Real.pi) - 2 < Real.eulerMascheroniConstant := by
  have h1 := log_four_pi_lt
  have h2 := gamma_gt_seq_fifteen
  have h3 := Real.log_two_lt_d9
  linarith

/-- **THE SIGN OF λ_1, AT T0**: the programme's Li coefficient at 1 is positive. A single rung; not Li's criterion. -/
theorem liCoeff_one_pos : 0 < LiWeil.LiCoeff 1 :=
  liCoeff_one_pos_iff.mpr threshold_lt_gamma

end KeiperSign
end SIDEExplicitFormula
