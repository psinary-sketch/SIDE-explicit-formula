/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperTwo.lean
THIS PROGRAMME'S WORK (act b725, ruling (R335)(3)(iii) and (4)(iii); branch keiper-b725, no main, no tag) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SECOND LI COEFFICIENT IN γ, γ_1, log 4π AND π², AND ITS SIGN FROM TWO NAMED PREMISES. Bulka's first Taylor coefficient of ξ
is `2 keiperA 0 + keiperA 1` by (O1) and (O2) as KeiperIdentities.lean proves them (`taylorCoeff_xi_one`); (O3) at `k = 1` reads
`zetaLogCoeff 1 = −2 γ_1 − γ²` (`zetaLogCoeff_one`); with (O4) at its first index -- Γℝ's second log-derivative coefficient at 1
is `(3/4) ζ(2)`, i.e. ψ'(1/2) = π²/2 -- carried as the Prop `GammaRZetaOne`, the closed form is
`LiCoeff 2 = 1 + γ − log 4π − γ² − 2 Re γ_1 + π²/8` (`liCoeff_two_keiper`). The sign follows from that premise and
`Re γ_1 < −1/20` (`liCoeff_two_pos_of`), by γ in (0.5456, 2/3) (Mathlib's sequence at 15, as KeiperSign.lean reads it, and
`Real.eulerMascheroniConstant_lt_two_thirds`), log 4π < 2.5421 (`KeiperSign.log_four_pi_lt`) and π > 3.1415: the margin at those
bounds is 1 + 2/9 − 2.5421 + 9.86902225/8 + 1/10 ≈ 0.0138.

THE CEILING: neither premise is proved here. Mathlib at the pin holds no derivative of digamma (relay data/b641_keiper_status.txt,
(K4)) and names no Stieltjes constant past γ ((B2)); `GammaRZetaOne` and the bound on `Re γ_1` are named premises, and nothing here
assumes a value of γ_1. λ_2 > 0 is a single rung and a known numerical fact; it is not Li's criterion and says nothing about any
λ_n beyond n = 2 or about the zeros of ζ beyond these theorems' own words.
-/
import SIDEExplicitFormula.KeiperIdentities
import SIDEExplicitFormula.KeiperSign
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperTwo

open Keiper

/-- **(O4) AT ITS FIRST INDEX, AS A PROP**: Γℝ's second log-derivative coefficient at 1 is `(3/4) ζ(2)` (ψ'(1/2) = π²/2). -/
def GammaRZetaOne : Prop := gammaRLogCoeff 1 = 3 / 4 * riemannZeta 2

/-- **(O4) gives it**: `GammaRZetaValues` at `k = 0`. -/
theorem gammaRZetaOne_of (h : GammaRZetaValues) : GammaRZetaOne := by
  have h0 := h 0
  unfold GammaRZetaOne
  first
  | (rw [h0]; norm_num; trace "ALT gammaRZetaOne_of 1")
  | (norm_num at h0 ⊢; exact h0; trace "ALT gammaRZetaOne_of 2")
  | (simp at h0 ⊢; rw [h0]; norm_num; trace "ALT gammaRZetaOne_of 3")
  | (trace "ALT gammaRZetaOne_of SORRY"; sorry)

/-- **(O3) at `k = 1`**: `zetaLogCoeff 1 = −2 γ_1 − γ_0²`, from `stieltjesLog_holds 1`. -/
theorem zetaLogCoeff_one : zetaLogCoeff 1 = -2 * stieltjes 1 - stieltjes 0 ^ 2 := by
  have h := stieltjesLog_holds 1
  have p0 : poleCoeff 0 = 1 := rfl
  have p1 : poleCoeff 1 = stieltjes 0 := by
    first
    | (simp [poleCoeff]; trace "ALT p1 1")
    | (show (-1 : ℂ) ^ 0 * stieltjes 0 / ((Nat.factorial 0 : ℕ) : ℂ) = stieltjes 0; simp; trace "ALT p1 2")
    | (trace "ALT p1 SORRY"; sorry)
  have p2 : poleCoeff 2 = -stieltjes 1 := by
    first
    | (simp [poleCoeff]; trace "ALT p2 1")
    | (show (-1 : ℂ) ^ 1 * stieltjes 1 / ((Nat.factorial 1 : ℕ) : ℂ) = -stieltjes 1; simp; trace "ALT p2 2")
    | (trace "ALT p2 SORRY"; sorry)
  have h' : (2 : ℂ) * poleCoeff 2 = poleCoeff 0 * zetaLogCoeff 1 + poleCoeff 1 * zetaLogCoeff 0 := by
    first
    | (simpa [Finset.sum_range_succ] using h; trace "ALT h' 1")
    | (rw [Finset.sum_range_succ, Finset.sum_range_one] at h; norm_num at h ⊢; exact h; trace "ALT h' 2")
    | (convert h using 1 <;> simp [Finset.sum_range_succ]; trace "ALT h' 3")
    | (trace "ALT h' SORRY"; sorry)
  first
  | (rw [p0, p1, p2, zetaLogCoeff_zero] at h'; linear_combination (-1 : ℂ) * h'; trace "ALT zetaLogCoeff_one 1")
  | (rw [p0, p1, p2, zetaLogCoeff_zero] at h'; linear_combination h'; trace "ALT zetaLogCoeff_one 2")
  | (trace "ALT zetaLogCoeff_one SORRY"; sorry)

/-- **Bulka's first coefficient**: `2 keiperA 0 + keiperA 1`, by (O1) and (O2) as KeiperIdentities.lean proves them. -/
theorem taylorCoeff_xi_one :
    LiCriterion.taylorCoeff LiCriterion.riemannXi 1 = 2 * keiperA 0 + keiperA 1 := by
  have hb := binomialTransform_holds 1
  have hs : ∀ k : ℕ, xiLogCoeff k = keiperA k := logDerivSplit_holds
  first
  | (rw [hb]; simp [Finset.sum_range_succ, hs]; trace "ALT taylorCoeff_xi_one 1")
  | (rw [hb]; simp [Finset.sum_range_succ, hs]; ring; trace "ALT taylorCoeff_xi_one 2")
  | (rw [hb]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, hs]; norm_num; trace "ALT taylorCoeff_xi_one 3")
  | (rw [hb]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, hs]; norm_num; ring; trace "ALT taylorCoeff_xi_one 4")
  | (trace "ALT taylorCoeff_xi_one SORRY"; sorry)

/-- **KEIPER'S λ_2, IN γ, γ_1, log 4π AND π², ON (O4) AT ITS FIRST INDEX**:
`LiCoeff 2 = 1 + γ − log 4π − γ² − 2 Re γ_1 + π²/8`. -/
theorem liCoeff_two_keiper (h4 : GammaRZetaOne) :
    LiWeil.LiCoeff 2 = 1 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)
      - Real.eulerMascheroniConstant ^ 2 - 2 * (stieltjes 1).re + Real.pi ^ 2 / 8 := by
  have h4' : gammaRLogCoeff 1 = 3 / 4 * riemannZeta 2 := h4
  have h : LiWeil.LiCoeff 2 = (LiCriterion.taylorCoeff LiCriterion.riemannXi 1).re :=
    LiCriterionBridge.li_coeff_eq_taylorCoeff 1
  have hc : LiCriterion.taylorCoeff LiCriterion.riemannXi 1
      = ((1 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) - Real.eulerMascheroniConstant ^ 2
          + Real.pi ^ 2 / 8 : ℝ) : ℂ) - 2 * stieltjes 1 := by
    first
    | (rw [taylorCoeff_xi_one, keiperA_zero, keiperA, zetaLogCoeff_one, h4', riemannZeta_two, stieltjes_zero,
        log_four_pi_ofReal]; push_cast; ring; trace "ALT hc 1")
    | (rw [taylorCoeff_xi_one, keiperA_zero, keiperA, zetaLogCoeff_one, h4', riemannZeta_two, stieltjes_zero,
        log_four_pi_ofReal]; simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
        Complex.ofReal_div, Complex.ofReal_ofNat]; ring; trace "ALT hc 2")
    | (simp only [taylorCoeff_xi_one, keiperA_zero, keiperA, zetaLogCoeff_one, h4', riemannZeta_two, stieltjes_zero,
        log_four_pi_ofReal]; push_cast; ring; trace "ALT hc 3")
    | (trace "ALT hc SORRY"; sorry)
  first
  | (rw [h, hc]; simp; ring; trace "ALT liCoeff_two_keiper 1")
  | (rw [h, hc]; simp; trace "ALT liCoeff_two_keiper 2")
  | (rw [h, hc]; simp; linarith; trace "ALT liCoeff_two_keiper 3")
  | (rw [h, hc, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]; norm_num; ring; trace "ALT liCoeff_two_keiper 4")
  | (trace "ALT liCoeff_two_keiper SORRY"; sorry)

/-- **THE SIGN OF λ_2, ON TWO NAMED PREMISES**: (O4) at its first index and `Re γ_1 < −1/20`. A single rung; not Li's
criterion. -/
theorem liCoeff_two_pos_of (h4 : GammaRZetaOne) (h1 : (stieltjes 1).re < -1 / 20) : 0 < LiWeil.LiCoeff 2 := by
  rw [liCoeff_two_keiper h4]
  have hg1 := KeiperSign.gamma_gt_seq_fifteen
  have hl2 := Real.log_two_lt_d9
  have hg2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog := KeiperSign.log_four_pi_lt
  have hpi := Real.pi_gt_d4
  have hA : (1 : ℝ) / 3 < Real.eulerMascheroniConstant := by
    first
    | (linarith; trace "ALT hA 1")
    | (norm_num at hg1 hl2 ⊢; linarith; trace "ALT hA 2")
    | (trace "ALT hA SORRY"; sorry)
  have hgg : Real.eulerMascheroniConstant ^ 2 ≤ Real.eulerMascheroniConstant - 2 / 9 := by
    first
    | (nlinarith [mul_pos (sub_pos.2 hA) (sub_pos.2 hg2)]; trace "ALT hgg 1")
    | (have hm := mul_pos (sub_pos.2 hA) (sub_pos.2 hg2); nlinarith [hm]; trace "ALT hgg 2")
    | (trace "ALT hgg SORRY"; sorry)
  have hpi2 : (9.86902225 : ℝ) < Real.pi ^ 2 := by
    first
    | (nlinarith [hpi, Real.pi_pos]; trace "ALT hpi2 1")
    | (have hs : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := (by gcongr); norm_num at hs; linarith; trace "ALT hpi2 2")
    | (trace "ALT hpi2 SORRY"; sorry)
  first
  | (linarith; trace "ALT liCoeff_two_pos_of 1")
  | (nlinarith; trace "ALT liCoeff_two_pos_of 2")
  | (trace "ALT liCoeff_two_pos_of SORRY"; sorry)

/-- **ON THE OBLIGATION AS KEIPER.LEAN NAMES IT**: (O4) whole, and `Re γ_1 < −1/20`, give `0 < LiCoeff 2`. -/
theorem liCoeff_two_pos_of_obligations (h4 : GammaRZetaValues) (h1 : (stieltjes 1).re < -1 / 20) :
    0 < LiWeil.LiCoeff 2 :=
  liCoeff_two_pos_of (gammaRZetaOne_of h4) h1

end KeiperTwo
end SIDEExplicitFormula
