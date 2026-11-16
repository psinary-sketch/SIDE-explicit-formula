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

TREE STATE 2 (relay data/b725_lambda2.txt): every step as the first build's traces read it (run 41090029391), but the closed form's
last step, which that build left unsolved; there four alternatives, each closed by `done`, each with a trace, the last `sorry`, so
that the axiom print grades what closes.
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
  rw [h0]
  norm_num

/-- **(O3) at `k = 1`**: `zetaLogCoeff 1 = −2 γ_1 − γ_0²`, from `stieltjesLog_holds 1`. -/
theorem zetaLogCoeff_one : zetaLogCoeff 1 = -2 * stieltjes 1 - stieltjes 0 ^ 2 := by
  have h := stieltjesLog_holds 1
  have p0 : poleCoeff 0 = 1 := rfl
  have p1 : poleCoeff 1 = stieltjes 0 := by simp [poleCoeff]
  have p2 : poleCoeff 2 = -stieltjes 1 := by simp [poleCoeff]
  have h' : (2 : ℂ) * poleCoeff 2 = poleCoeff 0 * zetaLogCoeff 1 + poleCoeff 1 * zetaLogCoeff 0 := by
    simpa [Finset.sum_range_succ] using h
  rw [p0, p1, p2, zetaLogCoeff_zero] at h'
  linear_combination (-1 : ℂ) * h'

/-- **Bulka's first coefficient**: `2 keiperA 0 + keiperA 1`, by (O1) and (O2) as KeiperIdentities.lean proves them. -/
theorem taylorCoeff_xi_one :
    LiCriterion.taylorCoeff LiCriterion.riemannXi 1 = 2 * keiperA 0 + keiperA 1 := by
  have hb := binomialTransform_holds 1
  have hs : ∀ k : ℕ, xiLogCoeff k = keiperA k := logDerivSplit_holds
  rw [hb]
  simp [Finset.sum_range_succ, hs]

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
    rw [taylorCoeff_xi_one, keiperA_zero, keiperA, zetaLogCoeff_one, h4', riemannZeta_two, stieltjes_zero,
      log_four_pi_ofReal]
    push_cast
    ring
  first
  | (rw [h, hc, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]; norm_num; ring_nf; done; trace "ALT liCoeff_two_keiper A")
  | (rw [h, hc, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]; norm_num; done; trace "ALT liCoeff_two_keiper B")
  | (rw [h, hc]; simp [← Complex.ofReal_pow]; ring_nf; done; trace "ALT liCoeff_two_keiper C")
  | (rw [h, hc, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]; simp; linarith; trace "ALT liCoeff_two_keiper D")
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
  have hA : (1 : ℝ) / 3 < Real.eulerMascheroniConstant := by linarith
  have hgg : Real.eulerMascheroniConstant ^ 2 ≤ Real.eulerMascheroniConstant - 2 / 9 := by
    nlinarith [mul_pos (sub_pos.2 hA) (sub_pos.2 hg2)]
  have hpi2 : (9.86902225 : ℝ) < Real.pi ^ 2 := by nlinarith [hpi, Real.pi_pos]
  linarith

/-- **ON THE OBLIGATION AS KEIPER.LEAN NAMES IT**: (O4) whole, and `Re γ_1 < −1/20`, give `0 < LiCoeff 2`. -/
theorem liCoeff_two_pos_of_obligations (h4 : GammaRZetaValues) (h1 : (stieltjes 1).re < -1 / 20) :
    0 < LiWeil.LiCoeff 2 :=
  liCoeff_two_pos_of (gammaRZetaOne_of h4) h1

end KeiperTwo
end SIDEExplicitFormula
