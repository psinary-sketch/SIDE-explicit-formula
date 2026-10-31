/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperGammaOne.lean
THIS PROGRAMME'S WORK (act b728, ruling (R338)(5); branch keiper-b725, no main, no tag) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(O4) AT ITS FIRST INDEX, PROVED: `gammaRZetaOne_holds : GammaRZetaOne`, Γℝ's second log-derivative coefficient at 1 is `(3/4) ζ(2)`.
Mathlib at the pin holds no derivative of digamma, and none is needed here: the reflection formula alone fixes it. With
`sinF s = sin (π s / 2)`, `Γℝ s · Γℝ (2 - s) = 1 / sinF s` (`Gammaℝ_mul_two_sub`), from `Complex.Gamma_mul_Gamma_one_sub` at `s / 2`.
The logarithmic derivative of `Γℝ(s) Γℝ(2 - s) sinF(s) = 1` near 1 reads `L(s) - L(2 - s) = -(π/2) cosF(s) / sinF(s)`, `L` Γℝ's
logarithmic derivative (`logDeriv_reflect`); its derivative at 1 is `2 L'(1) = π²/4` (`deriv_logDeriv_Gammaℝ_one`), and `(3/4) ζ(2)` is
`π²/8`.

THE CEILING: the second premise of `KeiperTwo.liCoeff_two_pos_of`, `Re γ_1 < -1/20`, is not proved here, and `liCoeff_two_pos` is not
stated: `liCoeff_two_closed` and `liCoeff_two_pos_of_stieltjes_one` carry what the first premise gives. Nothing here assumes a value
of γ_1, is a statement about the zeros of ζ beyond these theorems' own words, or proves RH or any sign of any λ_n.
-/
import SIDEExplicitFormula.KeiperTwo

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperTwo

open Keiper

/-- `cos (π s / 2)`. -/
def cosF (z : ℂ) : ℂ := Complex.cos ((Real.pi : ℂ) * (z / 2))

/-- `sin (π s / 2)`. -/
def sinF (z : ℂ) : ℂ := Complex.sin ((Real.pi : ℂ) * (z / 2))

theorem pi_half_eq : (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 := by ring

theorem sinF_one : sinF 1 = 1 := by
  unfold sinF
  rw [pi_half_eq]
  exact Complex.sin_pi_div_two

theorem cosF_one : cosF 1 = 0 := by
  unfold cosF
  rw [pi_half_eq]
  exact Complex.cos_pi_div_two

theorem hasDerivAt_arg (s : ℂ) :
    HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (z / 2)) ((Real.pi : ℂ) * (1 / 2)) s :=
  ((hasDerivAt_id' s).div_const 2).const_mul _

theorem hasDerivAt_sinF (s : ℂ) : HasDerivAt sinF (cosF s * ((Real.pi : ℂ) * (1 / 2))) s :=
  (hasDerivAt_arg s).csin

theorem hasDerivAt_cosF (s : ℂ) : HasDerivAt cosF (-sinF s * ((Real.pi : ℂ) * (1 / 2))) s :=
  (hasDerivAt_arg s).ccos

/-- **The reflection at 1**: `Γℝ s · Γℝ (2 - s) = 1 / sin (π s / 2)`. -/
theorem Gammaℝ_mul_two_sub (s : ℂ) : Gammaℝ s * Gammaℝ (2 - s) = 1 / sinF s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e1 : (2 - s) / 2 = 1 - s / 2 := by ring
  have e2 : (Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (-(2 - s) / 2) = (Real.pi : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hpi, show -s / 2 + -(2 - s) / 2 = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  have e3 : Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2) = (Real.pi : ℂ) / sinF s :=
    Complex.Gamma_mul_Gamma_one_sub (s / 2)
  rw [Gammaℝ_def, Gammaℝ_def, e1]
  calc (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * ((Real.pi : ℂ) ^ (-(2 - s) / 2) * Complex.Gamma (1 - s / 2))
      = ((Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (-(2 - s) / 2)) *
          (Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2)) := by ring
    _ = 1 / sinF s := by rw [e2, e3, ← mul_div_assoc, inv_mul_cancel₀ hpi]

theorem eventually_good : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < s.re ∧ 0 < (2 - s).re ∧ sinF s ≠ 0 := by
  have h1 : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  have hc : Continuous (fun s : ℂ => (2 - s).re) :=
    Complex.continuous_re.comp (continuous_const.sub continuous_id)
  have h2 : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < (2 - s).re :=
    (isOpen_lt continuous_const hc).mem_nhds (by
      show (0 : ℝ) < ((2 : ℂ) - 1).re
      norm_num)
  have h3 : ∀ᶠ s in 𝓝 (1 : ℂ), sinF s ≠ 0 :=
    (hasDerivAt_sinF 1).continuousAt.eventually_ne (by rw [sinF_one]; exact one_ne_zero)
  filter_upwards [h1, h2, h3] with s a b c using ⟨a, b, c⟩

/-- The field algebra of the logarithmic derivative of a product equal to 1. -/
theorem alg_step {a b c a' b' k C : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a' * b + a * (b' * (-1))) * c + a * b * (C * k) = 0) : a' / a - b' / b = -k * (C / c) := by
  have e1 : a' / a - b' / b + k * (C / c) = ((a' * b + a * (b' * (-1))) * c + a * b * (C * k)) / (a * b * c) := by
    first
      | (field_simp; ring)
      | field_simp
  have e2 : a' / a - b' / b + k * (C / c) = 0 := by rw [e1, h, zero_div]
  linear_combination e2

/-- **The logarithmic derivative of the reflection, near 1.** -/
theorem logDeriv_reflect : ∀ᶠ s in 𝓝 (1 : ℂ),
    logDeriv Gammaℝ s - logDeriv Gammaℝ (2 - s) = -((Real.pi : ℂ) * (1 / 2)) * (cosF s / sinF s) := by
  filter_upwards [eventually_good, eventually_good.eventually_nhds] with s hs hN
  obtain ⟨h1, h2, h3⟩ := hs
  have hA0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h1
  have hB0 : Gammaℝ (2 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos h2
  have hA : HasDerivAt Gammaℝ (deriv Gammaℝ s) s := (differentiableAt_Gammaℝ h1).hasDerivAt
  have hG : HasDerivAt Gammaℝ (deriv Gammaℝ (2 - s)) ((fun z : ℂ => 2 - z) s) :=
    (differentiableAt_Gammaℝ h2).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => 2 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (2 : ℂ)
  have hB : HasDerivAt (Gammaℝ ∘ fun z : ℂ => 2 - z) (deriv Gammaℝ (2 - s) * (-1)) s :=
    HasDerivAt.comp s hG hd
  have hP : HasDerivAt (fun z => Gammaℝ z * (Gammaℝ ∘ fun z : ℂ => 2 - z) z * sinF z)
      ((deriv Gammaℝ s * Gammaℝ (2 - s) + Gammaℝ s * (deriv Gammaℝ (2 - s) * (-1))) * sinF s
        + Gammaℝ s * Gammaℝ (2 - s) * (cosF s * ((Real.pi : ℂ) * (1 / 2)))) s :=
    (hA.mul hB).mul (hasDerivAt_sinF s)
  have hone : (fun z => Gammaℝ z * (Gammaℝ ∘ fun z : ℂ => 2 - z) z * sinF z) =ᶠ[𝓝 s] fun _ => (1 : ℂ) := by
    filter_upwards [hN] with z hz
    show Gammaℝ z * Gammaℝ (2 - z) * sinF z = 1
    rw [Gammaℝ_mul_two_sub, one_div, inv_mul_cancel₀ hz.2.2]
  have hc1 : HasDerivAt (fun z => Gammaℝ z * (Gammaℝ ∘ fun z : ℂ => 2 - z) z * sinF z) 0 s :=
    (hasDerivAt_const s (1 : ℂ)).congr_of_eventuallyEq hone
  have key := hP.unique hc1
  rw [logDeriv_apply, logDeriv_apply]
  exact alg_step hA0 hB0 h3 key

/-- **ψ'(1/2) = π²/2, AS Γℝ READS IT**: the derivative of Γℝ's logarithmic derivative at 1 is `π²/8`. -/
theorem deriv_logDeriv_Gammaℝ_one : deriv (logDeriv Gammaℝ) 1 = (Real.pi : ℂ) ^ 2 / 8 := by
  have hL : HasDerivAt (logDeriv Gammaℝ) (deriv (logDeriv Gammaℝ) 1) 1 :=
    analyticAt_logDeriv_Gammaℝ.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => 2 - z) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_sub (2 : ℂ)
  have hL' : HasDerivAt (logDeriv Gammaℝ) (deriv (logDeriv Gammaℝ) 1) ((fun z : ℂ => 2 - z) 1) := by
    have e : (2 : ℂ) - 1 = 1 := by norm_num
    show HasDerivAt (logDeriv Gammaℝ) (deriv (logDeriv Gammaℝ) 1) ((2 : ℂ) - 1)
    rw [e]
    exact hL
  have hR : HasDerivAt (logDeriv Gammaℝ ∘ fun z : ℂ => 2 - z) (deriv (logDeriv Gammaℝ) 1 * (-1)) 1 :=
    HasDerivAt.comp 1 hL' hd
  have hS : HasDerivAt (fun z => logDeriv Gammaℝ z - (logDeriv Gammaℝ ∘ fun z : ℂ => 2 - z) z)
      (deriv (logDeriv Gammaℝ) 1 - deriv (logDeriv Gammaℝ) 1 * (-1)) 1 := hL.sub hR
  have hne : sinF 1 ≠ 0 := by rw [sinF_one]; exact one_ne_zero
  have hQ : HasDerivAt (fun z => -((Real.pi : ℂ) * (1 / 2)) * (cosF z / sinF z)) ((Real.pi : ℂ) ^ 2 / 4) 1 := by
    have h := ((hasDerivAt_cosF 1).div (hasDerivAt_sinF 1) hne).const_mul (-((Real.pi : ℂ) * (1 / 2)))
    refine HasDerivAt.congr_deriv h ?_
    rw [sinF_one, cosF_one]
    ring
  have hE : (fun z => logDeriv Gammaℝ z - (logDeriv Gammaℝ ∘ fun z : ℂ => 2 - z) z) =ᶠ[𝓝 1]
      fun z => -((Real.pi : ℂ) * (1 / 2)) * (cosF z / sinF z) := by
    filter_upwards [logDeriv_reflect] with z hz using hz
  have key := hS.unique (hQ.congr_of_eventuallyEq hE)
  linear_combination (1 / 2 : ℂ) * key

/-- **(O4) AT ITS FIRST INDEX, PROVED.** -/
theorem gammaRZetaOne_holds : GammaRZetaOne := by
  unfold GammaRZetaOne gammaRLogCoeff taylorAt
  rw [iteratedDeriv_one, deriv_logDeriv_Gammaℝ_one, riemannZeta_two]
  first
    | (simp only [Nat.factorial_one, Nat.cast_one, div_one]; ring)
    | (norm_num [Nat.factorial]; ring)

/-- **λ_2's CLOSED FORM, ITS FIRST PREMISE DISCHARGED**: `LiCoeff 2 = 1 + γ − log 4π − γ² − 2 Re γ_1 + π²/8`. -/
theorem liCoeff_two_closed :
    LiWeil.LiCoeff 2 = 1 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)
      - Real.eulerMascheroniConstant ^ 2 - 2 * (stieltjes 1).re + Real.pi ^ 2 / 8 :=
  liCoeff_two_keiper gammaRZetaOne_holds

/-- **THE SIGN OF λ_2 ON ONE NAMED PREMISE**, `Re γ_1 < −1/20`. A single rung; not Li's criterion. -/
theorem liCoeff_two_pos_of_stieltjes_one (h1 : (stieltjes 1).re < -1 / 20) : 0 < LiWeil.LiCoeff 2 :=
  liCoeff_two_pos_of gammaRZetaOne_holds h1

end KeiperTwo
end SIDEExplicitFormula
