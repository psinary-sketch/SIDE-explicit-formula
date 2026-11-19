/-
SIDE-explicit-formula -- SIDEExplicitFormula/PoleAutocorrelation.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(6), statement (S3); W-ORD-SIGN-SECTORS) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE POLE TERM ON AN AUTOCORRELATION. For `h` twice continuously differentiable with compact support, the pole term of
`k = weilTest h h` is `2 Re(A conj B)` (`poleTerm_weilTest`), `A` and `B` the transforms of `h` at `-i/2` and `i/2`, which are the
integrals of `h` against `e^{x/2}` and `e^{-x/2}` (`paperFT_neg_half_I`, `paperFT_half_I`): the transform of `weilTest h h` is
`h^(z) conj(h^(conj z))` (`Zeta23.EF.paperFT_weilTest`), so the pole term is `B conj A + A conj B`. For a real `h`, with `C` and `S`
the integrals of `h` against `cosh(x/2)` and `sinh(x/2)`, `A = C + S`, `B = C - S` and the pole term is `2 (C² - S²)`
(`poleTerm_weilTest_real`): twice the square of `C` on an even `h` (`poleTerm_weilTest_even`, `S = 0`) and minus twice the square of
`S` on an odd one (`poleTerm_weilTest_odd`, `C = 0`). The odd window `oddWindow` (`u` times TwoPropertyWindow's plateau, ramp
fraction 1/2, half-width 1) has `S > 0`, so its autocorrelation is a `k` in classK whose pole term has real part below 0
(`exists_classK_poleTerm_re_neg`). No premise is bound; nothing here concerns any zero.
-/
import SIDEExplicitFormula.TwoPropertyWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The two transforms -/

/-- The transform at `-i/2` is the integral of `h` against `e^{x/2}`. -/
theorem paperFT_neg_half_I (h : ℝ → ℂ) :
    Zeta23.paperFT h (-I / 2) = ∫ u : ℝ, h u * ((Real.exp (u / 2) : ℝ) : ℂ) := by
  unfold Zeta23.paperFT
  congr 1
  ext u
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(u : ℂ) / 2) * Complex.I_sq

/-- The transform at `i/2` is the integral of `h` against `e^{-x/2}`. -/
theorem paperFT_half_I (h : ℝ → ℂ) :
    Zeta23.paperFT h (I / 2) = ∫ u : ℝ, h u * ((Real.exp (-u / 2) : ℝ) : ℂ) := by
  unfold Zeta23.paperFT
  congr 1
  ext u
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((u : ℂ) / 2) * Complex.I_sq

/-! ### (S3) the pole term -/

/-- **(S3) The pole term on an autocorrelation.** For `h` twice continuously differentiable with compact support,
`poleTerm (weilTest h h) = 2 Re(A conj B)`, with `A = h^(-i/2)` and `B = h^(i/2)`. -/
theorem poleTerm_weilTest {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (hs : HasCompactSupport h) :
    poleTerm (Zeta23.EF.weilTest h h) =
      ((2 * (Zeta23.paperFT h (-I / 2) * conj (Zeta23.paperFT h (I / 2))).re : ℝ) : ℂ) := by
  have hc : Continuous h := hh.continuous
  have h1 : conj (I / 2) = -I / 2 := by
    first
    | rw [map_div₀, Complex.conj_I, map_ofNat]
    | (apply Complex.ext <;> simp)
  have h2 : conj (-I / 2) = I / 2 := by
    first
    | rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
    | (apply Complex.ext <;> simp)
  unfold poleTerm
  rw [Zeta23.EF.paperFT_weilTest hc hc hs hs, Zeta23.EF.paperFT_weilTest hc hc hs hs, h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- For a real `g`, continuous with compact support, `g^(-i/2) = C + S`, `C` and `S` the integrals of `g` against `cosh(x/2)` and
`sinh(x/2)`. -/
theorem paperFT_real_neg_half_I {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Zeta23.paperFT (fun u => (g u : ℂ)) (-I / 2) =
      (((∫ u : ℝ, g u * Real.cosh (u / 2)) + ∫ u : ℝ, g u * Real.sinh (u / 2) : ℝ) : ℂ) := by
  have hci : Integrable (fun u : ℝ => g u * Real.cosh (u / 2)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hs.mono (Function.support_mul_subset_left _ _))
  have hsi : Integrable (fun u : ℝ => g u * Real.sinh (u / 2)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hs.mono (Function.support_mul_subset_left _ _))
  have hre : (((∫ u : ℝ, (g u * Real.cosh (u / 2) + g u * Real.sinh (u / 2))) : ℝ) : ℂ)
      = ∫ u : ℝ, (((g u * Real.cosh (u / 2) + g u * Real.sinh (u / 2)) : ℝ) : ℂ) := integral_ofReal.symm
  rw [paperFT_neg_half_I, ← integral_add hci hsi, hre]
  congr 1
  ext u
  rw [← Real.cosh_add_sinh]
  push_cast
  ring

/-- For a real `g`, continuous with compact support, `g^(i/2) = C - S`. -/
theorem paperFT_real_half_I {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Zeta23.paperFT (fun u => (g u : ℂ)) (I / 2) =
      (((∫ u : ℝ, g u * Real.cosh (u / 2)) - ∫ u : ℝ, g u * Real.sinh (u / 2) : ℝ) : ℂ) := by
  have hci : Integrable (fun u : ℝ => g u * Real.cosh (u / 2)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hs.mono (Function.support_mul_subset_left _ _))
  have hsi : Integrable (fun u : ℝ => g u * Real.sinh (u / 2)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hs.mono (Function.support_mul_subset_left _ _))
  have hre : (((∫ u : ℝ, (g u * Real.cosh (u / 2) - g u * Real.sinh (u / 2))) : ℝ) : ℂ)
      = ∫ u : ℝ, (((g u * Real.cosh (u / 2) - g u * Real.sinh (u / 2)) : ℝ) : ℂ) := integral_ofReal.symm
  rw [paperFT_half_I, ← integral_sub hci hsi, hre]
  congr 1
  ext u
  rw [show -u / 2 = -(u / 2) by ring, ← Real.cosh_sub_sinh]
  push_cast
  ring

/-- **(S3) on a real `h`:** `poleTerm (weilTest h h) = 2 (C² - S²)`, `C` and `S` the integrals of `h` against `cosh(x/2)` and
`sinh(x/2)`. -/
theorem poleTerm_weilTest_real {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    poleTerm (Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) =
      ((2 * ((∫ u : ℝ, g u * Real.cosh (u / 2)) ^ 2 - (∫ u : ℝ, g u * Real.sinh (u / 2)) ^ 2) : ℝ) : ℂ) := by
  have hh : ContDiff ℝ 2 (fun u => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hhs : HasCompactSupport (fun u => (g u : ℂ)) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  rw [poleTerm_weilTest hh hhs, paperFT_real_neg_half_I hg.continuous hs, paperFT_real_half_I hg.continuous hs,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  congr 1
  ring

/-- On an even real `g` the integral against `sinh(x/2)` vanishes. -/
theorem integral_mul_sinh_eq_zero_of_even {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) :
    ∫ u : ℝ, g u * Real.sinh (u / 2) = 0 := by
  have h1 : ∫ u : ℝ, g u * Real.sinh (u / 2) = ∫ u : ℝ, -(g u * Real.sinh (u / 2)) := by
    rw [← integral_neg_eq_self (fun u : ℝ => -(g u * Real.sinh (u / 2))) volume]
    congr 1
    ext u
    simp only [hev, neg_div, Real.sinh_neg, mul_neg, neg_neg]
  rw [integral_neg] at h1
  linarith

/-- On an odd real `g` the integral against `cosh(x/2)` vanishes. -/
theorem integral_mul_cosh_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) :
    ∫ u : ℝ, g u * Real.cosh (u / 2) = 0 := by
  have h1 : ∫ u : ℝ, g u * Real.cosh (u / 2) = ∫ u : ℝ, -(g u * Real.cosh (u / 2)) := by
    rw [← integral_neg_eq_self (fun u : ℝ => -(g u * Real.cosh (u / 2))) volume]
    congr 1
    ext u
    simp only [hodd, neg_div, Real.cosh_neg, neg_mul, neg_neg]
  rw [integral_neg] at h1
  linarith

/-- **(S3) on an even real `h`:** the pole term is twice the square of the integral of `h cosh(x/2)`. -/
theorem poleTerm_weilTest_even {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) (hev : ∀ x, g (-x) = g x) :
    poleTerm (Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) =
      ((2 * (∫ u : ℝ, g u * Real.cosh (u / 2)) ^ 2 : ℝ) : ℂ) := by
  rw [poleTerm_weilTest_real hg hs, integral_mul_sinh_eq_zero_of_even hev]
  congr 1
  ring

/-- **(S3) on an odd real `h`:** the pole term is minus twice the square of the integral of `h sinh(x/2)`. -/
theorem poleTerm_weilTest_odd {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) (hodd : ∀ x, g (-x) = -g x) :
    poleTerm (Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) =
      ((-(2 * (∫ u : ℝ, g u * Real.sinh (u / 2)) ^ 2) : ℝ) : ℂ) := by
  rw [poleTerm_weilTest_real hg hs, integral_mul_cosh_eq_zero_of_odd hodd]
  congr 1
  ring

/-! ### The odd window, and a `k` in classK with the pole term's real part below 0 -/

/-- TwoPropertyWindow's plateau at ramp fraction `1/2` and half-width `1`. -/
def basePlateau : ℝ → ℝ := plateau (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)

/-- The odd window: `u` times `basePlateau`. -/
def oddWindow : ℝ → ℝ := fun u => u * basePlateau u

theorem basePlateau_contDiff : ContDiff ℝ 2 basePlateau := by
  have := plateau_contDiff (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) 2
  unfold basePlateau
  exact_mod_cast this

/-- The plateau at or above 0, as PowerWindow's `plateau_nonneg` proves it (a product of two smooth transitions), here so that this
file does not import PowerWindow. -/
theorem basePlateau_nonneg (u : ℝ) : 0 ≤ basePlateau u := by
  unfold basePlateau plateau
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem oddWindow_contDiff : ContDiff ℝ 2 oddWindow := by
  unfold oddWindow
  exact contDiff_id.mul basePlateau_contDiff

theorem oddWindow_hasCompactSupport : HasCompactSupport oddWindow := by
  have h : HasCompactSupport basePlateau :=
    plateau_hasCompactSupport (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  exact h.mono (Function.support_mul_subset_right (fun u : ℝ => u) basePlateau)

theorem oddWindow_odd (x : ℝ) : oddWindow (-x) = -oddWindow x := by
  have he : basePlateau (-x) = basePlateau x :=
    plateau_even (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) x
  show -x * basePlateau (-x) = -(x * basePlateau x)
  rw [he]
  ring

/-- The odd window's integral against `sinh(x/2)` is positive: the integrand `u sinh(u/2)` times the plateau is at or above 0, and
positive at `u = 1/2`, where the plateau is 1. -/
theorem oddWindow_sinh_pos : 0 < ∫ u : ℝ, oddWindow u * Real.sinh (u / 2) := by
  have hpc : Continuous basePlateau := basePlateau_contDiff.continuous
  have hcont : Continuous (fun u : ℝ => oddWindow u * Real.sinh (u / 2)) := by
    show Continuous (fun u : ℝ => u * basePlateau u * Real.sinh (u / 2))
    exact (continuous_id.mul hpc).mul (by fun_prop)
  have hcs : HasCompactSupport (fun u : ℝ => oddWindow u * Real.sinh (u / 2)) :=
    oddWindow_hasCompactSupport.mono (Function.support_mul_subset_left _ _)
  have hnn : 0 ≤ fun u : ℝ => oddWindow u * Real.sinh (u / 2) := fun u => by
    show 0 ≤ u * basePlateau u * Real.sinh (u / 2)
    have hp : 0 ≤ basePlateau u := basePlateau_nonneg u
    have hus : 0 ≤ u * Real.sinh (u / 2) := by
      rcases le_total 0 u with h | h
      · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr (by linarith))
      · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr (by linarith))
    have hr : u * basePlateau u * Real.sinh (u / 2) = u * Real.sinh (u / 2) * basePlateau u := by ring
    rw [hr]
    exact mul_nonneg hus hp
  have hone : basePlateau (1 / 2) = 1 :=
    plateau_eq_one (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) (1 / 2)
      (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num)
  have hsh : 0 < Real.sinh ((1 / 2 : ℝ) / 2) := Real.sinh_pos_iff.mpr (by norm_num)
  have hx : (fun u : ℝ => oddWindow u * Real.sinh (u / 2)) (1 / 2) ≠ 0 := by
    show (1 / 2 : ℝ) * basePlateau (1 / 2) * Real.sinh ((1 / 2) / 2) ≠ 0
    rw [hone]
    exact (mul_pos (by norm_num) hsh).ne'
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcont hcs hnn hx

/-- **(S3), its sign:** there is a `k` in classK with the real part of `poleTerm k` below 0 -- the autocorrelation of the odd window,
where the pole term is minus twice the square of a positive integral. -/
theorem exists_classK_poleTerm_re_neg : ∃ k : ℝ → ℂ, classK k ∧ (poleTerm k).re < 0 := by
  have hg := oddWindow_contDiff
  have hs := oddWindow_hasCompactSupport
  have hh : ContDiff ℝ 2 (fun u => (oddWindow u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hhs : HasCompactSupport (fun u => (oddWindow u : ℂ)) :=
    hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  refine ⟨Zeta23.EF.weilTest (fun u => (oddWindow u : ℂ)) (fun u => (oddWindow u : ℂ)),
    ⟨fun x => weilTest_ofReal_even oddWindow x, Zeta23.EF.weilTest_contDiff hh hh.continuous hhs,
      Zeta23.EF.weilTest_hasCompactSupport hhs hhs, fun u => (oddWindow u : ℂ), hh, hhs, rfl⟩, ?_⟩
  rw [poleTerm_weilTest_odd hg hs oddWindow_odd, Complex.ofReal_re]
  have h2 := pow_pos oddWindow_sinh_pos 2
  linarith

end B321
end SIDEExplicitFormula
