/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Detector.lean
THIS PROGRAMME'S WORK (act b590, ruling (R200)(4)(a); the Epstein negative control, its generic half) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE DETECTOR THEOREM, EXTRACTED FROM THE CONVERSE. For any configuration of the schema with a point `ρ₀` off the line, a
window in classK has a zero side of negative real part. The window is named as far as the converse names it: its base is
the kernel's plateau with ramp fraction `1/2` and half-width `baseWidth ρ₀ = 1 / (4 (‖γ(ρ₀)‖ + 1))` -- the witness of
`base_nonzero_at` (PowerWindow.lean :276), restated here with that witness written into the statement -- and the window is
`kWindow a base j`, the operator of a coefficient list `a` applied to the `j`-th iterated self-convolution of the base,
paired with itself, supported in `[-(2^j w), 2^j w]` before the pairing. The list `a` and the power `j` stay existential:
the converse draws `j` from `Metric.tendsto_atTop` over a limit with no rate (Converse.lean :171). Nothing here proves RH
or GRH or locates any zero; every statement is over an arbitrary configuration with an off-line point as a hypothesis.
-/
import SIDEExplicitFormula.Schema.Converse

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

/-- The plateau's ramp fraction the converse takes. -/
theorem half_pos' : (0 : ℝ) < 1 / 2 := by norm_num

theorem half_lt_one' : (1 / 2 : ℝ) < 1 := by norm_num

/-- **The base width at a point**: `1 / (4 (‖γ(ρ)‖ + 1))`, the witness `base_nonzero_at` takes at `z = γ(ρ)`. -/
def baseWidth (ρ : ℂ) : ℝ := 1 / (4 * (‖Zeta23.gammaOf ρ‖ + 1))

theorem baseWidth_pos (ρ : ℂ) : 0 < baseWidth ρ := by
  unfold baseWidth
  positivity

/-- **The detector's base window at a point**: the kernel's plateau, ramp fraction `1/2`, half-width `baseWidth ρ`. -/
def detectorBase (ρ : ℂ) : ℝ → ℝ := plateau (1 / 2) (baseWidth ρ) half_pos' half_lt_one' (baseWidth_pos ρ)

/-- **`base_nonzero_at` with its witness named**: at any `z`, the plateau's transform is nonzero for every width up to
`1 / (4 (‖z‖ + 1))`. The proof is `base_nonzero_at`'s (PowerWindow.lean :276-:326), its witness written into the statement. -/
theorem base_nonzero_at_width (F : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (z : ℂ) (L : ℝ) (hL : 0 < L)
    (hLL : L ≤ 1 / (4 * (‖z‖ + 1))) : Zeta23.paperFT (phiC (plateau F L hF0 hF1 hL)) z ≠ 0 := by
  set φ := plateau F L hF0 hF1 hL with hφdef
  have hcont : Continuous φ := (plateau_contDiff F L hF0 hF1 hL 0).continuous
  have hcs : HasCompactSupport φ := plateau_hasCompactSupport F L hF0 hF1 hL
  have hsupp := plateau_support_Icc F L hF0 hF1 hL
  have hS : 0 < ∫ u, φ u := plateau_integral_pos F L hF0 hF1 hL
  have hzL : ‖z‖ * L ≤ 1 / 4 := by
    have h1 : ‖z‖ * L ≤ ‖z‖ * (1 / (4 * (‖z‖ + 1))) := mul_le_mul_of_nonneg_left hLL (norm_nonneg z)
    have h2 : ‖z‖ * (1 / (4 * (‖z‖ + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith [norm_nonneg z]
    linarith
  have hφc : Continuous (fun u => (φ u : ℂ)) := Complex.continuous_ofReal.comp hcont
  have hφcs : HasCompactSupport (fun u => (φ u : ℂ)) := hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have iE : Integrable (fun u : ℝ => (φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) :=
    phiC_exp_integrable hcont hcs z
  have i1 : Integrable (fun u : ℝ => (φ u : ℂ)) := hφc.integrable_of_hasCompactSupport hφcs
  have hpt : ∀ u, ‖(φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖ ≤ φ u * (1 / 2) := by
    intro u
    by_cases h0 : φ u = 0
    · rw [h0]; simp
    · have hu : u ∈ Set.Icc (-L) L := hsupp h0
      have hnu : ‖Complex.I * z * (u : ℂ)‖ ≤ 1 / 4 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have : |u| ≤ L := abs_le.mpr ⟨hu.1, hu.2⟩
        nlinarith [norm_nonneg z, abs_nonneg u]
      have he : ‖Complex.exp (Complex.I * z * (u : ℂ)) - 1‖ ≤ 2 * ‖Complex.I * z * (u : ℂ)‖ :=
        Complex.norm_exp_sub_one_le (by linarith)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg F L hF0 hF1 hL u)]
      exact mul_le_mul_of_nonneg_left (by linarith) (plateau_nonneg F L hF0 hF1 hL u)
  have hdiff : Zeta23.paperFT (phiC φ) z - ((∫ u, φ u : ℝ) : ℂ) =
      ∫ u, (φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1) := by
    have hre : ((∫ u, φ u : ℝ) : ℂ) = ∫ u, ((φ u : ℝ) : ℂ) := integral_ofReal.symm
    rw [hre]
    simp only [Zeta23.paperFT, phiC]
    rw [← integral_sub iE i1]
    congr 1
    ext u
    ring
  have hbound : ‖Zeta23.paperFT (phiC φ) z - ((∫ u, φ u : ℝ) : ℂ)‖ ≤ (∫ u, φ u) * (1 / 2) := by
    rw [hdiff]
    calc ‖∫ u, (φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖
        ≤ ∫ u, ‖(φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u, φ u * (1 / 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hcont.integrable_of_hasCompactSupport hcs).mul_const _) (Filter.Eventually.of_forall hpt)
      _ = (∫ u, φ u) * (1 / 2) := integral_mul_const _ _
  intro h0
  rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at hbound
  linarith

/-- **THE DETECTOR THEOREM**: for a configuration of the schema with a point `ρ₀` off the line, there are a coefficient list
`a` and a power `j` such that the window `kWindow a (detectorBase ρ₀) j` is in classK, its pre-pairing factor is supported in
`[-(2^j w), 2^j w]` with `w = baseWidth ρ₀`, and its zero side has negative real part. -/
theorem detector (C : WeilConfig) (ρ₀ : ℂ) (h₀ : ρ₀ ∈ C.carrier) (hoff : ρ₀.re ≠ 1 / 2) :
    ∃ (a : List ℝ) (j : ℕ), classK (kWindow a (detectorBase ρ₀) j) ∧
      Function.support (pwWindow a (detectorBase ρ₀) j) ⊆ Set.Icc (-(2 ^ j * baseWidth ρ₀)) (2 ^ j * baseWidth ρ₀) ∧
      (zeroSide_cfg C (kWindow a (detectorBase ρ₀) j)).re < 0 := by
  have hL := baseWidth_pos ρ₀
  have h4 : ContDiff ℝ 4 (detectorBase ρ₀) := by
    have := plateau_contDiff (1 / 2) (baseWidth ρ₀) half_pos' half_lt_one' hL 4
    exact_mod_cast this
  have hsupp : Function.support (detectorBase ρ₀) ⊆ Set.Icc (-baseWidth ρ₀) (baseWidth ρ₀) :=
    plateau_support_Icc (1 / 2) (baseWidth ρ₀) half_pos' half_lt_one' hL
  have hne : Zeta23.paperFT (phiC (detectorBase ρ₀)) (Zeta23.gammaOf ρ₀) ≠ 0 :=
    base_nonzero_at_width (1 / 2) half_pos' half_lt_one' (Zeta23.gammaOf ρ₀) (baseWidth ρ₀) hL le_rfl
  obtain ⟨ρs, hρs, hoffs, hpos, hdom⟩ :=
    dominant_exists C.toZeroConfig h4 hsupp hL.le ρ₀ h₀ hoff (norm_pos_iff.mpr hne)
  have H : PWSetup C.toZeroConfig (detectorBase ρ₀) (baseWidth ρ₀) (offScore (detectorBase ρ₀) ρs) :=
    ⟨plateau_even _ _ half_pos' half_lt_one' hL, plateau_contDiff _ _ half_pos' half_lt_one' hL ⊤, hsupp, hL.le, hpos, hdom⟩
  obtain ⟨a, j, hneg⟩ := zeroSide_eventually_neg_cfg H ρs ⟨hρs, hoffs, rfl⟩
  exact ⟨a, j, kWindow_classK a H.hsm H.hs j, pwWindow_support a H.hs j, hneg⟩

/-- **The detector's consequence**: a configuration of the schema with a point off the line is not Weil-positive on classK.
(The same conclusion as the contrapositive of `h2_sign_cfg_imp_online`, reached through the named window.) -/
theorem not_h2_sign_cfg_of_offline (C : WeilConfig) (ρ₀ : ℂ) (h₀ : ρ₀ ∈ C.carrier) (hoff : ρ₀.re ≠ 1 / 2) :
    ¬ h2_sign_cfg C := by
  intro h2
  obtain ⟨a, j, hk, -, hneg⟩ := detector C ρ₀ h₀ hoff
  have hsign := h2 _ hk
  obtain ⟨he, hc, hs, -⟩ := hk
  rw [← zeroSide_cfg_eq C hc hs he] at hsign
  have h0 := (Complex.nonneg_iff.mp hsign).1
  linarith

end Schema
end SIDEExplicitFormula
