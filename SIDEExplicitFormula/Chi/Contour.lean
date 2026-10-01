/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/Contour.lean
THIS PROGRAMME'S WORK (act b570, ruling (R180)(5)(d); W-ORD-GRH-WEIL, act five) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/Contour.lean's `rectangle_identity`. For primitive `χ ≠ 1` the completed function
`Λ(·, χ) = completedLFunction χ` is entire, so the weighted argument principle (Zeta23's
`rectangleIntegral'_mul_logDeriv`, Analytic/RectangleLogDeriv.lean :368) applies over `[1 − c, c] × [−R, R]` with no pole
terms: `(1/2πi)∮ H·Λ'/Λ = Σ_{|γ_ρ| < R} m_ρ H(ρ)` -- ζ's `− H(0) − H(1)` are absent. Nothing here locates any zero.
-/
import SIDEExplicitFormula.Chi.CountByIntegral
import SIDEExplicitFormula.Chi.VerticalLine
import Zeta23.WeilEF.Contour

open Complex Topology Filter Set

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF

variable {N : ℕ} [NeZero N]

/-- **The rectangle identity for χ** at a height `R` free of zeros of `Λ(·, χ)` on the horizontal sides. -/
theorem rectangle_identity_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) {R : ℝ} (hR : 7 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → completedLFunction χ s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZeroChi χ ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv (completedLFunction χ) s)
          ((1 - c : ℝ) - R * I) ((c : ℝ) + R * I)
        = ∑ ρ ∈ Z, (zeroMultChi χ ρ : ℂ) * Hfn k ρ := by
  classical
  set z : ℂ := (1 - c : ℝ) - R * I with hzdef
  set w : ℂ := (c : ℝ) + R * I with hwdef
  have hzre : z.re = 1 - c := by simp [hzdef]
  have hzim : z.im = -R := by simp [hzdef]
  have hwre : w.re = c := by simp [hwdef]
  have hwim : w.im = R := by simp [hwdef]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
    intro s
    simp only [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  have hfin := finite_window_chi h1 (-R) R
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmemiff : ∀ ρ : ℂ, ρ ∈ Z ↔ (IsNontrivialZeroChi χ ρ ∧ -R < ρ.im ∧ ρ.im ≤ R) := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hZcoe : (Z : Set ℂ) = {ρ : ℂ | IsNontrivialZeroChi χ ρ ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, hZmemiff]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1', h2, h3⟩
      refine ⟨h1', h2, lt_of_le_of_ne h3 ?_⟩
      intro h
      exact hgood ρ (Or.inl h) (by linarith [h1'.2.1]) (by linarith [h1'.2.2])
        ((completedLFunction_eq_zero_iff_of_re_pos h1 h1'.2.1).mpr h1'.1)
    · rintro ⟨h1', h2, h3⟩
      exact ⟨h1', h2, h3.le⟩
  refine ⟨Z, hZcoe, ?_⟩
  have hf : AnalyticOnNhd ℂ (completedLFunction χ) (Rectangle z w) := fun s _ => analyticAt_completedLFunction h1 s
  have hg : AnalyticOnNhd ℂ (Hfn k) (Rectangle z w) := by
    intro s _
    have hdiff : Differentiable ℂ (Hfn k) := by
      unfold Hfn
      exact (differentiable_paperFT hk.continuous hkc).comp ((differentiable_id.sub_const _).div_const _)
    exact hdiff.analyticAt s
  have hborder : ∀ s ∈ RectangleBorder z w, completedLFunction χ s ≠ 0 := by
    intro s hs h0
    have hsrect := rectangleBorder_subset_rectangle z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood s (Or.inr h') hr1 hr2 h0
    · exact completedLFunction_ne_zero_of_re_nonpos hχ h1 (by rw [h']; linarith) h0
    · exact hgood s (Or.inl h') hr1 hr2 h0
    · exact completedLFunction_ne_zero_of_one_le_re h1 (by rw [h']; linarith) h0
  have hZchar : ∀ s ∈ Rectangle z w, (completedLFunction χ s = 0 ↔ s ∈ Z) := by
    intro s hsrect
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    rw [hZmemiff]
    constructor
    · intro h0
      have hnz : IsNontrivialZeroChi χ s := (completedLFunction_eq_zero_iff hχ h1).mp h0
      refine ⟨hnz, ?_, hi2⟩
      rcases lt_or_eq_of_le hi1 with h | h
      · exact h
      · exact absurd h0 (hgood s (Or.inr h.symm) hr1 hr2)
    · rintro ⟨h1', _, _⟩
      exact (completedLFunction_eq_zero_iff hχ h1).mpr h1'
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro ρ hρ
    rw [Finset.mem_coe, hZmemiff] at hρ
    obtain ⟨h1', h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1'.2.1], by linarith [h1'.2.2]⟩, h2.le, h3⟩
  rw [Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder Z hZchar hZsub]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [analyticOrderNatAt_completedLFunction h1 ((hZmemiff ρ).mp hρ).1.2.1]

end GRHWeil
end SIDEExplicitFormula
