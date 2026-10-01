/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/FullLineAssembly.lean
THIS PROGRAMME'S WORK (act b571, ruling (R181)(4)(c); W-ORD-GRH-WEIL, act six) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/FullLineAssembly.lean: the `R → ∞` assembly of the full-line identity for χ from
`rectangle_identity_chi` (Chi/Contour), the fold and the heights (Chi/FullLine), `horizontal_vanish_chi` (Chi/Horizontal) and
`zero_sum_limit_chi` (Chi/ZeroSumLimit), along χ's good heights (`good_heights_chi`, Chi/GoodHeights):
  `(1/2π) ∫ Fline_chi χ k c t dt = Σ_ρ m_ρ H(ρ)`,
the zero side the absolutely convergent tsum over `chiZeroConfig`; no pole terms, `Λ(·, χ)` being entire for `χ ≠ 1`.
Nothing here locates any zero.
-/
import SIDEExplicitFormula.Chi.Horizontal
import SIDEExplicitFormula.Chi.ZeroSumLimit
import SIDEExplicitFormula.Chi.GoodHeights
import Zeta23.WeilEF.FullLineAssembly

open Complex Topology Filter Set MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF

variable {N : ℕ} [NeZero N]

/-- **The full-line identity for χ** (`R → ∞` along good heights; the horizontal pieces vanish):
`(1/2π) ∫ [H(c+it)·Λ'/Λ(c+it, χ) + H(1−c−it)·Λ'/Λ(c+it, χ⁻¹) + H(1−c−it)·log N] dt = Σ_ρ m_ρ H(ρ)`. -/
theorem full_line_identity_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Fline_chi χ k c t
      = ∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Hfn k ρ := by
  obtain ⟨Cg, hCg, R, hR⟩ := good_heights_chi hχ h1
  set f : ℂ → ℂ := fun s => Hfn k s * logDeriv (completedLFunction χ) s with hf
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZeroChi χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = ∑ ρ ∈ Z, (zeroMultChi χ ρ : ℂ) * Hfn k ρ := by
    intro j
    obtain ⟨h1', h2, h3⟩ := hR j
    exact rectangle_identity_chi hχ h1 hk hkc hc1 (R := R j) (by linarith)
      (completedLFunction_ne_zero_on_horizontals_chi hχ h1 hc1 hc2 (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish_chi hχ h1 hk hkc hc1 hc2 hCg hR
  have hZlim := zero_sum_limit_chi hχ h1 hk hkc (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := tendsto_interval_Fline_chi h1 hk hkc hc1 hc2 (R := R) (fun j => by linarith [(hR j).1])
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral f (1 - c) c (-(R j)) - HIntegral f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, Fline_chi χ k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq_chi hχ h1 hk hkc hc1 hc2 (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline_chi χ k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  have hL' : Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMultChi χ ρ : ℂ) * Hfn k ρ)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline_chi χ k c t)) :=
    hL.congr fun j => hE j
  exact tendsto_nhds_unique hL' hZlim

end GRHWeil
end SIDEExplicitFormula
