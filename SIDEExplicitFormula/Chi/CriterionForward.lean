/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/CriterionForward.lean
THIS PROGRAMME'S WORK (act b572, ruling (R182)(4)(a)-(b); W-ORD-GRH-WEIL, act seven) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CRITERION AT THE χ-INSTANCE, ITS FORWARD HALF. The statement of record is b562's `h2_sign_chi` (GRHWeil.lean :75), over the
χ-configuration alone: the ζ criterion's proof consumes the configuration's reflection ρ ↦ 1 − ρ̄ and no conjugation fact
(relay data/b572_reality.txt), and `chiZeroConfig` carries the reflection. Here: the zero side for χ, its identity with
`archTerm_chi − primeSum_chi` (from `EF_lit_chi_holds`, b571), the strip form for χ and its equivalence with `GRH_chi`, and
`GRH_chi χ → h2_sign_chi χ` by RHChain's argument -- on the line each zero's term is `m_ρ·|ĥ(γ_ρ)|²`.
Nothing here proves GRH or locates any zero of any `L(s, χ)`.
-/
import SIDEExplicitFormula.Chi.Main
import SIDEExplicitFormula.PowerLimit

open Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The zero side for χ: `Σ_ρ m_ρ ĥ(γ_ρ)` over the nontrivial zeros of `LFunction χ` -- `B321.zeroSide` at the
χ-configuration. -/
def zeroSide_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (k : ℝ → ℂ) : ℂ :=
  ∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

/-- **b321's identity for χ**: for `k ∈ C_c²`, the zero side is `archTerm_chi χ k − primeSum_chi χ k` (`EF_lit_chi_holds`). -/
theorem zeroSide_chi_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    zeroSide_chi χ hχ h1 k = archTerm_chi χ k - primeSum_chi χ k :=
  (EF_lit_chi_holds hχ h1 k hk hkc).2

/-- The strip form for χ: every point of the χ-configuration is on the line. -/
def rh_strip_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : Prop :=
  ∀ ρ ∈ (chiZeroConfig χ hχ h1).carrier, ρ.re = 1 / 2

/-- The strip form for χ is `GRH_chi χ` (the carrier is the zero set of `LFunction χ` in the open strip). -/
theorem rh_strip_chi_iff_grh_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    rh_strip_chi χ hχ h1 ↔ GRH_chi χ :=
  ⟨fun h s hs h0 h1' => h s ⟨hs, h0, h1'⟩, fun h ρ hρ => h ρ hρ.1 hρ.2.1 hρ.2.2⟩

/-- **The forward half at the strip**: `rh_strip_chi → h2_sign_chi`, RHChain's argument at the χ-configuration. -/
theorem rh_strip_chi_imp_h2_sign_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    rh_strip_chi χ hχ h1 → h2_sign_chi χ := by
  intro hstrip k hk
  obtain ⟨_he, hc, hs, h, hh, hhs, rfl⟩ := hk
  rw [← zeroSide_chi_eq hχ h1 hc hs]
  unfold zeroSide_chi
  refine tsum_nonneg fun ρ => ?_
  have hre : (ρ : ℂ).re = 1 / 2 := hstrip (ρ : ℂ) ρ.2
  have him : (Zeta23.gammaOf (ρ : ℂ)).im = 0 := by
    unfold Zeta23.gammaOf
    rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, hre]
    rw [Complex.div_ofNat_re, Complex.one_re, sub_self, neg_zero]
  have hcj : conj (Zeta23.gammaOf (ρ : ℂ)) = Zeta23.gammaOf (ρ : ℂ) :=
    Complex.conj_eq_iff_im.mpr him
  have hterm : Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ))
      = ((Complex.normSq (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ))) : ℝ) : ℂ) := by
    rw [Zeta23.EF.paperFT_weilTest hh.continuous hh.continuous hhs hhs, hcj,
      Complex.mul_conj (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ)))]
  have hm : (0 : ℂ) ≤ ((chiZeroConfig χ hχ h1).mult (ρ : ℂ) : ℂ) := by
    exact Nat.cast_nonneg _
  have hnn : (0 : ℂ) ≤ ((chiZeroConfig χ hχ h1).mult (ρ : ℂ) : ℂ)
      * Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ)) := by
    rw [hterm]
    exact mul_nonneg hm (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  exact hnn

/-- **THE FORWARD HALF OF THE CRITERION FOR χ**: `GRH_chi χ → h2_sign_chi χ`, for primitive `χ ≠ 1`. -/
theorem grh_chi_imp_h2_sign_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    GRH_chi χ → h2_sign_chi χ :=
  fun h => rh_strip_chi_imp_h2_sign_chi hχ h1 ((rh_strip_chi_iff_grh_chi hχ h1).mpr h)

end GRHWeil
end SIDEExplicitFormula
