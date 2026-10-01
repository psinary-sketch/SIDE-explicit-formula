/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Config.lean
THIS PROGRAMME'S WORK (act b573, ruling (R183)(4)(a)-(b); W-ORD-GRH-WEIL, act eight) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE GENERIC SCHEMA, ITS STRUCTURE AND ITS FORWARD HALF. `WeilConfig` extends Zeta23's `ZeroConfig` by the three fields the
b572 lemma list names (relay data/b572_lemmas.txt; the types read off the consuming lemmas, relay data/b573_fields.txt):
EF -- an arithmetic side `rhs` equal to the zero side on even `k ∈ C_c²` (b321_identity's type); COUNT -- the local count
`HCount` (as `dominant_summable` consumes it); TARGET -- a Prop equivalent to the strip form (the seam left to the instance).
Weil positivity on classK over the structure is `h2_sign_cfg`; the forward half `online → h2_sign_cfg` is RHChain's argument.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.PowerLimit

open Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

/-- **A configuration with an explicit formula and a local count**: Zeta23's `ZeroConfig` and three fields. -/
structure WeilConfig extends Zeta23.ZeroConfig where
  /-- EF: the arithmetic side of the explicit formula -/
  rhs : (ℝ → ℂ) → ℂ
  /-- EF: the zero side equals it on even `k ∈ C_c²` (b321_identity's type at its consuming site) -/
  ef : ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k → (∀ x : ℝ, k (-x) = k x) →
    (∑' ρ : carrier, (mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) = rhs k
  /-- COUNT: the local count, as dominant_summable consumes it (HCount, RestBound.lean :44) -/
  count : ∃ A₀ : ℝ, B321.HCount ⟨carrier, mult, one_le_mult, strip, reflect_mem, mult_reflect, finite_window⟩ A₀
  /-- TARGET: the instance's statement of the zeros' location, equivalent to the strip form (the seam left to the instance) -/
  target : Prop
  target_iff : target ↔ ∀ ρ ∈ carrier, ρ.re = 1 / 2

/-- The zero side over the structure. -/
def zeroSide_cfg (C : WeilConfig) (k : ℝ → ℂ) : ℂ :=
  ∑' ρ : C.carrier, (C.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

/-- **Weil positivity on classK over the structure.** -/
def h2_sign_cfg (C : WeilConfig) : Prop := ∀ k : ℝ → ℂ, B321.classK k → 0 ≤ C.rhs k

/-- The strip form over the structure: every point of the configuration is on the line. -/
def online (C : WeilConfig) : Prop := ∀ ρ ∈ C.carrier, ρ.re = 1 / 2

/-- b321's identity over the structure, for `k` in classK. -/
theorem zeroSide_cfg_eq (C : WeilConfig) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    (he : ∀ x : ℝ, k (-x) = k x) : zeroSide_cfg C k = C.rhs k :=
  C.ef k hk hs he

/-- **The forward half over the structure**: `online C → h2_sign_cfg C`, RHChain's argument. -/
theorem online_imp_h2_sign_cfg (C : WeilConfig) : online C → h2_sign_cfg C := by
  intro hstrip k hk
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  rw [← zeroSide_cfg_eq C hc hs he]
  unfold zeroSide_cfg
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
  have hm : (0 : ℂ) ≤ (C.mult (ρ : ℂ) : ℂ) := by
    exact Nat.cast_nonneg _
  have hnn : (0 : ℂ) ≤ (C.mult (ρ : ℂ) : ℂ) * Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ)) := by
    rw [hterm]
    exact mul_nonneg hm (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  exact hnn

end Schema
end SIDEExplicitFormula
