/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/FromCoefficients.lean
THIS PROGRAMME'S WORK (act b770, ruling (R380)(4)(b); relay data/b770_plan.txt (4)(b)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

A ZERO OFF THE LINE FROM THE COEFFICIENTS. Where every point of a configuration of the wide class lies on the line `Re s = 1/2`, the
real part of its zero sum at each `k` of classK is at least `0`: each term is a multiplicity times a squared modulus, by the route of
`online_imp_h2_sign_cfg` (Schema/Config.lean :52-:74) over `zeroSideQ`'s terms. The configuration of the control's zeros, `zqZeroConfig`,
has its zero sum equal to its arithmetic side at each such `k` (`EF.zq_explicit_formula_instance`), and that side has negative real part
at the test function of `Window.controlFailureExists`; so `zqZeroConfig` has a point off the line, the statement of `zq_offline_zero`
proved by another road. This file imports nothing under Schema/ZQ/OffZero/. No zero is located and none is computed.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.Main
import SIDEExplicitFormula.Window.ArithNeg

open Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

/-- **The zero sum's real part on the line**: where every point of a configuration `Z` of the wide class has real part `1/2`, the real
part of its zero sum at each `k` of classK is at least `0`, each term a multiplicity times a squared modulus. -/
theorem online_imp_zeroSideQ_nonneg (Z : WideConfig) (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) (k : ℝ → ℂ)
    (hk : B321.classK k) : 0 ≤ (zeroSideQ Z k).re := by
  have hz : (0 : ℂ) ≤ zeroSideQ Z k := by
    obtain ⟨_, _, _, h, hh, hhs, rfl⟩ := hk
    unfold zeroSideQ
    refine tsum_nonneg fun ρ => ?_
    have hre : (ρ : ℂ).re = 1 / 2 := hon (ρ : ℂ) ρ.2
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
    have hm : (0 : ℂ) ≤ (Z.mult (ρ : ℂ) : ℂ) := by
      exact Nat.cast_nonneg _
    rw [hterm]
    exact mul_nonneg hm (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  have h0 := (Complex.le_def.mp hz).1
  rw [Complex.zero_re] at h0
  exact h0

namespace ZQ

/-- **A zero off the line from the coefficients**: the configuration of the control's zeros has a point whose real part is not `1/2`.
Were every point on the line, the real part of the zero sum at the test function of `Window.controlFailureExists` would be at least `0`
(`online_imp_zeroSideQ_nonneg`); by the explicit formula at the instance it equals the real part of the arithmetic side there, which is
below `0`. The statement of `zq_offline_zero`, proved by another road: no zero is located. -/
theorem zq_offline_from_coefficients : ∃ ρ ∈ zqZeroConfig.carrier, ρ.re ≠ 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk, _, hneg⟩ := SIDEExplicitFormula.Window.controlFailureExists
  have h0 := online_imp_zeroSideQ_nonneg zqZeroConfig hcon k hk
  obtain ⟨he, hc, hs, _⟩ := hk
  rw [EF.zq_explicit_formula_instance k hc hs he] at h0
  exact absurd hneg (not_lt.mpr h0)

end ZQ
end Schema
end SIDEExplicitFormula
