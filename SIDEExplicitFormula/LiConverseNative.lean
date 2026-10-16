/-
SIDE-explicit-formula -- SIDEExplicitFormula/LiConverseNative.lean
THIS PROGRAMME'S WORK (act b673, ruling (R283)(5)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE NATIVE ζ CONVERSE. `li_nonneg_imp_rh_native` is the generic converse `Schema.li_nonneg_cfg_imp_online` (S5) at
`Zeta23.zetaZeroConfig`: the kernel's Li coefficient `LiWeil.LiCoeff n` is `liCoeffCfg zetaZeroConfig n` by `rfl`
(`Schema.liCoeff_eq_liCoeffCfg`), the local count is `Zeta23.RvM.zetaZeroConfig_local_count`, and the open strip is the
carrier's own (`IsNontrivialZero`). Its conclusion is Mathlib's `RiemannHypothesis`, reached through the vendored
`LiCriterion.rh_equiv_mathlib` as `LiCriterionBridge.li_nonneg_iff_rh` reaches it. It is compiled beside the vendored converse
`LiCriterion.positivity_implies_RH` (consumed by `li_nonneg_iff_rh`) and replaces nothing: the vendored route runs through the
Taylor coefficients of ξ, this one through the power sums of the zeros.
Nothing here proves RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.LiConverseCfg
import SIDEExplicitFormula.LiCriterionBridge
import Zeta23.RvM.LocalCount

noncomputable section

namespace SIDEExplicitFormula
namespace LiConverseNative

open Zeta23

/-- **The native ζ converse:** `(∀ n, 0 ≤ LiCoeff n) → RiemannHypothesis`, by the power-sum route over the configuration. -/
theorem li_nonneg_imp_rh_native : (∀ n : ℕ, 0 ≤ LiWeil.LiCoeff n) → RiemannHypothesis := by
  intro h
  rw [LiCriterion.rh_equiv_mathlib]
  intro s hs hstrip
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hS : B321.HStrip zetaZeroConfig := by
    unfold B321.HStrip
    exact fun ρ hρ => ⟨hρ.2.1, hρ.2.2⟩
  have hnn : ∀ n : ℕ, 0 ≤ Schema.liCoeffCfg zetaZeroConfig n := fun n => by
    rw [← Schema.liCoeff_eq_liCoeffCfg]
    exact h n
  exact Schema.li_nonneg_cfg_imp_online zetaZeroConfig (A₀ := A₀) ⟨hA₀, hloc⟩ hS hnn s ⟨hs, hstrip.1, hstrip.2⟩

end LiConverseNative
end SIDEExplicitFormula
