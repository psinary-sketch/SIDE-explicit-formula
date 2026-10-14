/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/LiForward.lean
THIS PROGRAMME'S WORK (act b669, ruling (R279)(4); the χ-Li converse's forward half) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FORWARD HALF AT χ. For a primitive Dirichlet character `χ ≠ 1`, `GRH_chi χ` (GRHWeil.lean :53, the strip form over Mathlib's
`LFunction χ`) gives `0 ≤ liCoeffCfg (chiZeroConfig χ hχ h1) n` for every `n`: the carrier of `chiZeroConfig` is the zeros of
`LFunction χ` in the open strip (`IsNontrivialZeroChi`), so `GRH_chi χ` puts every one of them on the line -- the argument of
`rh_strip_chi_iff_grh_chi` (Chi/CriterionForward.lean :44), written here over the carrier -- and the generic forward half
`Schema.online_imp_liCoeffCfg_nonneg` closes it. The proof reads the configuration and no ζ object.
Nothing here proves GRH or RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.LiCfg
import SIDEExplicitFormula.Chi.ZeroConfig

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- **The forward half at χ:** `GRH_chi χ → ∀ n, 0 ≤ liCoeffCfg (chiZeroConfig χ hχ h1) n`. -/
theorem grh_chi_imp_li_nonneg_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    GRH_chi χ → ∀ n : ℕ, 0 ≤ Schema.liCoeffCfg (chiZeroConfig χ hχ h1) n := fun h =>
  Schema.online_imp_liCoeffCfg_nonneg _ (fun ρ hρ => h ρ hρ.1 hρ.2.1 hρ.2.2)

end GRHWeil
end SIDEExplicitFormula
