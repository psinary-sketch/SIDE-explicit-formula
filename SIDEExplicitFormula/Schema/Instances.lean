/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Instances.lean
THIS PROGRAMME'S WORK (act b573, ruling (R183)(4)(d); W-ORD-GRH-WEIL, act eight) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE TWO INSTANCES OF THE SCHEMA. ζ: Zeta23's `zetaZeroConfig`, its arithmetic side b321's `P − PR + A` (`b321_identity`, b321Norm = 1),
its local count `zetaZeroConfig_local_count`, its target Mathlib's `RiemannHypothesis` with the seam (`rh_strip_imp_rh_holds`,
`RH_implies_on_line`). χ: `chiZeroConfig`, its arithmetic side `archTerm_chi − primeSum_chi` (`zeroSide_chi_eq`), its local count
`chiZeroConfig_local_count`, its target `GRH_chi` (`rh_strip_chi_iff_grh_chi`). For each, the schema's criterion and a check
that its statement IS the existing equivalence's statement (`rfl`). Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Converse
import SIDEExplicitFormula.Seam
import SIDEExplicitFormula.Chi.CriterionConverse

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321 GRHWeil

/-- **ζ as an instance**: the zeros of Mathlib's `riemannZeta` with b321's arithmetic side, ζ's local count, and Mathlib's
`RiemannHypothesis` as the target. -/
def zetaWeilConfig : WeilConfig :=
  { Zeta23.zetaZeroConfig with
    rhs := fun k => poleTerm k - primeSum k + archTerm k
    ef := fun k hk hs he => by
      have h := b321_identity k hk hs he
      unfold zeroSide b321Norm at h
      rw [one_mul] at h
      exact h
    count := Zeta23.RvM.zetaZeroConfig_local_count
    target := RiemannHypothesis
    target_iff := ⟨fun hRH ρ hρ => Zeta23.RH_implies_on_line hRH (by
        rw [Zeta23.zetaZeroConfig_carrier] at hρ
        exact hρ), fun h => rh_strip_imp_rh_holds h⟩ }

/-- **The schema at ζ.** -/
theorem h2_sign_cfg_zeta : h2_sign_cfg zetaWeilConfig ↔ zetaWeilConfig.target :=
  h2_sign_cfg_iff_target zetaWeilConfig

/-- **The ζ check**: the schema's statement at ζ is `h2_sign_iff_rh`'s statement, by definition. -/
theorem h2_sign_cfg_zeta_statement : (h2_sign_cfg zetaWeilConfig ↔ zetaWeilConfig.target) = (h2_sign ↔ RiemannHypothesis) :=
  rfl

variable {N : ℕ} [NeZero N]

/-- **χ as an instance**, for primitive `χ ≠ 1`: the nontrivial zeros of `LFunction χ` with the χ-explicit formula's arithmetic side,
χ's local count, and `GRH_chi χ` as the target. -/
def chiWeilConfig (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : WeilConfig :=
  { chiZeroConfig χ hχ h1 with
    rhs := fun k => archTerm_chi χ k - primeSum_chi χ k
    ef := fun _k hk hs _he => zeroSide_chi_eq hχ h1 hk hs
    count := chiZeroConfig_local_count hχ h1
    target := GRH_chi χ
    target_iff := (rh_strip_chi_iff_grh_chi hχ h1).symm }

/-- **The schema at χ.** -/
theorem h2_sign_cfg_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    h2_sign_cfg (chiWeilConfig χ hχ h1) ↔ (chiWeilConfig χ hχ h1).target :=
  h2_sign_cfg_iff_target (chiWeilConfig χ hχ h1)

/-- **The χ check**: the schema's statement at χ is `h2_sign_chi_iff_grh_chi`'s statement, by definition. -/
theorem h2_sign_cfg_chi_statement (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    (h2_sign_cfg (chiWeilConfig χ hχ h1) ↔ (chiWeilConfig χ hχ h1).target) = (h2_sign_chi χ ↔ GRH_chi χ) :=
  rfl

end Schema
end SIDEExplicitFormula
