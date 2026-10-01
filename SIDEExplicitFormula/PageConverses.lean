/-
SIDE-explicit-formula -- SIDEExplicitFormula/PageConverses.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(2); the page THE_CLAUSE_AND_ITS_COMPILED_FACES.md) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE TWO CONVERSES THE PAGE LACKED. At v0.10 two of the page's faces reach Mathlib's `RiemannHypothesis` by a compiled
implication only: `Register4_positivity LiCoeff` (ResidueDischarge.lean :41) and the nonnegativity of the real parts of
Bulka's Taylor coefficients (`positivity_implies_RH`, Vendored/Bulka Lc/LiCriterion/ReverseDirection.lean :413). Each
converse is a composition of compiled pieces:
(C1) `RiemannHypothesis → Register4_positivity LiCoeff`, from `rh_imp_li_nonneg` (LiWeil.lean :267);
(C2) the iff, with `register4_positivity_liCoeff_imp_rh`;
(C3) `RiemannHypothesis → ∀ n, 0 ≤ (taylorCoeff riemannXi n).re`, from `rh_imp_li_nonneg` at `n + 1` through
     `li_coeff_eq_taylorCoeff` (LiCriterionBridge.lean :149);
(C4) the iff, with `positivity_implies_RH` through `rh_equiv_mathlib`.
No new analysis. Nothing here proves RH.
-/
import SIDEExplicitFormula.ResidueDischarge

noncomputable section

namespace SIDEExplicitFormula
namespace PageConverses

open LiWeil ResidueDischarge

/-- **(C1)** Mathlib's `RiemannHypothesis` gives the restated register-four positivity of the Li coefficients. -/
theorem rh_imp_register4_positivity_liCoeff : RiemannHypothesis → Register4_positivity LiCoeff :=
  fun h n _ => rh_imp_li_nonneg h n

/-- **(C2)** The restated register-four positivity of the Li coefficients is equivalent to Mathlib's
`RiemannHypothesis`. -/
theorem register4_positivity_liCoeff_iff_rh : Register4_positivity LiCoeff ↔ RiemannHypothesis :=
  ⟨register4_positivity_liCoeff_imp_rh, rh_imp_register4_positivity_liCoeff⟩

/-- **(C3)** Mathlib's `RiemannHypothesis` gives the nonnegativity of the real parts of Bulka's Taylor coefficients of
`ξ`, by the programme's Li coefficients at `n + 1`. -/
theorem rh_imp_taylorCoeff_nonneg :
    RiemannHypothesis → ∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re := by
  intro h n
  rw [← LiCriterionBridge.li_coeff_eq_taylorCoeff]
  exact rh_imp_li_nonneg h (n + 1)

/-- **(C4)** The nonnegativity of the real parts of Bulka's Taylor coefficients of `ξ` is equivalent to Mathlib's
`RiemannHypothesis`. -/
theorem taylorCoeff_nonneg_iff_rh :
    (∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re) ↔ RiemannHypothesis :=
  ⟨fun h => LiCriterion.rh_equiv_mathlib.mpr (LiCriterion.positivity_implies_RH h), rh_imp_taylorCoeff_nonneg⟩

end PageConverses
end SIDEExplicitFormula
