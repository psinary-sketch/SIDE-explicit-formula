/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Dedekind.lean
THIS PROGRAMME'S WORK (act b631, ruling (R241)(3) and the author's answer before b631's seal; W-ORD-DEDEKIND-INSTANCE) -- NOT
VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE DEDEKIND ZETA OF ℚ(ζ_q) AS A CONFIGURATION OF THE SCHEMA. `DedekindConfig q` is the schema's sum (`Product.sum`) of ζ's
configuration -- the trivial character's summand, its arithmetic side carrying the pole term (`zetaWeilConfig`, `zeta_rhs_pole`) --
and the family's summed configuration over the non-trivial characters mod `q` at their primitive inducers (`Family.familyConfig`).
`DedekindTheorem q` is the instance's statement as a Prop.

THE SPLIT, BY THE AUTHOR'S ANSWER. `dedekind_instance` -- Weil positivity of the summed configuration holds exactly when ζ's
target and every family target hold -- needs NO premise: it is the family theorem with the trivial summand added, by the product
lemma (`Product.productLemma_holds`) and `Family.family_theorem` (itself `finsetSum_productLemma` through `finsetSum_target_iff`).
`dedekind_rhs` reads the summed arithmetic side as the Dedekind reading's sum -- the trivial summand in the family's form and every
non-trivial character mod `q` at its own level -- and takes EXACTLY the two premises of (R213)(3)(d), `Family.TrivialSummandPremise`
and `Family.EulerFactorPremise q`, as Family.lean declares them since v0.21, and uses both; they are extended here, not re-declared,
and NOTHING HERE DISCHARGES EITHER. `dedekind_three`: the statement at `q = 3`, by `rfl`, after `Family.family_three_statement`.

THE CEILING: the instance's positivity equivalence is the family theorem with the trivial summand added and needs no premise; the two
premises are what it costs to read the summed side as the Dedekind zeta's, and they sit on `dedekind_rhs` where they are used. Every
statement here is about the schema's summed configuration. Nothing here proves RH or GRH, identifies the sum with a Dedekind zeta
function, or locates any zero.
-/
import SIDEExplicitFormula.Schema.Family

open Complex
open Classical

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Dedekind

open B321 GRHWeil Family

section dedekind

variable (q : ℕ) [NeZero q]

/-- **THE SUMMED CONFIGURATION OF THE DEDEKIND READING**: ζ's configuration, its pole term carried, summed with the family's. -/
def DedekindConfig : WeilConfig := Product.sum zetaWeilConfig (familyConfig q)

/-- **THE INSTANCE'S STATEMENT, AS A PROP**: Weil positivity of the summed configuration holds exactly when ζ's target and the
target of every character of the family hold. -/
def DedekindTheorem : Prop :=
  h2_sign_cfg (DedekindConfig q) ↔ zetaWeilConfig.target ∧ ∀ χ ∈ family q, GRH_chi χ.primitiveCharacter

/-- **(R241)(3), THE INSTANCE, WITH NO PREMISE**: the family theorem with the trivial summand added, by the product lemma. -/
theorem dedekind_instance :
    h2_sign_cfg (DedekindConfig q) ↔ zetaWeilConfig.target ∧ ∀ χ ∈ family q, GRH_chi χ.primitiveCharacter :=
  (Product.productLemma_holds zetaWeilConfig (familyConfig q)).trans
    (and_congr (h2_sign_cfg_iff_target zetaWeilConfig) (family_theorem q))

/-- **THE SUMMED ARITHMETIC SIDE AS THE DEDEKIND READING'S, ON THE TWO PREMISES**: under `TrivialSummandPremise` (the trivial
summand in the family's form, without the pole term) and `EulerFactorPremise q` (every non-trivial character mod `q` with its
primitive inducer's arithmetic side), the summed side is the trivial summand's plus every non-trivial character's at its own level.
Both premises are used; neither is discharged. -/
theorem dedekind_rhs (hT : TrivialSummandPremise) (hE : EulerFactorPremise q) (k : ℝ → ℂ) :
    (DedekindConfig q).rhs k
      = (archTerm_chi (1 : DirichletCharacter ℂ 1) k - primeSum_chi (1 : DirichletCharacter ℂ 1) k)
        + ∑ χ ∈ family q, (archTerm_chi χ k - primeSum_chi χ k) := by
  unfold DedekindConfig
  rw [Product.sum_rhs, hT k, familyConfig_arith q k]
  congr 1
  exact Finset.sum_congr rfl fun χ hχ => (hE χ ((mem_family q χ).mp hχ) k).symm

end dedekind

/-- **The statement at q = 3 is the instance's**, by definition. -/
theorem dedekind_three :
    DedekindTheorem 3 = (h2_sign_cfg (DedekindConfig 3) ↔ zetaWeilConfig.target ∧ ∀ χ ∈ family 3, GRH_chi χ.primitiveCharacter) :=
  rfl

end Dedekind
end Schema
end SIDEExplicitFormula
