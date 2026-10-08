/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/DedekindRestated.lean
THIS PROGRAMME'S WORK (act b642, ruling (R252)(3)(d); W-ORD-DEDEKIND-RHS-RESTATE, OPEN_TRAILS :13495) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE DEDEKIND READING'S TRIVIAL SUMMAND, RESTATED. `TrivialSummandPremise` (Family.lean) asks ζ's arithmetic side to be the trivial
character's summand in the family's form with no pole term, and is false (`Family.not_trivialSummandPremise`). Beside it,
`TrivialSummandPremise' k` carries the pole term as a term, at a test function `k`: ζ's side is the pole term plus the trivial
character's summand. It holds at every even `k` (`trivialSummandPremise'_of_even`: the Γ terms agree and, `k` even, the two prime
sums agree), so it is not vacuous (`trivialSummandPremise'_witness`, at the constant 1).

Nothing here proves RH or GRH, identifies the sum with a Dedekind zeta function, or locates any zero.
-/
import SIDEExplicitFormula.Schema.Dedekind
import SIDEExplicitFormula.Schema.FamilyPremises

open Complex
open Classical

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Dedekind

open B321 GRHWeil Family

/-- **THE TRIVIAL SUMMAND, RESTATED (b642, `(R252)`(3)(d))**: at a test function `k`, ζ's arithmetic side is the trivial character's
summand in the family's form WITH the pole term carried as a term, rather than required to vanish (`TrivialSummandPremise`, refuted by
`Family.not_trivialSummandPremise`). -/
def TrivialSummandPremise' (k : ℝ → ℂ) : Prop :=
  zetaWeilConfig.rhs k = poleTerm k + (archTerm_chi (1 : DirichletCharacter ℂ 1) k - primeSum_chi (1 : DirichletCharacter ℂ 1) k)

/-- **The restated premise holds at every even test function**: the Γ terms agree and, `k` even, the two prime sums agree. -/
theorem trivialSummandPremise'_of_even (k : ℝ → ℂ) (he : ∀ x, k (-x) = k x) : TrivialSummandPremise' k := by
  unfold TrivialSummandPremise'
  rw [zeta_rhs_pole, archTerm_chi_one]
  have hP : primeSum_chi (1 : DirichletCharacter ℂ 1) k = primeSum k := by
    unfold primeSum_chi primeSum
    refine tsum_congr fun n => ?_
    rw [one_apply_nat, map_one, he]
    ring
  rw [hP]
  ring

/-- **THE NON-VACUITY WITNESS**: the constant test function 1 satisfies the restated premise. -/
theorem trivialSummandPremise'_witness : TrivialSummandPremise' (fun _ => 1) :=
  trivialSummandPremise'_of_even _ fun _ => rfl

/-- **THE SUMMED ARITHMETIC SIDE AS THE DEDEKIND READING'S, ON THE RESTATED PREMISE**: under `TrivialSummandPremise' k` (the trivial
summand with its pole term carried) and `EulerFactorPremise q`, the summed side is the pole term plus the trivial summand's plus every
non-trivial character's at its own level. Both premises carry a witness (`trivialSummandPremise'_witness`; `eulerFactorPremise_three`).
The v0.25 `dedekind_rhs`, on the refuted `TrivialSummandPremise`, is kept. -/
theorem dedekind_rhs' (q : ℕ) [NeZero q] (k : ℝ → ℂ) (hT : TrivialSummandPremise' k) (hE : EulerFactorPremise q) :
    (DedekindConfig q).rhs k
      = poleTerm k + (archTerm_chi (1 : DirichletCharacter ℂ 1) k - primeSum_chi (1 : DirichletCharacter ℂ 1) k)
        + ∑ χ ∈ family q, (archTerm_chi χ k - primeSum_chi χ k) := by
  unfold DedekindConfig
  rw [Product.sum_rhs, hT, familyConfig_arith q k]
  congr 1
  exact Finset.sum_congr rfl fun χ hχ => (hE χ ((mem_family q χ).mp hχ) k).symm

/-- **`dedekind_three`, re-checked at v0.26**: the statement at `q = 3` is the instance's, by definition. -/
theorem dedekind_three_v026 :
    DedekindTheorem 3 = (h2_sign_cfg (DedekindConfig 3) ↔ zetaWeilConfig.target ∧ ∀ χ ∈ family 3, GRH_chi χ.primitiveCharacter) :=
  rfl

end Dedekind
end Schema
end SIDEExplicitFormula
