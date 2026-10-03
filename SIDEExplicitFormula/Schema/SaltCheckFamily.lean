/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/SaltCheckFamily.lean
THIS PROGRAMME'S WORK (act b603, ruling (R213)(3), H37a-H37b) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE FAMILY FORM, COMPILED. The finite sum of Schema/Family.lean is read over configurations that satisfy
every field of `Schema.WeilConfig`:

* **`finsetSum_satisfiable`** -- a finite sum with a point, Weil-positive on classK (b600's configuration on the line,
  summed over a one-element Finset).
* **`finsetSum_summand_load_bearing`** -- a finite sum over a two-element Finset, one summand Weil-positive on classK,
  the sum not (b600's configuration on the line beside b590's toy pair off the line): no single summand's criterion
  decides the sum's.
* **`family_one_empty`**, **`family_one_h2`** -- the boundary of the family: mod 1 the only character is the trivial one
  (Mathlib's `level_one`), so the family is empty, its summed configuration the empty one, and both sides of the family
  theorem hold vacuously -- the theorem's content lives at the moduli with a non-trivial character.

These are models of the schema's FORM, not of ζ or of any L-function: nothing here is a statement about the zeros of
`riemannZeta`, of any `LFunction χ`, or of any Dedekind zeta function. 0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Schema.Family
import SIDEExplicitFormula.SaltCheckProduct

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Family
namespace SaltCheck

open Product.SaltCheck

/-- **H37a, NON-VACUITY**: a finite sum with a point, Weil-positive on classK. -/
theorem finsetSum_satisfiable :
    ∃ (s : Finset Unit) (f : Unit → WeilConfig), h2_sign_cfg (finsetSum s f) ∧ (finsetSum s f).carrier.Nonempty := by
  refine ⟨{()}, fun _ => onCfg, (finsetSum_productLemma _ _).mpr fun _ _ => onCfg_h2, Simplicity.SaltCheck.pt, ?_⟩
  show Simplicity.SaltCheck.pt ∈ (Product.sum onCfg emptyCfg).carrier
  exact Or.inl (Set.mem_singleton _)

/-- **H37a, EVERY SUMMAND IS LOAD-BEARING**: one summand Weil-positive, the finite sum not. -/
theorem finsetSum_summand_load_bearing :
    ∃ (s : Finset Bool) (f : Bool → WeilConfig), false ∈ s ∧ h2_sign_cfg (f false) ∧ ¬ h2_sign_cfg (finsetSum s f) := by
  refine ⟨{true, false}, fun b => cond b offCfg onCfg, by simp, onCfg_h2, fun h => ?_⟩
  exact offCfg_not_h2 ((finsetSum_productLemma _ _).mp h true (by simp))

/-- **The boundary**: mod 1 the family is empty. -/
theorem family_one_empty : family 1 = ∅ :=
  Finset.eq_empty_of_forall_notMem fun χ h => (mem_family 1 χ).mp h (DirichletCharacter.level_one χ)

/-- **The boundary**: mod 1 the summed configuration is Weil-positive, both sides of the family theorem vacuous. -/
theorem family_one_h2 : h2_sign_cfg (familyConfig 1) := by
  unfold familyConfig
  rw [family_one_empty, finsetSum_empty]
  exact emptyCfg_h2

end SaltCheck
end Family
end Schema
end SIDEExplicitFormula
