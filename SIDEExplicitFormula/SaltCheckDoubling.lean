/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckDoubling.lean
THIS PROGRAMME'S WORK (act b601, ruling (R211)(3), H35a) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE DOUBLING COROLLARY, COMPILED. An equivalence whose two sides the fields decided alike, or a
non-implication the fields made empty, would say nothing beyond them. `Doubling.lean` is read here over configurations
that satisfy every field of `Schema.WeilConfig`:

* **`doubling_satisfiable`** -- a configuration with a point whose doubled sum is Weil-positive on classK (b596's toy).
* **`doubling_not_forced`** -- a configuration with a point whose doubled sum is not Weil-positive on classK (b590's
  two-point toy configuration with its point `rhoE` off the line): the doubling keeps a negative criterion negative, so the
  equivalence carries weight in both directions.
* **`positivity_with_simplicity`** -- a configuration with a point, Weil-positive on classK, every point simple (b596's
  toy): within the schema positivity does not force a multiple point either, so the corollary's non-implication is not
  the stronger statement that positivity excludes simplicity.

These are models of the schema's FORM, not of ζ: nothing here is a statement about the zeros of `riemannZeta`.
0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Doubling
import SIDEExplicitFormula.SaltCheckProduct

noncomputable section

namespace SIDEExplicitFormula
namespace Doubling
namespace SaltCheck

open Schema Product

/-- **H35a, NON-VACUITY**: a configuration with a point whose doubled sum is Weil-positive on classK. -/
theorem doubling_satisfiable :
    ∃ C : WeilConfig, C.carrier.Nonempty ∧ h2_sign_cfg (sum C C) :=
  ⟨Product.SaltCheck.onCfg, ⟨Simplicity.SaltCheck.pt, Set.mem_singleton _⟩,
    (doubling_iff _).mpr Product.SaltCheck.onCfg_h2⟩

/-- **H35a, NOT FORCED**: a configuration with a point whose doubled sum is not Weil-positive on classK. -/
theorem doubling_not_forced :
    ∃ C : WeilConfig, C.carrier.Nonempty ∧ ¬ h2_sign_cfg (sum C C) :=
  ⟨Product.SaltCheck.offCfg, ⟨rhoE, Set.mem_insert rhoE _⟩,
    fun h => Product.SaltCheck.offCfg_not_h2 ((doubling_iff _).mp h)⟩

/-- **H35a, THE NON-IMPLICATION IS NOT AN EXCLUSION**: a configuration with a point, Weil-positive on classK, every point
simple. -/
theorem positivity_with_simplicity :
    ∃ C : WeilConfig, C.carrier.Nonempty ∧ h2_sign_cfg C ∧ Simplicity.allSimple C :=
  ⟨Product.SaltCheck.onCfg, ⟨Simplicity.SaltCheck.pt, Set.mem_singleton _⟩, Product.SaltCheck.onCfg_h2, fun _ _ => rfl⟩

end SaltCheck
end Doubling
end SIDEExplicitFormula
