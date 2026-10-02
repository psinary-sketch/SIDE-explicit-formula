/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckProduct.lean
THIS PROGRAMME'S WORK (act b600, ruling (R210)(4), H34a) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE PRODUCT LEMMA, COMPILED. An equivalence whose two sides the fields decided alike would say nothing
beyond them. The sum of `Product.lean` is read here over configurations that satisfy every field of `Schema.WeilConfig`:

* **`product_satisfiable`** -- two configurations whose sum has a point and is Weil-positive on classK (two copies of
  b596's one-point toy on the line, multiplicity one).
* **`product_part_load_bearing`** -- two configurations, the first Weil-positive on classK, whose sum is not (b596's toy
  beside b590's two-point toy configuration with its point `rhoE` off the line): one part's criterion does not decide the
  sum's, so the second conjunct of the product lemma carries weight.
* **`product_sum_not_forced`** -- the same with the parts in the other order.

These are models of the schema's FORM, not of ζ or of any L-function: nothing here is a statement about the zeros of
`riemannZeta`, of an Epstein zeta function, or of any product of L-functions. 0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Product
import SIDEExplicitFormula.SaltCheckSimplicity

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Product
namespace SaltCheck

open Schema B321

/-- **The configuration on the line**: b596's one point `1/2 + 14 i`, multiplicity one. -/
def onCfg : WeilConfig := Simplicity.SaltCheck.toyCfg 1 le_rfl

theorem onCfg_h2 : h2_sign_cfg onCfg :=
  online_imp_h2_sign_cfg _ (Simplicity.SaltCheck.toy_online 1 le_rfl)

/-- **The configuration off the line**: b590's toy pair `rhoE`, `reflect rhoE`, the target the strip form. -/
def offCfg : WeilConfig :=
  epsteinConfig SaltCheckEpstein.toyZ SaltCheckEpstein.toyRhs SaltCheckEpstein.toy_premises

theorem offCfg_not_h2 : ¬ h2_sign_cfg offCfg := fun h => by
  have ht : offCfg.target := (h2_sign_cfg_iff_target offCfg).mp h
  exact rhoE_re_ne_half (ht rhoE (Set.mem_insert rhoE _))

/-- **H34a, NON-VACUITY**: a sum with a point, Weil-positive on classK. -/
theorem product_satisfiable :
    ∃ C₁ C₂ : WeilConfig, h2_sign_cfg (sum C₁ C₂) ∧ (sum C₁ C₂).carrier.Nonempty :=
  ⟨onCfg, onCfg, (productLemma_holds onCfg onCfg).mpr ⟨onCfg_h2, onCfg_h2⟩,
    ⟨Simplicity.SaltCheck.pt, Or.inl (Set.mem_singleton _)⟩⟩

/-- **H34a, THE SECOND PART IS LOAD-BEARING**: the first part Weil-positive, the sum not. -/
theorem product_part_load_bearing :
    ∃ C₁ C₂ : WeilConfig, h2_sign_cfg C₁ ∧ ¬ h2_sign_cfg (sum C₁ C₂) :=
  ⟨onCfg, offCfg, onCfg_h2, fun h => offCfg_not_h2 ((productLemma_holds onCfg offCfg).mp h).2⟩

/-- **H34a, THE FIRST PART IS LOAD-BEARING**: the second part Weil-positive, the sum not. -/
theorem product_sum_not_forced :
    ∃ C₁ C₂ : WeilConfig, h2_sign_cfg C₂ ∧ ¬ h2_sign_cfg (sum C₁ C₂) :=
  ⟨offCfg, onCfg, onCfg_h2, fun h => offCfg_not_h2 ((productLemma_holds offCfg onCfg).mp h).1⟩

end SaltCheck
end Product
end SIDEExplicitFormula
