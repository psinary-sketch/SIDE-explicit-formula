/-
SIDE-explicit-formula -- SIDEExplicitFormula/Doubling.lean
THIS PROGRAMME'S WORK (act b601, ruling (R211)(3); the doubling corollary of the product lemma) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE DOUBLING COROLLARY. For a configuration `C` of the schema (`Schema.WeilConfig`), the sum of `C` with itself
(`Product.sum C C`) has multiplicity `2 · m` at every point of `C`'s carrier, and is Weil-positive on classK exactly when
`C` is -- `productLemma_holds` with both parts `C`. So a configuration's multiplicities can be doubled without moving its
criterion, and the schema's positivity Prop (`Schema.h2_sign_cfg`) does not imply the schema's simplicity Prop
(`Simplicity.allSimple`): `positivity_not_imp_simplicity`, exhibited by `doubledToy`, the sum of b596's one-point toy on the
line (`Simplicity.SaltCheck.toyCfg 1`) with itself, positive and with its point of multiplicity two. The salt-check is
SIDEExplicitFormula/SaltCheckDoubling.lean. This is a statement about the schema's form: nothing here is a statement about
the zeros of `riemannZeta`, proves or refutes the simplicity of any zero, proves RH, or locates any zero.
-/
import SIDEExplicitFormula.Product
import SIDEExplicitFormula.SaltCheckSimplicity

noncomputable section

namespace SIDEExplicitFormula
namespace Doubling

open Schema Product Simplicity

/-- The carrier of the doubled configuration is the carrier. -/
theorem sum_self_carrier (C : WeilConfig) : (sum C C).carrier = C.carrier :=
  Set.union_self C.carrier

/-- **The multiplicities doubled**: at every point of `C`'s carrier, the sum of `C` with itself has multiplicity `2 · m`. -/
theorem sum_self_mult (C : WeilConfig) (ρ : ℂ) (hρ : ρ ∈ C.carrier) : (sum C C).mult ρ = 2 * C.mult ρ := by
  rw [sum_mult]
  unfold onMult
  rw [if_pos hρ]
  omega

/-- **The criterion unmoved**: the sum of `C` with itself is Weil-positive on classK exactly when `C` is
(`productLemma_holds` with both parts `C`). -/
theorem doubling_iff (C : WeilConfig) : h2_sign_cfg (sum C C) ↔ h2_sign_cfg C :=
  (productLemma_holds C C).trans and_self_iff

/-- **THE DOUBLING COROLLARY, AS A PROP**: for every configuration of the schema, the sum with itself doubles every
multiplicity on the carrier and keeps Weil positivity on classK unchanged. -/
def DoublingCorollary : Prop :=
  ∀ C : WeilConfig, (∀ ρ ∈ C.carrier, (sum C C).mult ρ = 2 * C.mult ρ) ∧ (h2_sign_cfg (sum C C) ↔ h2_sign_cfg C)

/-- **THE DOUBLING COROLLARY, PROVED.** -/
theorem doubling_holds : DoublingCorollary := fun C => ⟨sum_self_mult C, doubling_iff C⟩

/-- **The doubled on-line toy**: b596's one point `1/2 + 14 i` of multiplicity one, summed with itself. -/
def doubledToy : WeilConfig := sum (Simplicity.SaltCheck.toyCfg 1 le_rfl) (Simplicity.SaltCheck.toyCfg 1 le_rfl)

/-- The doubled toy's point is on its carrier. -/
theorem doubledToy_pt_mem : Simplicity.SaltCheck.pt ∈ doubledToy.carrier := Or.inl (Set.mem_singleton _)

/-- **The doubled toy has a point of multiplicity two.** -/
theorem doubledToy_mult_pt : doubledToy.mult Simplicity.SaltCheck.pt = 2 :=
  sum_self_mult (Simplicity.SaltCheck.toyCfg 1 le_rfl) Simplicity.SaltCheck.pt (Set.mem_singleton _)

/-- **The doubled toy satisfies the schema's positivity Prop.** -/
theorem doubledToy_h2_sign_cfg : h2_sign_cfg doubledToy :=
  (doubling_iff _).mpr (online_imp_h2_sign_cfg _ (Simplicity.SaltCheck.toy_online 1 le_rfl))

/-- **The doubled toy fails the schema's simplicity Prop.** -/
theorem doubledToy_not_allSimple : ¬ allSimple doubledToy := fun h => by
  have h1 := h Simplicity.SaltCheck.pt doubledToy_pt_mem
  rw [doubledToy_mult_pt] at h1
  omega

/-- The schema's positivity Prop implying the schema's simplicity Prop, as a Prop. -/
def PositivityImpliesSimplicity : Prop := ∀ C : WeilConfig, h2_sign_cfg C → allSimple C

/-- **THE NAMED COROLLARY: WITHIN THE SCHEMA, WEIL POSITIVITY DOES NOT IMPLY SIMPLICITY** -- exhibited by the doubled toy. -/
theorem positivity_not_imp_simplicity : ¬ PositivityImpliesSimplicity := fun h =>
  doubledToy_not_allSimple (h doubledToy doubledToy_h2_sign_cfg)

end Doubling
end SIDEExplicitFormula
