/-
SIDE-explicit-formula -- SIDEExplicitFormula/Product.lean
THIS PROGRAMME'S WORK (act b600, ruling (R210)(4); W-ORD-GRH-WEIL REMAINDER 5, OPEN_TRAILS :12136) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE PRODUCT LEMMA, AS THE WORK-ORDER STATES IT. For two configurations of the schema (`Schema.WeilConfig`), the sum --
carrier the union, multiplicities added (each configuration's multiplicity read on its own carrier, Zeta23's `mult`
being irrelevant off it), arithmetic sides added, targets conjoined -- is a configuration of the schema, and its
criterion is the conjunction of the two, by `h2_sign_cfg_iff_target` (Schema/Converse.lean :265). The one step of
substance is the summed explicit formula `sum_ef`: each zero side is summable by the count its configuration carries
(`Zeta23.WeilEF.EF_zero_sum_summable_gen`), so the zero side over the union is the two zero sides added. The count of
the sum is the two counts added (`sumZ_N`), `A₀` the sum of the two. `ProductLemma` is the statement as a Prop;
`productLemma_holds` proves it. The salt-check is SIDEExplicitFormula/SaltCheckProduct.lean. A configuration here is
the schema's form: nothing in this file names an L-function, identifies a sum with a Dedekind zeta function, proves RH
or GRH, or locates any zero.
-/
import SIDEExplicitFormula.Schema.Converse
import Zeta23.WeilEF.ZeroSummability

open Complex
open Classical

noncomputable section

namespace SIDEExplicitFormula
namespace Product

open Schema B321

/-- The reflection is an involution. -/
theorem reflect_reflect (ρ : ℂ) : Zeta23.reflect (Zeta23.reflect ρ) = ρ := by
  unfold Zeta23.reflect
  rw [map_sub, map_one, Complex.conj_conj, sub_sub_cancel]

/-- A configuration's carrier is closed under the reflection both ways. -/
theorem reflect_mem_iff (C : WeilConfig) (ρ : ℂ) : Zeta23.reflect ρ ∈ C.carrier ↔ ρ ∈ C.carrier := by
  constructor
  · intro h
    have h' := C.reflect_mem _ h
    rwa [reflect_reflect] at h'
  · exact C.reflect_mem ρ

/-- **A configuration's multiplicity read on its own carrier** (zero off it). -/
def onMult (C : WeilConfig) (ρ : ℂ) : ℕ := if ρ ∈ C.carrier then C.mult ρ else 0

theorem onMult_reflect (C : WeilConfig) (ρ : ℂ) : onMult C (Zeta23.reflect ρ) = onMult C ρ := by
  unfold onMult
  by_cases h : ρ ∈ C.carrier
  · rw [if_pos ((reflect_mem_iff C ρ).mpr h), if_pos h, C.mult_reflect ρ h]
  · rw [if_neg (fun h' => h ((reflect_mem_iff C ρ).mp h')), if_neg h]

/-- **The multiplicity of the sum**: the two multiplicities added, each on its own carrier. -/
def sumMult (C₁ C₂ : WeilConfig) (ρ : ℂ) : ℕ := onMult C₁ ρ + onMult C₂ ρ

/-- **The zero configuration of the sum**: the carriers' union, the multiplicities added. -/
def sumZ (C₁ C₂ : WeilConfig) : Zeta23.ZeroConfig where
  carrier := C₁.carrier ∪ C₂.carrier
  mult := sumMult C₁ C₂
  one_le_mult := fun ρ hρ => by
    unfold sumMult onMult
    rcases hρ with h | h
    · rw [if_pos h]
      exact le_trans (C₁.one_le_mult ρ h) (Nat.le_add_right _ _)
    · rw [if_pos h]
      exact le_trans (C₂.one_le_mult ρ h) (Nat.le_add_left _ _)
  strip := fun ρ hρ => hρ.elim (C₁.strip ρ) (C₂.strip ρ)
  reflect_mem := fun ρ hρ =>
    hρ.elim (fun h => Or.inl (C₁.reflect_mem ρ h)) (fun h => Or.inr (C₂.reflect_mem ρ h))
  mult_reflect := fun ρ _ => by
    unfold sumMult
    rw [onMult_reflect C₁ ρ, onMult_reflect C₂ ρ]
  finite_window := fun T₁ T₂ => by
    rw [Set.union_inter_distrib_right]
    exact (C₁.finite_window T₁ T₂).union (C₂.finite_window T₁ T₂)

/-- **The count of the sum is the two counts added**, on every window. -/
theorem sumZ_N (C₁ C₂ : WeilConfig) (T₁ T₂ : ℝ) :
    (sumZ C₁ C₂).N T₁ T₂ = C₁.N T₁ T₂ + C₂.N T₁ T₂ := by
  unfold Zeta23.ZeroConfig.N
  rw [finsum_mem_def, finsum_mem_def, finsum_mem_def]
  have h1 : (Function.support ((C₁.window T₁ T₂).indicator C₁.mult)).Finite :=
    (C₁.finite_window T₁ T₂).subset Set.support_indicator_subset
  have h2 : (Function.support ((C₂.window T₁ T₂).indicator C₂.mult)).Finite :=
    (C₂.finite_window T₁ T₂).subset Set.support_indicator_subset
  rw [← finsum_add_distrib h1 h2]
  congr 1
  funext ρ
  simp only [Set.indicator_apply, Zeta23.ZeroConfig.window, sumZ, sumMult, onMult, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq]
  by_cases a : ρ ∈ C₁.carrier <;> by_cases b : ρ ∈ C₂.carrier <;>
    by_cases c : (T₁ < ρ.im ∧ ρ.im ≤ T₂) <;> simp [a, b, c]

/-- **COUNT for the sum**: `HCount` with `A₀` the two constants added. -/
theorem sumZ_count (C₁ C₂ : WeilConfig) : ∃ A₀ : ℝ, HCount (sumZ C₁ C₂) A₀ := by
  obtain ⟨A₁, hA₁, hl₁⟩ := C₁.count
  obtain ⟨A₂, hA₂, hl₂⟩ := C₂.count
  refine ⟨A₁ + A₂, by linarith, fun t => ?_⟩
  have e₁ : (C₁.N t (t + 1) : ℝ) ≤ A₁ * Real.log (|t| + 3) := hl₁ t
  have e₂ : (C₂.N t (t + 1) : ℝ) ≤ A₂ * Real.log (|t| + 3) := hl₂ t
  rw [sumZ_N, Nat.cast_add, add_mul]
  linarith

/-- **Each zero side is summable**, by the count its configuration carries. -/
theorem zeroSide_summable (C : WeilConfig) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    Summable (fun ρ : C.carrier => (C.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := C.count
  exact Zeta23.WeilEF.EF_zero_sum_summable_gen C.toZeroConfig hA₀ hloc hk hs

/-- **THE SUMMED EXPLICIT FORMULA**: on even `k ∈ C_c²` the zero side over the union, with the multiplicities added,
is the two arithmetic sides added. -/
theorem sum_ef (C₁ C₂ : WeilConfig) (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    (he : ∀ x : ℝ, k (-x) = k x) :
    (∑' ρ : (sumZ C₁ C₂).carrier, ((sumZ C₁ C₂).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ))
      = C₁.rhs k + C₂.rhs k := by
  rw [← C₁.ef k hk hs he, ← C₂.ef k hk hs he]
  set F : ℂ → ℂ := fun ρ => Zeta23.paperFT k (Zeta23.gammaOf ρ) with hF
  have s₁ := (summable_subtype_iff_indicator (f := fun ρ => (C₁.mult ρ : ℂ) * F ρ) (s := C₁.carrier)).mp
    (zeroSide_summable C₁ hk hs)
  have s₂ := (summable_subtype_iff_indicator (f := fun ρ => (C₂.mult ρ : ℂ) * F ρ) (s := C₂.carrier)).mp
    (zeroSide_summable C₂ hk hs)
  rw [tsum_subtype (sumZ C₁ C₂).carrier (fun ρ => ((sumZ C₁ C₂).mult ρ : ℂ) * F ρ),
    tsum_subtype C₁.carrier (fun ρ => (C₁.mult ρ : ℂ) * F ρ),
    tsum_subtype C₂.carrier (fun ρ => (C₂.mult ρ : ℂ) * F ρ), ← s₁.tsum_add s₂]
  congr 1
  funext ρ
  simp only [Set.indicator_apply, sumZ, sumMult, onMult, Set.mem_union]
  by_cases a : ρ ∈ C₁.carrier <;> by_cases b : ρ ∈ C₂.carrier <;> simp [a, b, add_mul]

/-- The target of the sum, the conjunction, is the strip form over the union. -/
theorem sum_target_iff (C₁ C₂ : WeilConfig) :
    (C₁.target ∧ C₂.target) ↔ ∀ ρ ∈ (sumZ C₁ C₂).carrier, ρ.re = 1 / 2 := by
  rw [C₁.target_iff, C₂.target_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ ρ hρ
    rcases (hρ : ρ ∈ C₁.carrier ∪ C₂.carrier) with h | h
    exacts [h₁ ρ h, h₂ ρ h]
  · intro h
    exact ⟨fun ρ hρ => h ρ (Or.inl hρ), fun ρ hρ => h ρ (Or.inr hρ)⟩

/-- **THE SUM OF TWO CONFIGURATIONS OF THE SCHEMA** (the work-order's object): carrier the union, multiplicities
added, arithmetic sides added, targets conjoined. -/
def sum (C₁ C₂ : WeilConfig) : WeilConfig where
  toZeroConfig := sumZ C₁ C₂
  rhs := fun k => C₁.rhs k + C₂.rhs k
  ef := sum_ef C₁ C₂
  count := sumZ_count C₁ C₂
  target := C₁.target ∧ C₂.target
  target_iff := sum_target_iff C₁ C₂

theorem sum_carrier (C₁ C₂ : WeilConfig) : (sum C₁ C₂).carrier = C₁.carrier ∪ C₂.carrier := rfl

theorem sum_mult (C₁ C₂ : WeilConfig) (ρ : ℂ) : (sum C₁ C₂).mult ρ = onMult C₁ ρ + onMult C₂ ρ := rfl

theorem sum_rhs (C₁ C₂ : WeilConfig) (k : ℝ → ℂ) : (sum C₁ C₂).rhs k = C₁.rhs k + C₂.rhs k := rfl

theorem sum_target (C₁ C₂ : WeilConfig) : (sum C₁ C₂).target ↔ C₁.target ∧ C₂.target := Iff.rfl

/-- **THE PRODUCT LEMMA, AS A PROP**: for any two configurations of the schema, Weil positivity on classK of their sum
is the conjunction of the two. -/
def ProductLemma : Prop :=
  ∀ C₁ C₂ : WeilConfig, h2_sign_cfg (sum C₁ C₂) ↔ h2_sign_cfg C₁ ∧ h2_sign_cfg C₂

/-- **The criterion of the sum is the conjunction of the two targets**, by `h2_sign_cfg_iff_target` at the sum. -/
theorem h2_sign_cfg_sum_iff_targets (C₁ C₂ : WeilConfig) :
    h2_sign_cfg (sum C₁ C₂) ↔ C₁.target ∧ C₂.target :=
  h2_sign_cfg_iff_target (sum C₁ C₂)

/-- **THE PRODUCT LEMMA, PROVED.** -/
theorem productLemma_holds : ProductLemma := fun C₁ C₂ => by
  rw [h2_sign_cfg_sum_iff_targets, h2_sign_cfg_iff_target, h2_sign_cfg_iff_target]

end Product
end SIDEExplicitFormula
