/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Family.lean
THIS PROGRAMME'S WORK (act b603, ruling (R213)(3)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FAMILY FORM OVER χ MOD q, BUILT FROM THE PRODUCT LEMMA (Product.lean, v0.18).

(a) THE FINITE SUM. `Product.sum` is commutative and associative up to the equality of configurations (`cfg_ext`: carrier,
multiplicity, arithmetic side, target), so it folds over a `Finset` (Mathlib's `Finset.fold`) from the empty configuration
`emptyCfg`. `finsetSum_productLemma`, by Finset induction from `Product.sum` and `productLemma_holds`: Weil positivity on
classK of the finite sum holds exactly when it holds for every summand. `finsetSum_rhs`: the arithmetic side of the finite
sum is the finite sum of the arithmetic sides.

(b) THE FAMILY. For a modulus `q`, `family q` is the finite set of Dirichlet characters mod `q` other than the trivial one
(Mathlib's `MulChar.finite`); each `χ` in it is induced by exactly one primitive character, `χ.primitiveCharacter` of
conductor `χ.conductor ∣ q` (Mathlib, DirichletCharacter/Basic.lean), non-trivial when `χ` is. `charCfg q χ` is the schema's
χ instance (`chiWeilConfig`, Schema/Instances.lean, v0.15) at that primitive character, so the summands of `familyConfig q`
are the configurations of the primitive characters `≠ 1` of conductor dividing `q`. `family_theorem`: Weil positivity of
the summed configuration holds exactly when `GRH_chi` -- the target of each summand -- holds for every character of the
family, from (a) and `h2_sign_cfg_iff_target`. `familyConfig_arith` prints the summed arithmetic side, one
`archTerm_chi − primeSum_chi` per character, and `gammaBracket_conductor` the conductor in it, `log (N/π)` at `N` the
conductor, once per summand.

(c) ONE MODULUS. `family_three` and `family_three_statement` (`rfl`), at `q = 3`.

(d) THE DEDEKIND READING, CARRIED AS A READING. The reading of `ζ_{ℚ(ζ_q)}` as the product over all characters mod `q`
would need two premises the schema's statements do not supply; each is NAMED here as a Prop and NOTHING HERE DISCHARGES
EITHER: `TrivialSummandPremise` (the trivial character's summand in the family's form -- the kernel's instance at the
trivial character is ζ's, whose arithmetic side carries the pole term, `zeta_rhs_pole`) and `EulerFactorPremise` (each
character mod `q`, imprimitive ones included, with its primitive inducer's arithmetic side -- the kernel's χ side reads `χ`
at its own level, so at an imprimitive `χ` the terms at `p ∣ q` and the level in `log (N/π)` differ). `DedekindPremises`
joins them.

THE CEILING: every statement here is about the schema's summed configuration and the conjunction of the family's targets.
Nothing here proves RH or GRH, reduces GRH for any modulus, identifies a sum with a Dedekind zeta function, or locates any
zero.
-/
import SIDEExplicitFormula.Product
import SIDEExplicitFormula.Schema.Instances
import Mathlib.NumberTheory.MulChar.Duality

open Complex
open Classical

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Family

open B321 GRHWeil

/-! ## (a) The finite sum of configurations -/

/-- The empty zero configuration (no point; the multiplicity zero, irrelevant off the empty carrier). -/
def emptyZ : Zeta23.ZeroConfig where
  carrier := ∅
  mult := fun _ => 0
  one_le_mult := fun _ h => absurd h (Set.notMem_empty _)
  strip := fun _ h => absurd h (Set.notMem_empty _)
  reflect_mem := fun _ h => absurd h (Set.notMem_empty _)
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => Set.finite_empty.subset Set.inter_subset_left

theorem emptyZ_N (T₁ T₂ : ℝ) : emptyZ.N T₁ T₂ = 0 := by
  unfold Zeta23.ZeroConfig.N
  simp [emptyZ]

theorem emptyZ_count : HCount emptyZ 1 := by
  refine ⟨le_rfl, fun t => ?_⟩
  rw [emptyZ_N, Nat.cast_zero, one_mul]
  exact Real.log_nonneg (by linarith [abs_nonneg t])

/-- **The empty configuration of the schema**: no point, arithmetic side zero, target `True`. -/
def emptyCfg : WeilConfig where
  toZeroConfig := emptyZ
  rhs := fun _ => 0
  ef := fun _ _ _ _ => by simp [emptyZ]
  count := ⟨1, emptyZ_count⟩
  target := True
  target_iff := ⟨fun _ ρ h => absurd h (Set.notMem_empty ρ), fun _ => trivial⟩

theorem emptyCfg_h2 : h2_sign_cfg emptyCfg :=
  online_imp_h2_sign_cfg _ (fun ρ h => absurd h (Set.notMem_empty ρ))

/-- **Two configurations are equal** when carrier, multiplicity, arithmetic side and target agree (the remaining fields
are proofs). -/
theorem cfg_ext {C D : WeilConfig} (hc : C.carrier = D.carrier) (hm : C.mult = D.mult) (hr : C.rhs = D.rhs)
    (ht : C.target = D.target) : C = D := by
  obtain ⟨⟨c, m, _, _, _, _, _⟩, r, _, _, t, _⟩ := C
  obtain ⟨⟨c', m', _, _, _, _, _⟩, r', _, _, t', _⟩ := D
  cases hc
  cases hm
  cases hr
  cases ht
  rfl

/-- The multiplicity of a sum, read on its own carrier, is the two read on theirs, added. -/
theorem onMult_sum (A B : WeilConfig) (ρ : ℂ) :
    Product.onMult (Product.sum A B) ρ = Product.onMult A ρ + Product.onMult B ρ := by
  by_cases ha : ρ ∈ A.carrier <;> by_cases hb : ρ ∈ B.carrier <;>
    simp [Product.onMult, Product.sum_carrier, Product.sum_mult, ha, hb]

/-- **The sum is commutative.** -/
theorem sum_comm (A B : WeilConfig) : Product.sum A B = Product.sum B A :=
  cfg_ext (Set.union_comm A.carrier B.carrier)
    (funext fun ρ => by simp only [Product.sum_mult, Nat.add_comm])
    (funext fun k => by simp only [Product.sum_rhs, add_comm])
    (propext (@and_comm A.target B.target))

/-- **The sum is associative.** -/
theorem sum_assoc (A B C : WeilConfig) :
    Product.sum (Product.sum A B) C = Product.sum A (Product.sum B C) :=
  cfg_ext (Set.union_assoc A.carrier B.carrier C.carrier)
    (funext fun ρ => by simp only [Product.sum_mult, onMult_sum, Nat.add_assoc])
    (funext fun k => by simp only [Product.sum_rhs, add_assoc])
    (propext (@and_assoc A.target B.target C.target))

instance : Std.Commutative Product.sum := ⟨sum_comm⟩

instance : Std.Associative Product.sum := ⟨sum_assoc⟩

/-- **THE FINITE SUM OF CONFIGURATIONS** over a Finset: `Product.sum` folded, the empty configuration at the base. -/
def finsetSum {ι : Type*} (s : Finset ι) (f : ι → WeilConfig) : WeilConfig :=
  s.fold Product.sum emptyCfg f

theorem finsetSum_empty {ι : Type*} (f : ι → WeilConfig) : finsetSum ∅ f = emptyCfg :=
  Finset.fold_empty

theorem finsetSum_insert {ι : Type*} {a : ι} {s : Finset ι} (f : ι → WeilConfig) (h : a ∉ s) :
    finsetSum (insert a s) f = Product.sum (f a) (finsetSum s f) :=
  Finset.fold_insert h

/-- **(R213)(3)(a), THE PRODUCT LEMMA OVER A FINSET**: Weil positivity on classK of the finite sum holds exactly when it
holds for every summand -- by Finset induction from `Product.sum` and `productLemma_holds`. -/
theorem finsetSum_productLemma {ι : Type*} (s : Finset ι) (f : ι → WeilConfig) :
    h2_sign_cfg (finsetSum s f) ↔ ∀ i ∈ s, h2_sign_cfg (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [finsetSum_empty]
    exact ⟨fun _ i hi => absurd hi (Finset.notMem_empty i), fun _ => emptyCfg_h2⟩
  | insert a s ha ih =>
    rw [finsetSum_insert f ha, Product.productLemma_holds, ih, Finset.forall_mem_insert]

/-- The finite sum's criterion is the conjunction of the summands' targets. -/
theorem finsetSum_target_iff {ι : Type*} (s : Finset ι) (f : ι → WeilConfig) :
    h2_sign_cfg (finsetSum s f) ↔ ∀ i ∈ s, (f i).target :=
  (finsetSum_productLemma s f).trans (forall₂_congr fun i _ => h2_sign_cfg_iff_target (f i))

/-- **The arithmetic side of the finite sum** is the finite sum of the arithmetic sides. -/
theorem finsetSum_rhs {ι : Type*} (s : Finset ι) (f : ι → WeilConfig) (k : ℝ → ℂ) :
    (finsetSum s f).rhs k = ∑ i ∈ s, (f i).rhs k := by
  induction s using Finset.induction_on with
  | empty =>
    exact (congrArg (fun C : WeilConfig => C.rhs k) (finsetSum_empty f)).trans Finset.sum_empty.symm
  | insert a s ha ih =>
    rw [finsetSum_insert f ha, Product.sum_rhs, ih, Finset.sum_insert ha]

/-! ## (b) The family over χ mod q -/

section family

variable (q : ℕ) [NeZero q]

/-- A character mod a nonzero modulus has a nonzero conductor (Mathlib's `conductor_ne_zero`). -/
instance conductor_neZero (χ : DirichletCharacter ℂ q) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- **The family's characters**: the Dirichlet characters mod `q` other than the trivial one, a finite set
(Mathlib's `MulChar.finite`). -/
def family : Finset (DirichletCharacter ℂ q) :=
  (Set.toFinite {χ : DirichletCharacter ℂ q | χ ≠ 1}).toFinset

theorem mem_family (χ : DirichletCharacter ℂ q) : χ ∈ family q ↔ χ ≠ 1 := by
  simp only [family, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- **The primitive character inducing a non-trivial character is non-trivial** (Mathlib's
`changeLevel_primitiveCharacter`, `changeLevel_one`). -/
theorem primitiveCharacter_ne_one {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro hp
  apply h
  rw [← χ.changeLevel_primitiveCharacter, hp, DirichletCharacter.changeLevel_one]

/-- **The configuration of a character of the family**: the schema's χ instance at the primitive character inducing it
(the empty configuration at the trivial character, which the family excludes). -/
def charCfg (χ : DirichletCharacter ℂ q) : WeilConfig :=
  if h : χ = 1 then emptyCfg
  else chiWeilConfig χ.primitiveCharacter χ.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one q h)

theorem charCfg_of_ne (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) :
    charCfg q χ = chiWeilConfig χ.primitiveCharacter χ.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one q h) :=
  dif_neg h

/-- The target of a summand is `GRH_chi` at the primitive character. -/
theorem charCfg_target (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) :
    (charCfg q χ).target ↔ GRH_chi χ.primitiveCharacter :=
  Iff.of_eq (congrArg WeilConfig.target (charCfg_of_ne q χ h))

/-- The arithmetic side of a summand is the χ-explicit formula's, at the primitive character. -/
theorem charCfg_rhs (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) (k : ℝ → ℂ) :
    (charCfg q χ).rhs k = archTerm_chi χ.primitiveCharacter k - primeSum_chi χ.primitiveCharacter k :=
  (congrArg (fun C : WeilConfig => C.rhs k) (charCfg_of_ne q χ h)).trans rfl

/-- **THE SUMMED CONFIGURATION OF THE FAMILY.** -/
def familyConfig : WeilConfig := finsetSum (family q) (charCfg q)

/-- **THE FAMILY THEOREM, AS A PROP**: Weil positivity of the family's summed configuration holds exactly when the target
of every character of the family holds. -/
def FamilyTheorem : Prop :=
  h2_sign_cfg (familyConfig q) ↔ ∀ χ ∈ family q, GRH_chi χ.primitiveCharacter

/-- **(R213)(3)(b), THE FAMILY THEOREM**, from (a) and `h2_sign_cfg_iff_target`. -/
theorem family_theorem : h2_sign_cfg (familyConfig q) ↔ ∀ χ ∈ family q, GRH_chi χ.primitiveCharacter := by
  unfold familyConfig
  rw [finsetSum_target_iff]
  exact forall₂_congr fun χ hχ => charCfg_target q χ ((mem_family q χ).mp hχ)

theorem familyTheorem_holds : FamilyTheorem q := family_theorem q

/-- **The summed arithmetic side**: one `archTerm_chi − primeSum_chi` per character of the family, at its primitive
character. -/
theorem familyConfig_arith (k : ℝ → ℂ) :
    (familyConfig q).rhs k
      = ∑ χ ∈ family q, (archTerm_chi χ.primitiveCharacter k - primeSum_chi χ.primitiveCharacter k) := by
  unfold familyConfig
  rw [finsetSum_rhs]
  exact Finset.sum_congr rfl fun χ hχ => charCfg_rhs q χ ((mem_family q χ).mp hχ) k

/-- **The conductor in each summand**: the Γ bracket of a summand reads `log (N/π)` at `N` the conductor. -/
theorem gammaBracket_conductor (χ : DirichletCharacter ℂ q) (r : ℝ) :
    gammaBracket_chi χ.primitiveCharacter r
      = Real.log (χ.conductor / Real.pi)
        + (Complex.digamma (1 / 4 + (parity χ.primitiveCharacter : ℂ) / 2 + I * r / 2)).re :=
  rfl

end family

/-! ## (c) One modulus: q = 3 -/

/-- **(R213)(3)(c), THE FAMILY THEOREM AT q = 3.** -/
theorem family_three : h2_sign_cfg (familyConfig 3) ↔ ∀ χ ∈ family 3, GRH_chi χ.primitiveCharacter :=
  family_theorem 3

/-- **The statement at q = 3 is the family theorem's**, by definition. -/
theorem family_three_statement :
    FamilyTheorem 3 = (h2_sign_cfg (familyConfig 3) ↔ ∀ χ ∈ family 3, GRH_chi χ.primitiveCharacter) :=
  rfl

/-! ## (d) The Dedekind reading's two obstructions, named and not discharged -/

/-- **The ζ instance's arithmetic side carries the pole term** (Schema/Instances.lean, `zetaWeilConfig`). -/
theorem zeta_rhs_pole (k : ℝ → ℂ) : zetaWeilConfig.rhs k = poleTerm k - primeSum k + archTerm k :=
  rfl

/-- **OBSTRUCTION (1), THE POLE, as the premise the reading would need**: the trivial character's summand in the family's
form, ζ's arithmetic side with no pole term. NOT DISCHARGED HERE. **REFUTED at b642, ruling (R252)(3)(d)**: the premise is false
-- `Family.not_trivialSummandPremise` (Schema/FamilyPremises.lean), the pole term positive at a test function where it would need
to vanish; kept as it stands. The premise restated with the pole term carried is `Dedekind.TrivialSummandPremise'`
(Schema/DedekindRestated.lean), with its witness. -/
def TrivialSummandPremise : Prop :=
  ∀ k : ℝ → ℂ,
    zetaWeilConfig.rhs k = archTerm_chi (1 : DirichletCharacter ℂ 1) k - primeSum_chi (1 : DirichletCharacter ℂ 1) k

/-- **OBSTRUCTION (2), THE EULER FACTORS AT p ∣ q, as the premise the reading would need**: every non-trivial character
mod `q`, imprimitive ones included, with its primitive inducer's arithmetic side -- the kernel's χ side reads `χ (n : ZMod
N)` and `log (N/π)` at the level `N`, so at an imprimitive character the terms at `p ∣ q` and the level differ. NOT
DISCHARGED HERE. -/
def EulerFactorPremise (q : ℕ) [NeZero q] : Prop :=
  ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ k : ℝ → ℂ,
    archTerm_chi χ k - primeSum_chi χ k = archTerm_chi χ.primitiveCharacter k - primeSum_chi χ.primitiveCharacter k

/-- **THE DEDEKIND READING'S PREMISES**, joined. NOT DISCHARGED HERE. -/
structure DedekindPremises (q : ℕ) [NeZero q] : Prop where
  trivial_summand : TrivialSummandPremise
  euler_factors : EulerFactorPremise q

end Family
end Schema
end SIDEExplicitFormula
