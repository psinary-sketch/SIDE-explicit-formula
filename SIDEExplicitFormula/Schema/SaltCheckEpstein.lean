/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/SaltCheckEpstein.lean
THIS PROGRAMME'S WORK (act b590, ruling (R200)(4)(b), H31b) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE EPSTEIN INSTANCE, COMPILED. A theorem whose hypotheses cannot hold together is vacuously true and
says nothing. `epstein_not_h2_sign_cfg` takes `EpsteinPremises Z rhs` and `rhoE ∈ Z.carrier`; two checks:

* **`epstein_hypotheses_satisfiable`** -- the hypotheses hold together: a configuration whose carrier is `rhoE` and its
  reflection, multiplicity one, the arithmetic side its own zero side, satisfies every field, the count with `A₀ = 2`.
  No field contradicts another or the membership. (It is a model of the premises' FORM, not of `Z_Q`: the premise
  bundle's consistency with the actual Epstein zeta function is not proved in the kernel.)
* **`membership_load_bearing`** -- the membership hypothesis is USED: the empty configuration satisfies the premises and IS
  Weil-positive on classK, so the conclusion does not follow from the premises alone.

0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Schema.Epstein
import Mathlib.Data.Set.Card.Arithmetic

open Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace SaltCheckEpstein

open B321

/-- The toy carrier: `rhoE` and its reflection `1 - conj rhoE`. -/
def toyCarrier : Set ℂ := {rhoE, Zeta23.reflect rhoE}

theorem toy_strip : ∀ ρ ∈ toyCarrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  intro ρ hρ
  rcases hρ with rfl | rfl
  · show 0 ≤ (0.7979971571786801 : ℝ) ∧ (0.7979971571786801 : ℝ) ≤ 1
    constructor <;> norm_num
  · show 0 ≤ (1 - (starRingEnd ℂ) rhoE).re ∧ (1 - (starRingEnd ℂ) rhoE).re ≤ 1
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    show 0 ≤ 1 - (0.7979971571786801 : ℝ) ∧ 1 - (0.7979971571786801 : ℝ) ≤ 1
    constructor <;> norm_num

theorem toy_reflect_mem : ∀ ρ ∈ toyCarrier, Zeta23.reflect ρ ∈ toyCarrier := by
  intro ρ hρ
  rcases hρ with rfl | rfl
  · exact Or.inr rfl
  · left
    unfold Zeta23.reflect
    simp

theorem toy_finite : toyCarrier.Finite := (Set.finite_singleton _).insert _

/-- **The toy configuration**: `rhoE` and its reflection, multiplicity one. -/
def toyZ : Zeta23.ZeroConfig where
  carrier := toyCarrier
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := toy_strip
  reflect_mem := toy_reflect_mem
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => toy_finite.subset Set.inter_subset_left

theorem log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem toy_count : HCount toyZ 2 := by
  refine ⟨by norm_num, fun t => ?_⟩
  have hN : toyZ.N t (t + 1) ≤ 2 := by
    show (∑ᶠ ρ ∈ toyZ.window t (t + 1), (1 : ℕ)) ≤ 2
    rw [finsum_one]
    calc (toyZ.window t (t + 1)).ncard ≤ toyCarrier.ncard :=
          Set.ncard_le_ncard Set.inter_subset_left toy_finite
      _ ≤ 2 := by
          unfold toyCarrier
          calc ({rhoE, Zeta23.reflect rhoE} : Set ℂ).ncard ≤ ({Zeta23.reflect rhoE} : Set ℂ).ncard + 1 := Set.ncard_insert_le _ _
            _ = 2 := by rw [Set.ncard_singleton]
  have hlog : 1 ≤ Real.log (|t| + 3) := by
    have h3 : Real.log 3 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith [log_three_gt_one]
  have hN' : (toyZ.N t (t + 1) : ℝ) ≤ 2 := by exact_mod_cast hN
  nlinarith

/-- The toy's arithmetic side: its own zero side. -/
def toyRhs : (ℝ → ℂ) → ℂ := fun k => ∑' ρ : toyZ.carrier, (toyZ.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

theorem toy_premises : EpsteinPremises toyZ toyRhs :=
  ⟨fun _ _ _ _ => rfl, ⟨2, toy_count⟩⟩

/-- **H31b, NON-VACUITY**: the hypotheses of `epstein_not_h2_sign_cfg` hold together. -/
theorem epstein_hypotheses_satisfiable :
    ∃ (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ), EpsteinPremises Z rhs ∧ rhoE ∈ Z.carrier :=
  ⟨toyZ, toyRhs, toy_premises, Or.inl rfl⟩

/-- The empty configuration. -/
def emptyZ : Zeta23.ZeroConfig where
  carrier := ∅
  mult := fun _ => 1
  one_le_mult := fun _ h => absurd h (Set.notMem_empty _)
  strip := fun _ h => absurd h (Set.notMem_empty _)
  reflect_mem := fun _ h => absurd h (Set.notMem_empty _)
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => Set.finite_empty.subset Set.inter_subset_left

theorem empty_count : HCount emptyZ 1 := by
  refine ⟨le_rfl, fun t => ?_⟩
  have hN : emptyZ.N t (t + 1) = 0 := by
    show (∑ᶠ ρ ∈ emptyZ.window t (t + 1), (1 : ℕ)) = 0
    rw [finsum_one]
    show (emptyZ.carrier ∩ {ρ : ℂ | t < ρ.im ∧ ρ.im ≤ t + 1}).ncard = 0
    rw [Set.ncard_eq_zero (emptyZ.finite_window t (t + 1))]
    exact Set.empty_inter _
  rw [hN, Nat.cast_zero, one_mul]
  exact Real.log_nonneg (by linarith [abs_nonneg t])

def emptyRhs : (ℝ → ℂ) → ℂ := fun k => ∑' ρ : emptyZ.carrier, (emptyZ.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

theorem empty_premises : EpsteinPremises emptyZ emptyRhs :=
  ⟨fun _ _ _ _ => rfl, ⟨1, empty_count⟩⟩

/-- **H31b, THE MEMBERSHIP IS LOAD-BEARING**: without `rhoE ∈ Z.carrier` the conclusion fails -- the empty configuration
satisfies the premises and is Weil-positive on classK. -/
theorem membership_load_bearing :
    ∃ (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : EpsteinPremises Z rhs), h2_sign_cfg (epsteinConfig Z rhs hP) :=
  ⟨emptyZ, emptyRhs, empty_premises,
    online_imp_h2_sign_cfg _ (fun ρ (h : ρ ∈ (∅ : Set ℂ)) => absurd h (Set.notMem_empty ρ))⟩

end SaltCheckEpstein
end Schema
end SIDEExplicitFormula
