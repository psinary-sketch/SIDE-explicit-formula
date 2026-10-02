/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckSimplicity.lean
THIS PROGRAMME'S WORK (act b596, ruling (R206)(4)(b), H29b) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE TITLE'S CLAUSE, COMPILED. A Prop that the schema's own fields decided would say nothing beyond
them. `allSimple` is read over configurations that satisfy every field of `Schema.WeilConfig` (the explicit formula with
an arithmetic side, the local count) with the target held (every point on the line) and Weil-positive on classK:

* **`allSimple_satisfiable`** -- such a configuration with a point exists in which every point is simple (one point on
  the line, multiplicity one, its arithmetic side its own zero side, the count with `A₀ = 1`).
* **`allSimple_not_forced`** -- such a configuration exists in which a point is not simple (the same point, multiplicity
  two, the count with `A₀ = 2`): the fields, the target and Weil positivity together do not imply the clause.

These are models of the schema's FORM, not of ζ: nothing here is a statement about the zeros of `riemannZeta`.
0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Simplicity
import SIDEExplicitFormula.Schema.SaltCheckEpstein

open Complex
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Simplicity
namespace SaltCheck

open Schema B321

/-- The toy point: `1/2 + 14 i`, on the line. -/
def pt : ℂ := ⟨1 / 2, 14⟩

theorem pt_reflect : Zeta23.reflect pt = pt := by
  apply Complex.ext
  · show (1 - (starRingEnd ℂ) pt).re = pt.re
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    show (1 : ℝ) - 1 / 2 = 1 / 2
    norm_num
  · show (1 - (starRingEnd ℂ) pt).im = pt.im
    rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

/-- **The toy configuration**: the one point `pt`, multiplicity `m`. -/
def toyZ (m : ℕ) (hm : 1 ≤ m) : Zeta23.ZeroConfig where
  carrier := {pt}
  mult := fun _ => m
  one_le_mult := fun _ _ => hm
  strip := fun ρ hρ => by
    have h : ρ = pt := hρ
    subst h
    show (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1
    constructor <;> norm_num
  reflect_mem := fun ρ hρ => by
    have h : ρ = pt := hρ
    subst h
    show Zeta23.reflect pt = pt
    exact pt_reflect
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Set.finite_singleton pt).subset Set.inter_subset_left

theorem toy_N_le (m : ℕ) (hm : 1 ≤ m) (t : ℝ) : (toyZ m hm).N t (t + 1) ≤ m := by
  have hsub : (toyZ m hm).window t (t + 1) ⊆ {pt} := Set.inter_subset_left
  unfold Zeta23.ZeroConfig.N
  rcases Set.subset_singleton_iff_eq.mp hsub with h | h
  · rw [h, finsum_mem_empty]
    exact Nat.zero_le _
  · rw [h, finsum_mem_singleton]
    exact le_rfl

theorem toy_count (m : ℕ) (hm : 1 ≤ m) : HCount (toyZ m hm) m := by
  refine ⟨by exact_mod_cast hm, fun t => ?_⟩
  have hlog : 1 ≤ Real.log (|t| + 3) := by
    have h3 : Real.log 3 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith [Schema.SaltCheckEpstein.log_three_gt_one]
  have hN : ((toyZ m hm).N t (t + 1) : ℝ) ≤ m := by exact_mod_cast toy_N_le m hm t
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc ((toyZ m hm).N t (t + 1) : ℝ) ≤ m := hN
    _ = (m : ℝ) * 1 := (mul_one _).symm
    _ ≤ (m : ℝ) * Real.log (|t| + 3) := mul_le_mul_of_nonneg_left hlog hm0

/-- **The toy configuration of the schema**: its arithmetic side its own zero side, the target the strip form. -/
def toyCfg (m : ℕ) (hm : 1 ≤ m) : WeilConfig where
  toZeroConfig := toyZ m hm
  rhs := fun k => ∑' ρ : (toyZ m hm).carrier, ((toyZ m hm).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)
  ef := fun _ _ _ _ => rfl
  count := ⟨m, toy_count m hm⟩
  target := ∀ ρ ∈ (toyZ m hm).carrier, ρ.re = 1 / 2
  target_iff := Iff.rfl

theorem toy_online (m : ℕ) (hm : 1 ≤ m) : online (toyCfg m hm) := by
  intro ρ hρ
  have h : ρ = pt := hρ
  subst h
  rfl

/-- **H29b, NON-VACUITY**: a configuration of the schema, its target held and Weil-positive on classK, with a point,
every point simple. -/
theorem allSimple_satisfiable :
    ∃ C : WeilConfig, C.target ∧ h2_sign_cfg C ∧ C.carrier.Nonempty ∧ allSimple C :=
  ⟨toyCfg 1 le_rfl, toy_online 1 le_rfl, online_imp_h2_sign_cfg _ (toy_online 1 le_rfl), ⟨pt, Set.mem_singleton pt⟩,
    fun _ _ => rfl⟩

/-- **H29b, NOT FORCED**: a configuration of the schema, its target held and Weil-positive on classK, with a point that is
not simple. -/
theorem allSimple_not_forced :
    ∃ C : WeilConfig, C.target ∧ h2_sign_cfg C ∧ ¬ allSimple C :=
  ⟨toyCfg 2 (by norm_num), toy_online 2 (by norm_num), online_imp_h2_sign_cfg _ (toy_online 2 (by norm_num)),
    fun h => by
      have h2 : (2 : ℕ) = 1 := h pt (Set.mem_singleton pt)
      omega⟩

end SaltCheck
end Simplicity
end SIDEExplicitFormula
