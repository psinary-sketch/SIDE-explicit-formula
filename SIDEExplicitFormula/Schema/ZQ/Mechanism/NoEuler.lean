/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Mechanism/NoEuler.lean
THIS PROGRAMME'S WORK (act b757, ruling (R367)(5), T0 of relay data/b752_attribution_plan.txt :43-:93) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE HALVED COEFFICIENTS OF Z_Q ARE NOT MULTIPLICATIVE. `r_Q(n)` counts the pairs `(x, y)` with `x² + xy + 6y² = n` (EpsteinZQ.lean :59), and
`r_Q(1) = 2` (LogDeriv.lean :56), so `n ↦ r_Q(n)/2` takes 1 at 1 (`rQ_half_one`). Its values at 2 and at 3 are 0 and its value at 6 is 2
(`rQ_two`, `rQ_three`, `rQ_six`, each by bounding a solution through `4 Q0 = (2x + y)² + 23 y²` and reading the box), so at the coprime
pair 2, 3 the product of its values is 0 and its value at the product is 2 (`rQ_six_ne`): the function is not multiplicative
(`zq_coeff_not_multiplicative`). Mathlib's Euler product for an arithmetic function (`ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd`)
takes multiplicativity as its hypothesis; zeta's coefficients meet it (`ArithmeticFunction.isMultiplicative_zeta`, read here as
`zeta_isMultiplicative_control`), and these do not. Nothing here says where a zero of Z_Q lies, nor that Z_Q has no product formula of
another kind; nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.LogDeriv
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- No vector has norm 2. -/
theorem boxF_two : boxF 2 = ∅ := by
  unfold boxF
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨m, n⟩ - hq
  have hq' : Q0form m n = 2 := by simpa using hq
  have h4 := four_mul_Q0form m n
  rw [hq'] at h4
  have hb1 : n < 1 := by nlinarith [sq_nonneg (2 * m + n)]
  have hb2 : -1 < n := by nlinarith [sq_nonneg (2 * m + n)]
  have hn : n = 0 := by omega
  subst hn
  have ha1 : m < 2 := by nlinarith
  have ha2 : -2 < m := by nlinarith
  interval_cases m <;> norm_num [Q0form] at hq'

/-- No vector has norm 3. -/
theorem boxF_three : boxF 3 = ∅ := by
  unfold boxF
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨m, n⟩ - hq
  have hq' : Q0form m n = 3 := by simpa using hq
  have h4 := four_mul_Q0form m n
  rw [hq'] at h4
  have hb1 : n < 1 := by nlinarith [sq_nonneg (2 * m + n)]
  have hb2 : -1 < n := by nlinarith [sq_nonneg (2 * m + n)]
  have hn : n = 0 := by omega
  subst hn
  have ha1 : m < 2 := by nlinarith
  have ha2 : -2 < m := by nlinarith
  interval_cases m <;> norm_num [Q0form] at hq'

/-- The four vectors of norm 6: `(0, 1)`, `(-1, 1)`, `(1, -1)`, `(0, -1)`. -/
theorem boxF_six : boxF 6 = {(0, 1), (-1, 1), (1, -1), (0, -1)} := by
  ext ⟨m, n⟩
  constructor
  · intro h
    have hq : Q0form m n = 6 := by simpa using (Finset.mem_filter.mp h).2
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 2 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -2 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 5 := by nlinarith [sq_nonneg n]
    have ha2 : -5 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 3 := by omega
    have hc2 : -3 < m := by omega
    clear h h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · intro h
    unfold boxF
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩

/-- `r_Q(2) = 0`. -/
theorem rQ_two : rQ 2 = 0 := by
  rw [rQ_eq_card (show (2 : ℕ) ≠ 0 by norm_num), boxF_two, Finset.card_empty]

/-- `r_Q(3) = 0`. -/
theorem rQ_three : rQ 3 = 0 := by
  rw [rQ_eq_card (show (3 : ℕ) ≠ 0 by norm_num), boxF_three, Finset.card_empty]

/-- `r_Q(6) = 4`. -/
theorem rQ_six : rQ 6 = 4 := by
  rw [rQ_eq_card (show (6 : ℕ) ≠ 0 by norm_num), boxF_six]
  decide

/-- **THE WITNESS**: at the coprime pair 2, 3 the halved coefficients' product is 0 and their value at 6 is 2. -/
theorem rQ_six_ne : (rQ 6 : ℝ) / 2 ≠ ((rQ 2 : ℝ) / 2) * ((rQ 3 : ℝ) / 2) := by
  rw [rQ_six, rQ_two, rQ_three]
  norm_num

/-- **T0: THE HALVED COEFFICIENTS OF Z_Q ARE NOT MULTIPLICATIVE.** -/
theorem zq_coeff_not_multiplicative :
    ¬ ArithmeticFunction.IsMultiplicative (⟨fun n => (rQ n : ℝ) / 2, by simp [rQ_zero]⟩ : ArithmeticFunction ℝ) := by
  intro h
  have h6 : (rQ (2 * 3) : ℝ) / 2 = (rQ 2 : ℝ) / 2 * ((rQ 3 : ℝ) / 2) :=
    h.map_mul_of_coprime (show Nat.gcd 2 3 = 1 by norm_num)
  exact rQ_six_ne h6

/-- **THE POSITIVE CONTROL**: the halved coefficient at 1 is 1, so the failure sits at 6 and not at the unit. -/
theorem rQ_half_one : (rQ 1 : ℝ) / 2 = 1 := by
  rw [rQ_one]
  norm_num

/-- **THE NEGATIVE CONTROL**: zeta's coefficients meet the hypothesis T0 denies (Mathlib's `ArithmeticFunction.isMultiplicative_zeta`). -/
theorem zeta_isMultiplicative_control : ArithmeticFunction.IsMultiplicative ArithmeticFunction.zeta :=
  ArithmeticFunction.isMultiplicative_zeta

end ZQ
end Schema
end SIDEExplicitFormula
