/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Mechanism/CoeffSign.lean
THIS PROGRAMME'S WORK (act b757, ruling (R367)(5), T1 of relay data/b752_attribution_plan.txt :43-:93) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE COEFFICIENT AT 48 OF −Z_Q′/Z_Q, IN CLOSED FORM. `cQ` (LogDeriv.lean :63) solves `c ⍟ r_Q = log · r_Q` by recursion, `2 c(n) = r_Q(n) log n −
Σ_{d | n, d < n} c(d) r_Q(n/d)` (`cQ_eq`), the place the von Mangoldt function holds for zeta. Unfolded over the divisors of 48, with `r_Q` read
at each (`rQ_four` to `rQ_forty_eight`, each by bounding a solution through `4 Q0 = (2x + y)² + 23 y²` and reading the box; `r_Q(2) = r_Q(3) = 0`
from NoEuler.lean), it gives `c(48) = −8 log 2 − 2 log 3` (`cQ_forty_eight`), so the `c(n)` are not all nonnegative (`cQ_not_nonneg`), where
the von Mangoldt function is (`ArithmeticFunction.vonMangoldt_nonneg`, read here as `vonMangoldt_nonneg_control`). The controls in the same
unfolding: `c(4) = 2 log 2` and `c(6) = 2 log 6` (`cQ_four`, `cQ_six`). Nothing here says where a zero of Z_Q lies, nor that this sign causes
a zero off the line; nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Mechanism.NoEuler
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Simproc.Divisors

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-! ### `r_Q` at the divisors of 48 -/

/-- The two vectors of norm 4. -/
theorem boxF_four : boxF 4 = {(2, 0), (-2, 0)} := by
  ext ⟨m, n⟩
  constructor
  · intro h
    have hq : Q0form m n = 4 := by simpa using (Finset.mem_filter.mp h).2
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 1 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -1 < n := by nlinarith [sq_nonneg (2 * m + n)]
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
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩

/-- The four vectors of norm 8. -/
theorem boxF_eight : boxF 8 = {(1, 1), (-2, 1), (2, -1), (-1, -1)} := by
  ext ⟨m, n⟩
  constructor
  · intro h
    have hq : Q0form m n = 8 := by simpa using (Finset.mem_filter.mp h).2
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 2 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -2 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 6 := by nlinarith [sq_nonneg n]
    have ha2 : -6 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 4 := by omega
    have hc2 : -4 < m := by omega
    clear h h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · intro h
    unfold boxF
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩

/-- The four vectors of norm 12. -/
theorem boxF_twelve : boxF 12 = {(2, 1), (-3, 1), (3, -1), (-2, -1)} := by
  ext ⟨m, n⟩
  constructor
  · intro h
    have hq : Q0form m n = 12 := by simpa using (Finset.mem_filter.mp h).2
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 2 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -2 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 7 := by nlinarith [sq_nonneg n]
    have ha2 : -7 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 4 := by omega
    have hc2 : -4 < m := by omega
    clear h h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · intro h
    unfold boxF
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩

/- The boxes for 16, 24 and 48 (65 x 33 points and up) are read through `simp only [boxF, Finset.mem_filter, ...]`, the form of
Lattice.lean's `preimage_boxF`, and not by unifying a membership against the box's filter, which reached Lean's recursion limit at
these three sizes in run 43836818700 (b757); the statements are as before. -/

set_option maxRecDepth 4096 in
/-- The two vectors of norm 16. -/
theorem boxF_sixteen : boxF 16 = {(4, 0), (-4, 0)} := by
  ext ⟨m, n⟩
  simp only [boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨-, hq0⟩
    have hq : Q0form m n = 16 := by simpa using hq0
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 2 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -2 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 9 := by nlinarith [sq_nonneg n]
    have ha2 : -9 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 5 := by omega
    have hc2 : -5 < m := by omega
    clear hq0 h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [Q0form]

set_option maxRecDepth 4096 in
/-- The four vectors of norm 24. -/
theorem boxF_twenty_four : boxF 24 = {(0, 2), (-2, 2), (2, -2), (0, -2)} := by
  ext ⟨m, n⟩
  simp only [boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨-, hq0⟩
    have hq : Q0form m n = 24 := by simpa using hq0
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 3 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -3 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 10 := by nlinarith [sq_nonneg n]
    have ha2 : -10 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 6 := by omega
    have hc2 : -6 < m := by omega
    clear hq0 h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [Q0form]

set_option maxRecDepth 4096 in
/-- The eight vectors of norm 48. -/
theorem boxF_forty_eight :
    boxF 48 = {(6, 1), (-7, 1), (7, -1), (-6, -1), (4, 2), (-6, 2), (6, -2), (-4, -2)} := by
  ext ⟨m, n⟩
  simp only [boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨-, hq0⟩
    have hq : Q0form m n = 48 := by simpa using hq0
    have h4 := four_mul_Q0form m n
    rw [hq] at h4
    have hb1 : n < 3 := by nlinarith [sq_nonneg (2 * m + n)]
    have hb2 : -3 < n := by nlinarith [sq_nonneg (2 * m + n)]
    have ha1 : 2 * m + n < 14 := by nlinarith [sq_nonneg n]
    have ha2 : -14 < 2 * m + n := by nlinarith [sq_nonneg n]
    have hc1 : m < 8 := by omega
    have hc2 : -8 < m := by omega
    clear hq0 h4 ha1 ha2
    revert hq
    interval_cases n <;> interval_cases m <;> norm_num [Q0form]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [Q0form]

theorem rQ_four : rQ 4 = 2 := by
  rw [rQ_eq_card (show (4 : ℕ) ≠ 0 by norm_num), boxF_four]
  decide

theorem rQ_eight : rQ 8 = 4 := by
  rw [rQ_eq_card (show (8 : ℕ) ≠ 0 by norm_num), boxF_eight]
  decide

theorem rQ_twelve : rQ 12 = 4 := by
  rw [rQ_eq_card (show (12 : ℕ) ≠ 0 by norm_num), boxF_twelve]
  decide

theorem rQ_sixteen : rQ 16 = 2 := by
  rw [rQ_eq_card (show (16 : ℕ) ≠ 0 by norm_num), boxF_sixteen]
  decide

theorem rQ_twenty_four : rQ 24 = 4 := by
  rw [rQ_eq_card (show (24 : ℕ) ≠ 0 by norm_num), boxF_twenty_four]
  decide

theorem rQ_forty_eight : rQ 48 = 8 := by
  rw [rQ_eq_card (show (48 : ℕ) ≠ 0 by norm_num), boxF_forty_eight]
  decide

/-! ### the logarithms at the divisors, in `log 2` and `log 3` -/

theorem logQ_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem logQ_six : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem logQ_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num

theorem logQ_twelve : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem logQ_sixteen : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num

theorem logQ_twenty_four : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
  rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem logQ_forty_eight : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
  rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num

/-! ### `c` at the divisors of 48, by `cQ_eq`; each divisor set by Mathlib's `Nat.properDivisors_ofNat`, `decide` beside it -/

theorem cQ_one : cQ 1 = 0 := cQ_le_one le_rfl

theorem cQ_two : cQ 2 = 0 := by
  have h := cQ_eq (n := 2) (by norm_num)
  rw [show Nat.properDivisors 2 = {1} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [cQ_one, rQ_two] at h
  linarith

theorem cQ_three : cQ 3 = 0 := by
  have h := cQ_eq (n := 3) (by norm_num)
  rw [show Nat.properDivisors 3 = {1} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [cQ_one, rQ_three] at h
  linarith

/-- **THE FIRST CONTROL**: `c(4) = 2 log 2`. -/
theorem cQ_four : cQ 4 = 2 * Real.log 2 := by
  have h := cQ_eq (n := 4) (by norm_num)
  rw [show Nat.properDivisors 4 = {1, 2} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, rQ_two, rQ_four] at h
  linarith [logQ_four]

/-- **THE SECOND CONTROL**: `c(6) = 2 log 6`. -/
theorem cQ_six : cQ 6 = 2 * Real.log 6 := by
  have h := cQ_eq (n := 6) (by norm_num)
  rw [show Nat.properDivisors 6 = {1, 2, 3} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_three, rQ_two, rQ_three, rQ_six] at h
  linarith

theorem cQ_eight : cQ 8 = 6 * Real.log 2 := by
  have h := cQ_eq (n := 8) (by norm_num)
  rw [show Nat.properDivisors 8 = {1, 2, 4} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_four, rQ_two, rQ_four, rQ_eight] at h
  linarith [logQ_eight]

theorem cQ_twelve : cQ 12 = 2 * Real.log 12 := by
  have h := cQ_eq (n := 12) (by norm_num)
  rw [show Nat.properDivisors 12 = {1, 2, 3, 4, 6} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_three, cQ_four, cQ_six, rQ_two, rQ_three, rQ_four, rQ_six,
    rQ_twelve] at h
  linarith

theorem cQ_sixteen : cQ 16 = 2 * Real.log 2 := by
  have h := cQ_eq (n := 16) (by norm_num)
  rw [show Nat.properDivisors 16 = {1, 2, 4, 8} by first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_four, cQ_eight, rQ_two, rQ_four, rQ_eight, rQ_sixteen] at h
  linarith [logQ_sixteen]

theorem cQ_twenty_four : cQ 24 = 0 := by
  have h := cQ_eq (n := 24) (by norm_num)
  rw [show Nat.properDivisors 24 = {1, 2, 3, 4, 6, 8, 12} by
    first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_three, cQ_four, cQ_six, cQ_eight, cQ_twelve, rQ_two, rQ_three,
    rQ_four, rQ_six, rQ_eight, rQ_twelve, rQ_twenty_four] at h
  linarith [logQ_six, logQ_twenty_four]

/-- **T1's WITNESS: `c(48) = −8 log 2 − 2 log 3`**, the coefficient law's value at discriminant −23, 48 = 2⁴ · 3. -/
theorem cQ_forty_eight : cQ 48 = -(8 * Real.log 2) - 2 * Real.log 3 := by
  have h := cQ_eq (n := 48) (by norm_num)
  rw [show Nat.properDivisors 48 = {1, 2, 3, 4, 6, 8, 12, 16, 24} by
    first | (simp only [Nat.properDivisors_ofNat]; done) | decide] at h
  norm_num [Finset.sum_insert, cQ_one, cQ_two, cQ_three, cQ_four, cQ_six, cQ_eight, cQ_twelve, cQ_sixteen,
    cQ_twenty_four, rQ_two, rQ_three, rQ_four, rQ_six, rQ_eight, rQ_twelve, rQ_sixteen, rQ_twenty_four,
    rQ_forty_eight] at h
  linarith [logQ_six, logQ_twelve, logQ_forty_eight]

/-- **T1: THE COEFFICIENTS OF −Z_Q′/Z_Q ARE NOT ALL NONNEGATIVE.** -/
theorem cQ_not_nonneg : ¬ (∀ n : ℕ, 0 ≤ cQ n) := by
  intro h
  have h48 := h 48
  rw [cQ_forty_eight] at h48
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

/-- **THE CONTROL BESIDE IT**: the von Mangoldt function, zeta's place for `c`, is nonnegative (Mathlib's
`ArithmeticFunction.vonMangoldt_nonneg`). -/
theorem vonMangoldt_nonneg_control (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

end ZQ
end Schema
end SIDEExplicitFormula
