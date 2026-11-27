/-
SIDE-explicit-formula -- SIDEExplicitFormula/Window/CQLeast.lean
THIS PROGRAMME'S WORK (act b770, ruling (R380)(4)(e); relay data/b770_plan.txt (4)(e)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LEAST NEGATIVE COEFFICIENT AT THE CONTROL. Among the coefficients `c(n)` of minus the logarithmic derivative of the
control (`Schema.ZQ.cQ`), `c(48)` is negative and `c(n)` is at least `0` for each `n` below 48 (`cQ_least_negative`). Its
leading half is `Schema.ZQ.cQ_forty_eight` (CoeffSign.lean :281), `c(48) = -8 log 2 - 2 log 3`. Its second half reads each
`c(n)`, `n < 48`, as the combination `∑_p z(n, p) log p` over the primes below 1024 (`cQ_eq_comb`, CQValues.lean :240): the
integers `z(n, p)` (`cqZ`, CQValues.lean :165) are at least `0` for each `n < 48` and each prime of the list
(`cq_nonneg_ok`, one kernel evaluation of 48 places, each over the 172 primes of `primeList`), and `log p` is at least `0`.
Nothing here says where a zero of the control lies.
-/
import SIDEExplicitFormula.Window.CQValues
import SIDEExplicitFormula.Schema.ZQ.Mechanism.CoeffSign

namespace SIDEExplicitFormula
namespace Window

/-- At `n`, the integer coefficient of `log p` in the combination the data holds is at least `0`, for each prime of the
list. -/
def cqNonneg (n : ℕ) : Bool :=
  primeList.all (fun p => decide (0 ≤ cqZ n p))

/-- **The integer coefficients below 48 are at least `0`**, read by the kernel at each `n < 48`. -/
theorem cq_nonneg_ok : allDC cqNonneg 0 48 6 = true := by decide +kernel

/-- **`c(48)` is negative and `c(n)` is at least `0` for each `n` below 48**, `c` the coefficients of minus the
logarithmic derivative of the control. -/
theorem cQ_least_negative : Schema.ZQ.cQ 48 < 0 ∧ ∀ n : ℕ, n < 48 → 0 ≤ Schema.ZQ.cQ n := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [Schema.ZQ.cQ_forty_eight]
    have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  · rw [cQ_eq_comb n (by omega)]
    have hc := allDC_at (by norm_num) cq_nonneg_ok (Nat.zero_le n) (by omega : n < 0 + 48)
    simp only [cqNonneg, List.all_eq_true, decide_eq_true_eq] at hc
    refine Finset.sum_nonneg fun p hp => ?_
    have hp' := mem_cqPF.mp hp
    have h2 := primeList_two_le p hp'
    have hz : (0 : ℝ) ≤ (cqZ n p : ℝ) := by exact_mod_cast hc p hp'
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    exact mul_nonneg hz hl

end Window
end SIDEExplicitFormula
