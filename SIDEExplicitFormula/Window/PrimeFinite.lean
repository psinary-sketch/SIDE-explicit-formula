import SIDEExplicitFormula.Schema.EpsteinZQ
import SIDEExplicitFormula.Schema.ZQ.LogDeriv

/-!
# The prime-power side as a finite sum

For a continuous `k` that vanishes where `|u| > log N` (`N ≥ 2`) and weights `c` with `c 1 = 0`, the prime-power side
`Schema.primeTermQ c k` is the finite sum over `n` from `2` to `N - 1`. The term at `n = N` vanishes because `k` is continuous
and zero beyond `log N`, so zero at `log N` itself; the terms at `0` and `1` vanish by the definition and by `c 1 = 0`.
Read at the control's weights `Schema.ZQ.cQ`, whose value at `1` is `0` (`Schema.ZQ.cQ_le_one`).
-/

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- **The prime-power side as a finite sum.** For a continuous `k` vanishing where `|u| > log N`, `N ≥ 2`, and weights `c`
with `c 1 = 0`, the prime-power side is the sum over `n` from `2` to `N - 1`. -/
theorem primeTermQ_eq_finite_sum (c : ℕ → ℝ) (k : ℝ → ℂ) (N : ℕ) (hN : 2 ≤ N) (hc1 : c 1 = 0)
    (hk : Continuous k) (hsupp : ∀ u : ℝ, Real.log N < |u| → k u = 0) :
    Schema.primeTermQ c k =
      ∑ n ∈ Finset.Ico 2 N, ((c n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hzero : ∀ u : ℝ, Real.log N ≤ u → k u = 0 := by
    have hcl : IsClosed {u : ℝ | k u = 0} := isClosed_eq hk continuous_const
    have hsub : Set.Ioi (Real.log N) ⊆ {u : ℝ | k u = 0} := by
      intro u hu
      have hu' : Real.log N < u := hu
      have hpos : 0 < u := lt_of_le_of_lt hlogN hu'
      exact hsupp u (by rw [abs_of_pos hpos]; exact hu')
    have h := closure_minimal hsub hcl
    rw [closure_Ioi] at h
    intro u hu
    exact h hu
  unfold Schema.primeTermQ
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_Ico] at hn
  push_neg at hn
  by_cases h2 : 2 ≤ n
  · have hnN : N ≤ n := hn h2
    have hle : Real.log N ≤ Real.log n := Real.log_le_log hN0 (by exact_mod_cast hnN)
    rw [hzero _ hle]
    simp
  · have hn2 : n < 2 := by omega
    interval_cases n
    · simp
    · simp [hc1]

/-- **The prime-power side at the control's weights as a finite sum:** `primeTermQ_eq_finite_sum` read at `Schema.ZQ.cQ`. -/
theorem primeTermQ_cQ_eq_finite_sum (k : ℝ → ℂ) (N : ℕ) (hN : 2 ≤ N) (hk : Continuous k)
    (hsupp : ∀ u : ℝ, Real.log N < |u| → k u = 0) :
    Schema.primeTermQ Schema.ZQ.cQ k =
      ∑ n ∈ Finset.Ico 2 N, ((Schema.ZQ.cQ n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n)) :=
  primeTermQ_eq_finite_sum _ k N hN (Schema.ZQ.cQ_le_one le_rfl) hk hsupp

end Window
end SIDEExplicitFormula
