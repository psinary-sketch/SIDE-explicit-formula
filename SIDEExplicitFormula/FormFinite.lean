/-
SIDE-explicit-formula -- SIDEExplicitFormula/FormFinite.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(6), statements (S1) and (S2); W-ORD-SIGN-SECTORS) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE PRIME-POWER SIDE OF A WINDOW IS A FINITE SUM. For any real weights `c` and any `k` that vanishes outside `[-L, L]`, the
prime-power side `primeTermQ c k = Σ_n c(n) n^{-1/2} · 2 k(log n)` equals its sum over `n ≤ ⌊e^L⌋` (S1, `primeTermQ_window`): a term
with `n > e^L` has `log n > L`, where `k` vanishes. Stated once for weights in general: at the control's coefficients it reads at
`primeTermQ cQ`, and at the von Mangoldt function it is zeta's `primeSum` (`primeSum_eq_primeTermQ`, the two definitions agreeing term
by term; `primeSum_window`). Below `log 2` the prime sum of zeta's formula vanishes (S2, `primeSum_eq_zero_of_lt_log_two`):
`Λ(0) = Λ(1) = 0`, and every `n ≥ 2` has `log n ≥ log 2`, where `k` vanishes. No premise is bound; nothing here concerns any zero.
-/
import SIDEExplicitFormula.Schema.EpsteinZQ

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **(S1) The prime-power side of a window is a finite sum.** For any real weights `c` and any `k` that vanishes outside
`[-L, L]`, the prime-power side equals its sum over `n ≤ ⌊e^L⌋`. -/
theorem primeTermQ_window (c : ℕ → ℝ) (k : ℝ → ℂ) (L : ℝ) (hk : ∀ u : ℝ, L < |u| → k u = 0) :
    Schema.primeTermQ c k =
      ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1), ((c n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n)) := by
  unfold Schema.primeTermQ
  refine tsum_eq_sum (fun n hn => ?_)
  have hn' : ⌊Real.exp L⌋₊ + 1 ≤ n := by
    simpa [Finset.mem_range, not_lt] using hn
  have hlt : Real.exp L < n := by
    have h1 := Nat.lt_floor_add_one (Real.exp L)
    have h2 : ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos L) hlt
  have hlog : L < Real.log n := (Real.lt_log_iff_exp_lt hpos).mpr hlt
  rw [hk (Real.log n) (lt_of_lt_of_le hlog (le_abs_self _)), mul_zero, mul_zero]

/-- Zeta's `primeSum` is the prime-power side with the von Mangoldt weights, term by term. -/
theorem primeSum_eq_primeTermQ (k : ℝ → ℂ) :
    primeSum k = Schema.primeTermQ (fun n => ArithmeticFunction.vonMangoldt n) k := rfl

/-- **(S1) at the von Mangoldt weights:** on a window `[-L, L]`, `primeSum` is its sum over `n ≤ ⌊e^L⌋`. -/
theorem primeSum_window (k : ℝ → ℂ) (L : ℝ) (hk : ∀ u : ℝ, L < |u| → k u = 0) :
    primeSum k = ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n)) := by
  rw [primeSum_eq_primeTermQ]
  exact primeTermQ_window _ k L hk

/-- **(S2) Below log 2 the prime sum of zeta's formula vanishes:** for `k` vanishing outside `[-L, L]` with `L < log 2`,
`primeSum k = 0`. -/
theorem primeSum_eq_zero_of_lt_log_two (k : ℝ → ℂ) (L : ℝ) (hL : L < Real.log 2)
    (hk : ∀ u : ℝ, L < |u| → k u = 0) : primeSum k = 0 := by
  unfold primeSum
  have hz : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n)) = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
      rw [hk (Real.log n) (lt_of_lt_of_le hL (hlog.trans (le_abs_self _))), mul_zero, mul_zero]
  simp only [hz, tsum_zero]

end B321
end SIDEExplicitFormula
