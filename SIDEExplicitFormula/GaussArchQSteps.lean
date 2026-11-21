/-
b765 under (R375)(5)(b): GAUSS'S INTEGRAL FOR THE CONTROL'S ARCHIMEDEAN TERM, ITS PROOF IN STEPS, as far as it goes.

The statement is `GaussArchQ` (GaussArchQ.lean). Each step below is a theorem with no sorry; the steps not yet written are
named in the act's record and not here. The route: Fourier inversion at the origin and against the cosine (steps 1 and 2,
from `Zeta23.EF.paper_inversion` and `Zeta23.EF.k_add_k_neg`); each term `1/(n+1) − 1/(z+n+1)` of the digamma series
(`Zeta23.digamma_series`) written as an integral over `t > 0` (steps 3 and 4); then the series summed under the integral, the
bracket written by Gauss's integral, and the exchange of the two integrals.
-/
import SIDEExplicitFormula.GaussArchQ
import Zeta23.ExplicitFormula.Bridge

open MeasureTheory Set

noncomputable section

namespace SIDEExplicitFormula
namespace B321
namespace GaussArchQSteps

/-- **Step 1. Fourier inversion at the origin:** `(1/2π) ∫ k̂(r) dr = k(0)` for `k` in classK. -/
theorem inversion_zero {k : ℝ → ℂ} (hk : classK k) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r = k 0 := by
  unfold classK at hk
  obtain ⟨-, hk2, hkc, -⟩ := hk
  rw [Zeta23.EF.paper_inversion hk2.continuous (hk2.continuous.integrable_of_hasCompactSupport hkc)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hkc) 0]
  congr 1 <;> simp

/-- **Step 2. Fourier inversion against the cosine:** `(1/2π) ∫ k̂(r) cos(r t) dr = k(t)` for `k` in classK, `k` even. -/
theorem inversion_cos {k : ℝ → ℂ} (hk : classK k) (t : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Real.cos (r * t) : ℂ) = k t := by
  unfold classK at hk
  obtain ⟨heven, hk2, hkc, -⟩ := hk
  have h := Zeta23.EF.k_add_k_neg hk2.continuous (hk2.continuous.integrable_of_hasCompactSupport hkc)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hkc) t
  rw [heven t] at h
  have e : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 / 2 : ℂ) * (1 / (Real.pi : ℂ)) := by
    push_cast
    ring
  rw [e, mul_assoc, ← h]
  ring

/-- **Step 3.** `∫_{t>0} e^{−z t} dt = 1/z` for `Re z > 0`. -/
theorem integral_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) = 1 / z := by
  have h := integral_exp_mul_complex_Ioi (a := -z) (by rw [Complex.neg_re]; linarith) 0
  have e : (fun t : ℝ => Complex.exp (-(z * t))) = fun t : ℝ => Complex.exp (-z * t) := by
    funext t
    rw [neg_mul]
  rw [e, h]
  simp

/-- `t ↦ e^{−z t}` is integrable on `t > 0` for `Re z > 0`. -/
theorem integrableOn_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * t))) (Ioi (0 : ℝ)) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -z) (by rw [Complex.neg_re]; linarith) 0
  have e : (fun t : ℝ => Complex.exp (-(z * t))) = fun t : ℝ => Complex.exp (-z * t) := by
    funext t
    rw [neg_mul]
  rw [e]
  exact h

/-- **Step 4. Each term of the digamma series as an integral:** for `Re z > 0` and every `n`,
`∫_{t>0} (e^{−(n+1) t} − e^{−(z+n+1) t}) dt = 1/(n+1) − 1/(z+n+1)`. -/
theorem digamma_term_integral {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t)))
      = 1 / ((n : ℂ) + 1) - 1 / (z + n + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 < ((n : ℂ) + 1).re := by
    have e : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
    rw [e]
    linarith
  have h2 : 0 < (z + n + 1).re := by
    have e : (z + n + 1).re = z.re + n + 1 := by simp
    rw [e]
    linarith
  rw [integral_sub (integrableOn_cexp_neg_mul h1) (integrableOn_cexp_neg_mul h2), integral_cexp_neg_mul h1,
    integral_cexp_neg_mul h2]

end GaussArchQSteps
end B321
end SIDEExplicitFormula
