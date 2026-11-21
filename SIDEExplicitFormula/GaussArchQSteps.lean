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
import Zeta23.GammaFacts.Series

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

/-- `‖e^{−t}‖ < 1` for `t > 0`. -/
theorem norm_cexp_neg_lt_one {t : ℝ} (ht : 0 < t) : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **Step 5a. The series' terms summed for `t > 0`:**
`Σₙ (e^{−(n+1)t} − e^{−(z+n+1)t}) = (e^{−t} − e^{−(z+1)t}) / (1 − e^{−t})`. -/
theorem hasSum_term_geometric (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t)))
      ((Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ)))) := by
  have he : ∀ n : ℕ, Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))
      = (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) * Complex.exp (-(t : ℂ)) ^ n := by
    intro n
    have h1 : Complex.exp (-(((n : ℂ) + 1) * t)) = Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ)) ^ n := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    have h2 : Complex.exp (-((z + n + 1) * t)) = Complex.exp (-((z + 1) * t)) * Complex.exp (-(t : ℂ)) ^ n := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    rw [h1, h2]
    ring
  have hf : (fun n : ℕ => Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t)))
      = fun n : ℕ => (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) * Complex.exp (-(t : ℂ)) ^ n :=
    funext he
  rw [hf, div_eq_mul_inv]
  exact (hasSum_geometric_of_norm_lt_one (norm_cexp_neg_lt_one ht)).mul_left _

/-- **Step 5b.** For `Re z ≥ 0` and `t ≥ 0`: `‖e^{−z t} − 1‖ ≤ ‖z‖ t`, by the mean value inequality. -/
theorem norm_cexp_neg_mul_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(z * t)) - 1‖ ≤ ‖z‖ * t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun s : ℝ => Complex.exp (-(z * s)))
      (Complex.exp (-(z * s)) * -(z * 1)) (Icc 0 t) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).ofReal_comp
    exact ((h1.const_mul z).neg.cexp).hasDerivWithinAt
  have hb : ∀ s ∈ Ico (0 : ℝ) t, ‖Complex.exp (-(z * s)) * -(z * 1)‖ ≤ ‖z‖ := by
    intro s hs
    have hre : (-(z * (s : ℂ))).re = -(z.re * s) := by simp
    have h0 : Real.exp (-(z.re * s)) ≤ 1 := by
      rw [← Real.exp_zero]
      have hzs := mul_nonneg hz hs.1
      exact Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, norm_neg, mul_one, Complex.norm_exp, hre]
    exact mul_le_of_le_one_left (norm_nonneg z) h0
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

/-- **Step 5c.** For `Re z ≥ 0`, `t ≥ 0` and every `n`: `‖e^{−(n+1)t} − e^{−(z+n+1)t}‖ ≤ ‖z‖ t e^{−(n+1)t}`. -/
theorem norm_term_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))‖
      ≤ ‖z‖ * t * Real.exp (-(((n : ℝ) + 1) * t)) := by
  have he : Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))
      = -(Complex.exp (-(((n : ℂ) + 1) * t)) * (Complex.exp (-(z * t)) - 1)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have e : -(((n : ℂ) + 1) * t) + -(z * t) = -((z + n + 1) * t) := by ring
    rw [e]
    ring
  have hn : ‖Complex.exp (-(((n : ℂ) + 1) * t))‖ = Real.exp (-(((n : ℝ) + 1) * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [he, norm_neg, norm_mul, hn]
  calc Real.exp (-(((n : ℝ) + 1) * t)) * ‖Complex.exp (-(z * t)) - 1‖
      ≤ Real.exp (-(((n : ℝ) + 1) * t)) * (‖z‖ * t) :=
        mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_sub_one_le hz ht) (Real.exp_pos _).le
    _ = ‖z‖ * t * Real.exp (-(((n : ℝ) + 1) * t)) := by ring

/-- `t ↦ c t e^{−(n+1)t}` is integrable on `t > 0`. -/
theorem integrableOn_mul_exp_neg (c : ℝ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => c * t * Real.exp (-(((n : ℝ) + 1) * t))) (Ioi (0 : ℝ)) := by
  have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Integrable.const_mul
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) hr) c
  have e : (fun t : ℝ => c * t * Real.exp (-(((n : ℝ) + 1) * t)))
      = fun t : ℝ => c * (t ^ (1 : ℝ) * Real.exp (-((n : ℝ) + 1) * t ^ (1 : ℝ))) := by
    funext t
    rw [Real.rpow_one, neg_mul]
    ring
  rw [e]
  exact h

/-- `∫_{t>0} c t e^{−(n+1)t} dt = c / (n+1)²`. -/
theorem integral_mul_exp_neg (c : ℝ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), c * t * Real.exp (-(((n : ℝ) + 1) * t)) = c * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
  have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  have e : (fun t : ℝ => c * t * Real.exp (-(((n : ℝ) + 1) * t)))
      = fun t : ℝ => c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(((n : ℝ) + 1) * t))) := by
    funext t
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  rw [e, integral_const_mul, h, Real.Gamma_two, mul_one, Real.rpow_two, one_div, inv_pow]

/-- Each term of the series is integrable on `t > 0`, for `Re z > 0`. -/
theorem integrable_term {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t)))
      (Ioi (0 : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 < ((n : ℂ) + 1).re := by
    have e : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
    rw [e]
    linarith
  have h2 : 0 < (z + n + 1).re := by
    have e : (z + n + 1).re = z.re + n + 1 := by simp
    rw [e]
    linarith
  exact Integrable.sub (integrableOn_cexp_neg_mul h1) (integrableOn_cexp_neg_mul h2)

/-- `∫_{t>0} ‖e^{−(n+1)t} − e^{−(z+n+1)t}‖ dt ≤ ‖z‖ / (n+1)²` for `Re z > 0`. -/
theorem integral_norm_term_le {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))‖
      ≤ ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
  rw [← integral_mul_exp_neg ‖z‖ n]
  exact setIntegral_mono_on (Integrable.norm (integrable_term hz n)) (integrableOn_mul_exp_neg ‖z‖ n)
    measurableSet_Ioi (fun t ht => norm_term_le hz.le n (Set.mem_Ioi.mp ht).le)

/-- The integrals of the terms' norms are summable, for `Re z > 0`. -/
theorem summable_integral_norm_term {z : ℂ} (hz : 0 < z.re) :
    Summable fun n : ℕ => ∫ t in Ioi (0 : ℝ),
      ‖Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))‖ := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at h3
    have h4 := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using h4
  exact Summable.of_nonneg_of_le (fun n => setIntegral_nonneg measurableSet_Ioi (fun t _ => norm_nonneg _))
    (fun n => integral_norm_term_le hz n) (h1.mul_left ‖z‖)

/-- **Step 5d. Gauss's integral for the digamma function, in the form the kernel's series gives:** for `Re z > 0` off the
integers, `ψ(z) = −γ − 1/z + ∫_{t>0} (e^{−t} − e^{−(z+1)t}) / (1 − e^{−t}) dt`. -/
theorem digamma_integral {z : ℂ} (hz : 0 < z.re) (hzi : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∫ t in Ioi (0 : ℝ), (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))) := by
  rw [Zeta23.DigammaSeries.digamma_series hzi]
  congr 1
  have hterm : ∀ n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) = ∫ t in Ioi (0 : ℝ),
      (Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t))) :=
    fun n => (digamma_term_integral hz n).symm
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => Complex.exp (-(((n : ℂ) + 1) * t)) - Complex.exp (-((z + n + 1) * t)))
      (volume.restrict (Ioi (0 : ℝ))) := fun n => integrable_term hz n
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hint (summable_integral_norm_term hz)]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => (hasSum_term_geometric z (Set.mem_Ioi.mp ht)).tsum_eq)

end GaussArchQSteps
end B321
end SIDEExplicitFormula
