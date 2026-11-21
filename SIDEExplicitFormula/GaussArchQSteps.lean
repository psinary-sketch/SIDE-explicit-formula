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

/-- `1 − e^{−t} ≠ 0` for `t > 0`. -/
theorem one_sub_cexp_neg_ne_zero {t : ℝ} (ht : 0 < t) : 1 - Complex.exp (-(t : ℂ)) ≠ 0 := by
  intro h
  have h1 : Complex.exp (-(t : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have h2 := norm_cexp_neg_lt_one ht
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- **Step 6a.** For `Re z ≥ 0` and `t > 0`, the shifted integrand bounded through its series' terms:
`‖(e^{−t} − e^{−(z+1)t}) / (1 − e^{−t})‖ ≤ ‖z‖ t e^{−t} / (1 − e^{−t})`. -/
theorem norm_gauss_shift_le {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 < t) :
    ‖(Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ)))‖
      ≤ ‖z‖ * t * (Real.exp (-t) / (1 - Real.exp (-t))) := by
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have he : ∀ n : ℕ, Real.exp (-(((n : ℝ) + 1) * t)) = Real.exp (-t) * Real.exp (-t) ^ n := by
    intro n
    first
    | (rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring)
    | (rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf)
    | (rw [← Real.exp_nsmul, ← Real.exp_add]; congr 1; simp only [nsmul_eq_mul]; ring)
  have hf : (fun n : ℕ => ‖z‖ * t * Real.exp (-(((n : ℝ) + 1) * t)))
      = fun n : ℕ => ‖z‖ * t * Real.exp (-t) * Real.exp (-t) ^ n := by
    funext n
    rw [he n]
    ring
  have hg : HasSum (fun n : ℕ => ‖z‖ * t * Real.exp (-(((n : ℝ) + 1) * t)))
      (‖z‖ * t * (Real.exp (-t) / (1 - Real.exp (-t)))) := by
    rw [hf, div_eq_mul_inv, ← mul_assoc]
    exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  exact (hasSum_term_geometric z ht).norm_le_of_bounded hg (fun n => norm_term_le hz n ht.le)

/-- **Step 6b.** For `t > 0`: `t e^{−t} / (1 − e^{−t}) ≤ (t + 1) e^{−t}`, from `t + 1 ≤ e^t`. -/
theorem mul_div_one_sub_exp_le {t : ℝ} (ht : 0 < t) :
    t * (Real.exp (-t) / (1 - Real.exp (-t))) ≤ (t + 1) * Real.exp (-t) := by
  have hr0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hr1 : Real.exp (-t) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-t) := by linarith
  have h2 : Real.exp t * Real.exp (-t) = 1 := by
    first
    | (rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
    | (rw [← Real.exp_add]; simp)
  have h1 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) hr0.le
  rw [h2] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hr0.le
  rw [mul_div_assoc', div_le_iff₀ hd]
  nlinarith [h3]

/-- **Step 6c.** For `Re z ≥ 0` the shifted integrand is integrable on `t > 0`, bounded by `‖z‖ (t + 1) e^{−t}`. -/
theorem integrable_gauss_shift {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (fun t : ℝ => (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))))
      (Ioi (0 : ℝ)) := by
  have hg : IntegrableOn
      (fun t : ℝ => ‖z‖ * t * Real.exp (-((((0 : ℕ) : ℝ) + 1) * t)) + ‖z‖ * Real.exp (-1 * t)) (Ioi (0 : ℝ)) :=
    Integrable.add (integrableOn_mul_exp_neg ‖z‖ 0) (Integrable.const_mul (exp_neg_integrableOn_Ioi 0 one_pos) ‖z‖)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    first
    | exact ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt
        (ContinuousAt.div (by fun_prop) (by fun_prop) (one_sub_cexp_neg_ne_zero ht))) measurableSet_Ioi
    | exact ContinuousOn.aestronglyMeasurable (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => one_sub_cexp_neg_ne_zero ht)) measurableSet_Ioi
    | exact (by fun_prop : Measurable (fun t : ℝ =>
        (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))))).aestronglyMeasurable
    | exact (by measurability : Measurable (fun t : ℝ =>
        (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))))).aestronglyMeasurable
  refine Integrable.mono' hg hm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
  have ht' : 0 < t := ht
  have e1 : Real.exp (-((((0 : ℕ) : ℝ) + 1) * t)) = Real.exp (-t) := by
    first
    | simp
    | (congr 1; push_cast; ring)
  have e2 : Real.exp (-1 * t) = Real.exp (-t) := by
    first
    | simp
    | (congr 1; ring)
  rw [e1, e2]
  calc ‖(Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ)))‖
      ≤ ‖z‖ * t * (Real.exp (-t) / (1 - Real.exp (-t))) := norm_gauss_shift_le hz ht'
    _ = ‖z‖ * (t * (Real.exp (-t) / (1 - Real.exp (-t)))) := by ring
    _ ≤ ‖z‖ * ((t + 1) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (mul_div_one_sub_exp_le ht') (norm_nonneg z)
    _ = ‖z‖ * t * Real.exp (-t) + ‖z‖ * Real.exp (-t) := by ring

/-- For `t > 0`: `(e^{−t} − e^{−(z+1)t}) / (1 − e^{−t}) − e^{−z t} = (e^{−t} − e^{−z t}) / (1 − e^{−t})`. -/
theorem gauss_shift_sub (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))) - Complex.exp (-(z * t))
      = (Complex.exp (-(t : ℂ)) - Complex.exp (-(z * t))) / (1 - Complex.exp (-(t : ℂ))) := by
  have hne := one_sub_cexp_neg_ne_zero ht
  have he : Complex.exp (-((z + 1) * t)) = Complex.exp (-(z * t)) * Complex.exp (-(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
  ring

/-- **Step 6d.** Gauss's integrand `(e^{−t} − e^{−z t}) / (1 − e^{−t})` is integrable on `t > 0` for `Re z > 0`. -/
theorem integrable_gauss {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (Complex.exp (-(t : ℂ)) - Complex.exp (-(z * t))) / (1 - Complex.exp (-(t : ℂ))))
      (Ioi (0 : ℝ)) :=
  Integrable.congr (Integrable.sub (integrable_gauss_shift hz.le) (integrableOn_cexp_neg_mul hz))
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => gauss_shift_sub z ht))

/-- **Step 7. Gauss's integral for the digamma function:** for `Re z > 0` off the integers,
`ψ(z) = −γ + ∫_{t>0} (e^{−t} − e^{−z t}) / (1 − e^{−t}) dt`. -/
theorem digamma_gauss {z : ℂ} (hz : 0 < z.re) (hzi : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ)
      + ∫ t in Ioi (0 : ℝ), (Complex.exp (-(t : ℂ)) - Complex.exp (-(z * t))) / (1 - Complex.exp (-(t : ℂ))) := by
  have key : (∫ t in Ioi (0 : ℝ),
        (Complex.exp (-(t : ℂ)) - Complex.exp (-((z + 1) * t))) / (1 - Complex.exp (-(t : ℂ))))
      - ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t))
      = ∫ t in Ioi (0 : ℝ), (Complex.exp (-(t : ℂ)) - Complex.exp (-(z * t))) / (1 - Complex.exp (-(t : ℂ))) := by
    rw [← integral_sub (integrable_gauss_shift hz.le) (integrableOn_cexp_neg_mul hz)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => gauss_shift_sub z ht)
  rw [digamma_integral hz hzi, ← key, integral_cexp_neg_mul hz]
  ring

/-- The real part of Gauss's integrand at `z = 1/2 + i r`:
`(e^{−t} − e^{−t/2} cos(r t)) / (1 − e^{−t})`. -/
theorem re_gauss_integrand (r t : ℝ) :
    ((Complex.exp (-(t : ℂ)) - Complex.exp (-((1 / 2 + Complex.I * (r : ℂ)) * t))) / (1 - Complex.exp (-(t : ℂ)))).re
      = (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) := by
  have h1 : Complex.exp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have h2 : Complex.exp (-((1 / 2 + Complex.I * (r : ℂ)) * t))
      = ((Real.exp (-t / 2) : ℝ) : ℂ) * Complex.exp (((-(r * t) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **Step 8. The real part of the digamma function on the critical line, by Gauss's integral:**
`Re ψ(1/2 + i r) = −γ + ∫_{t>0} (e^{−t} − e^{−t/2} cos(r t)) / (1 − e^{−t}) dt`. -/
theorem re_digamma_half (r : ℝ) :
    (Complex.digamma (1 / 2 + Complex.I * (r : ℂ))).re = -Real.eulerMascheroniConstant
      + ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) := by
  have e : (1 / 2 + Complex.I * (r : ℂ)).re = 1 / 2 := by
    first
    | (rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]; ring)
    | norm_num
    | simp
    | (simp; norm_num)
  have hz : 0 < (1 / 2 + Complex.I * (r : ℂ)).re := by
    rw [e]
    norm_num
  have hzi : (1 / 2 + Complex.I * (r : ℂ)) ∈ Complex.integerComplement := by
    simp only [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro n hn
    have h := congrArg Complex.re hn
    rw [Complex.intCast_re, e] at h
    have h3 : (2 : ℝ) * (n : ℝ) = 1 := by linarith
    have h4 : (2 : ℤ) * n = 1 := by exact_mod_cast h3
    omega
  have hre : (∫ t in Ioi (0 : ℝ), (Complex.exp (-(t : ℂ)) - Complex.exp (-((1 / 2 + Complex.I * (r : ℂ)) * t)))
        / (1 - Complex.exp (-(t : ℂ)))).re
      = ∫ t in Ioi (0 : ℝ), ((Complex.exp (-(t : ℂ)) - Complex.exp (-((1 / 2 + Complex.I * (r : ℂ)) * t)))
        / (1 - Complex.exp (-(t : ℂ)))).re := by
    have h := integral_re (integrable_gauss hz)
    first
    | exact h.symm
    | (simp only [RCLike.re_to_complex] at h; exact h.symm)
    | simpa using h.symm
  rw [digamma_gauss hz hzi, Complex.add_re, Complex.neg_re, Complex.ofReal_re, hre]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => re_gauss_integrand r t)

/-- **Step 9. The control's bracket by Gauss's integral:** `bracketQ r = 2 (−γ + ∫_{t>0} (e^{−t} − e^{−t/2} cos(r t)) /
(1 − e^{−t}) dt) − 2 log(2π/√23)`. -/
theorem bracketQ_eq (r : ℝ) :
    Schema.bracketQ r = 2 * (-Real.eulerMascheroniConstant
      + ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)))
      - 2 * Real.log (2 * Real.pi / Real.sqrt 23) := by
  first
  | (rw [Schema.bracketQ, re_digamma_half r])
  | (unfold Schema.bracketQ; rw [re_digamma_half r])
  | (simp only [Schema.bracketQ, re_digamma_half r])

end GaussArchQSteps
end B321
end SIDEExplicitFormula
