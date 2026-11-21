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
import Zeta23.WeilEF.VerticalLine

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
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
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
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
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
    exact ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) (by fun_prop) (one_sub_cexp_neg_ne_zero ht))) measurableSet_Ioi
  refine Integrable.mono' hg hm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
  have ht' : 0 < t := ht
  have e1 : Real.exp (-((((0 : ℕ) : ℝ) + 1) * t)) = Real.exp (-t) := by
    simp
  have e2 : Real.exp (-1 * t) = Real.exp (-t) := by
    simp
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
    ((ae_restrict_mem measurableSet_Ioi).mono (fun _t ht => gauss_shift_sub z ht))

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
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
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
    exact (integral_re (integrable_gauss hz)).symm
  rw [digamma_gauss hz hzi, Complex.add_re, Complex.neg_re, Complex.ofReal_re, hre]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => re_gauss_integrand r t)

/-- **Step 9. The control's bracket by Gauss's integral:** `bracketQ r = 2 (−γ + ∫_{t>0} (e^{−t} − e^{−t/2} cos(r t)) /
(1 − e^{−t}) dt) − 2 log(2π/√23)`. -/
theorem bracketQ_eq (r : ℝ) :
    Schema.bracketQ r = 2 * (-Real.eulerMascheroniConstant
      + ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)))
      - 2 * Real.log (2 * Real.pi / Real.sqrt 23) := by
  rw [Schema.bracketQ, re_digamma_half r]

/-- **Step 10a.** `1 − cos x ≤ 2 √|x|` for every real `x`. -/
theorem one_sub_cos_le_two_sqrt (x : ℝ) : 1 - Real.cos x ≤ 2 * Real.sqrt |x| := by
  have hs0 : 0 ≤ Real.sqrt |x| := Real.sqrt_nonneg _
  have hss : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rcases le_or_gt |x| 1 with h | h
  · have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 : x ^ 2 = |x| * |x| := by
      rw [abs_mul_abs_self]
      ring
    have hs1 : Real.sqrt |x| ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h
    have h4 : |x| * |x| ≤ |x| := by nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr h)]
    have h5 : |x| ≤ Real.sqrt |x| := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
    linarith
  · have h1 : -1 ≤ Real.cos x := Real.neg_one_le_cos (x := x)
    have hs1 : 1 ≤ Real.sqrt |x| := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h.le
    linarith

/-- **Step 10b, its algebra.** For `0 < h < 1`, `c ≤ 1`, `s = √t > 0` with `h² (t + 1) ≤ 1`, `1 ≤ q`, `0 ≤ p ≤ q` and
`1 − c ≤ 2 p s`: `|(h² − h c) / (1 − h²)| ≤ q h (1 + 2/s + 2 s)`. -/
theorem gauss_alg {h c s q p t : ℝ} (hpos : 0 < h) (hlt : h < 1) (hc1 : c ≤ 1) (hs0 : 0 < s)
    (hss : s * s = t) (hte : h * h * (t + 1) ≤ 1) (hq1 : 1 ≤ q) (hp0 : 0 ≤ p) (hpq : p ≤ q)
    (hcq : 1 - c ≤ 2 * (p * s)) :
    |(h * h - h * c) / (1 - h * h)| ≤ q * (h * (1 + 2 * s⁻¹ + 2 * s)) := by
  have hhh : h * h ≤ h := mul_le_of_le_one_right hpos.le hlt.le
  have hD : 0 < 1 - h * h := by linarith
  have hu0 : 0 < s⁻¹ := inv_pos.mpr hs0
  have hsu : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  have hq0 : 0 ≤ q := by linarith
  have hX : 1 ≤ 1 + 2 * s⁻¹ + 2 * s := by linarith
  have hqX : 1 ≤ q * (1 + 2 * s⁻¹ + 2 * s) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hq0]
  have hB : 2 * s ≤ (2 * s⁻¹ + 2 * s) * (1 - h * h) := by
    have e : (2 * s⁻¹ + 2 * s) * (1 - h * h) - 2 * s = 2 * s⁻¹ * (1 - h * h * (s * s + 1)) := by
      linear_combination (2 * h * h * s) * hsu
    have h0 : 0 ≤ 2 * s⁻¹ * (1 - h * h * (s * s + 1)) := by
      refine mul_nonneg (by linarith) ?_
      rw [hss]
      linarith
    linarith
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor
  · have i1 := mul_le_mul_of_nonneg_right hqX (mul_nonneg hpos.le hD.le)
    have i2 := mul_le_mul_of_nonneg_left hhh hpos.le
    have i3 := mul_le_mul_of_nonneg_left hc1 hpos.le
    first
    | linarith
    | nlinarith [i1, i2, i3]
  · have i1 := mul_le_mul_of_nonneg_left hcq hpos.le
    have i2 := mul_le_mul_of_nonneg_right hpq (mul_nonneg (mul_nonneg zero_le_two hpos.le) hs0.le)
    have i3 := mul_le_mul_of_nonneg_left hB (mul_nonneg hq0 hpos.le)
    have i4 := mul_nonneg (mul_nonneg hq0 hpos.le) hD.le
    first
    | linarith
    | nlinarith [i1, i2, i3, i4, hhh]

/-- `√|r| ≤ (1 + r²)^{1/4}`. -/
theorem sqrt_abs_le_rpow (r : ℝ) : Real.sqrt |r| ≤ (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  have hy : (0 : ℝ) ≤ 1 + r ^ 2 := by positivity
  have h1 : |r| ≤ Real.sqrt (1 + r ^ 2) := Real.abs_le_sqrt (by linarith)
  have h2 : Real.sqrt (Real.sqrt (1 + r ^ 2)) = (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
    first
    | norm_num
    | (congr 1; norm_num)
  rw [← h2]
  exact Real.sqrt_le_sqrt h1

/-- **Step 10b. A bound on the bracket's integrand:** for `t > 0`,
`|(e^{−t} − e^{−t/2} cos(r t)) / (1 − e^{−t})| ≤ (1 + r²)^{1/4} · e^{−t/2} (1 + 2/√t + 2√t)`. -/
theorem abs_gauss_integrand_le (r : ℝ) {t : ℝ} (ht : 0 < t) :
    |(Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t))|
      ≤ (1 + r ^ 2) ^ (1 / 4 : ℝ) * (Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t)) := by
  have he : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hte : Real.exp (-t) * (t + 1) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h1
    first
    | linarith
    | nlinarith [h1]
  have hlt : Real.exp (-t / 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hcq : 1 - Real.cos (r * t) ≤ 2 * (Real.sqrt |r| * Real.sqrt t) := by
    have h1 := one_sub_cos_le_two_sqrt (r * t)
    rwa [abs_mul, abs_of_pos ht, Real.sqrt_mul (abs_nonneg r)] at h1
  have hq1 : 1 ≤ (1 + r ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg r] : (1 : ℝ) ≤ 1 + r ^ 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [he] at hte ⊢
  exact gauss_alg (Real.exp_pos _) hlt (Real.cos_le_one _) (Real.sqrt_pos.mpr ht) (Real.mul_self_sqrt ht.le) hte
    hq1 (Real.sqrt_nonneg _) (sqrt_abs_le_rpow r) hcq

/-- **Step 10c.** The bound in `t` is integrable on `t > 0`. -/
theorem integrableOn_gauss_majorant :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t)) (Ioi (0 : ℝ)) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1) (by norm_num) (by norm_num) hb
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (by norm_num) (by norm_num) hb
  have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 / 2) (p := 1) (by norm_num) (by norm_num) hb
  have hsum : IntegrableOn (fun t : ℝ => t ^ (0 : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ))
      + 2 * (t ^ (-(1 / 2) : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)))
      + 2 * (t ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)))) (Ioi (0 : ℝ)) :=
    Integrable.add (Integrable.add h0 (Integrable.const_mul h1 2)) (Integrable.const_mul h2 2)
  have key : ∀ t : ℝ, 0 < t → t ^ (0 : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ))
      + 2 * (t ^ (-(1 / 2) : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)))
      + 2 * (t ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)))
      = Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t) := by
    intro t ht
    have e1 : Real.exp (-(1 / 2) * t ^ (1 : ℝ)) = Real.exp (-t / 2) := by
      rw [Real.rpow_one]
      congr 1
      ring
    have e2 : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
    have e3 : t ^ (1 / 2 : ℝ) = Real.sqrt t := by
      rw [Real.sqrt_eq_rpow]
    rw [e1, e2, e3, Real.rpow_zero]
    ring
  exact Integrable.congr hsum ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => key t ht))

/-- **Step 10d.** `r ↦ ‖k̂(r)‖ (1 + r²)^{1/4}` is integrable for `k` in classK: `‖k̂(r)‖ ≤ C/(1 + r²)`. -/
theorem integrable_norm_paperFT_mul_quarter {k : ℝ → ℂ} (hk : classK k) :
    Integrable (fun r : ℝ => ‖Zeta23.paperFT k r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ)) := by
  unfold classK at hk
  obtain ⟨-, hk2, hkc, -⟩ := hk
  obtain ⟨Λ, hΛ⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  obtain ⟨C, hb0⟩ : ∃ C : ℝ, ∀ r : ℝ, ‖Zeta23.paperFT k r‖ * (1 + r ^ 2) ≤ C :=
    ⟨_, fun r => Zeta23.EF.norm_paperFT_mul_one_add_sq_le hk2 hΛ r⟩
  have hcont : Continuous (fun r : ℝ => Zeta23.paperFT k r) :=
    (Zeta23.WeilEF.differentiable_paperFT hk2.continuous hkc).continuous.comp Complex.continuous_ofReal
  have hmaj : Integrable (fun r : ℝ => C * ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul C
  have hqc : Continuous (fun r : ℝ => (1 + r ^ 2) ^ (1 / 4 : ℝ)) := by
    first
    | exact (continuous_const.add (continuous_pow 2)).rpow_const (fun _ => Or.inr (by norm_num))
    | fun_prop
  refine Integrable.mono' hmaj (hcont.norm.mul hqc).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => ?_)
  have hq : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hpos : 0 ≤ (1 + r ^ 2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hq.le _
  have hb : ‖Zeta23.paperFT k r‖ ≤ C / (1 + r ^ 2) := by
    rw [le_div_iff₀ hq]
    exact hb0 r
  have e : ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) = (1 + r ^ 2) ^ (1 / 4 : ℝ) / (1 + r ^ 2) := by
    rw [Real.norm_eq_abs, sq_abs, show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq,
      Real.rpow_one]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hpos), e]
  calc ‖Zeta23.paperFT k r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) ≤ C / (1 + r ^ 2) * (1 + r ^ 2) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hb hpos
    _ = C * ((1 + r ^ 2) ^ (1 / 4 : ℝ) / (1 + r ^ 2)) := by ring

/-- **Step 10e.** `(r, t) ↦ k̂(r) (e^{−t} − e^{−t/2} cos(r t)) / (1 − e^{−t})` is integrable on `ℝ × (0, ∞)`, bounded by the
product of the integrable functions of Steps 10c and 10d. -/
theorem integrable_gauss_prod {k : ℝ → ℂ} (hk : classK k) :
    Integrable (Function.uncurry fun (r t : ℝ) => Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hAB := Integrable.mul_prod (integrable_norm_paperFT_mul_quarter hk) integrableOn_gauss_majorant
  have hcont : Continuous (fun r : ℝ => Zeta23.paperFT k r) := by
    have hk' := hk
    unfold classK at hk'
    obtain ⟨-, hk2, hkc, -⟩ := hk'
    exact (Zeta23.WeilEF.differentiable_paperFT hk2.continuous hkc).continuous.comp Complex.continuous_ofReal
  have hGm : Measurable (fun p : ℝ × ℝ =>
      (Real.exp (-p.2) - Real.exp (-p.2 / 2) * Real.cos (p.1 * p.2)) / (1 - Real.exp (-p.2))) := by
    first
    | fun_prop
    | exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Real.exp (-p.2) - Real.exp (-p.2 / 2) * Real.cos (p.1 * p.2)).measurable).div
        ((by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.exp (-p.2)).measurable)
    | measurability
  have hm : AEStronglyMeasurable (Function.uncurry fun (r t : ℝ) => Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hcont.measurable.comp measurable_fst).mul (Complex.measurable_ofReal.comp hGm)
  have hprod : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))
      = ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi (0 : ℝ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))), p.2 ∈ Ioi (0 : ℝ) := by
    rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)] with p hp
    exact hp.2
  refine Integrable.mono' hAB hm ?_
  filter_upwards [hae] with p hp
  obtain ⟨r, t⟩ := p
  have ht : 0 < t := hp
  show ‖Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ)‖
    ≤ ‖Zeta23.paperFT k r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
      (Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Zeta23.paperFT k r‖ * |(Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t))|
      ≤ ‖Zeta23.paperFT k r‖ * ((1 + r ^ 2) ^ (1 / 4 : ℝ) *
          (Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t))) :=
        mul_le_mul_of_nonneg_left (abs_gauss_integrand_le r ht) (norm_nonneg _)
    _ = ‖Zeta23.paperFT k r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
          (Real.exp (-t / 2) * (1 + 2 * (Real.sqrt t)⁻¹ + 2 * Real.sqrt t)) := by ring

/-- **Step 10f. The integral in `r` at each `t`, by Steps 1 and 2:**
`(1/2π) ∫ k̂(r) (e^{−t} − e^{−t/2} cos(r t)) / (1 − e^{−t}) dr = (e^{−t} k(0) − e^{−t/2} k(t)) / (1 − e^{−t})`. -/
theorem integral_paperFT_mul_gauss {k : ℝ → ℂ} (hk : classK k) (t : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ)
      = ((Real.exp (-t) : ℂ) * k 0 - (Real.exp (-t / 2) : ℂ) * k t) / (1 - (Real.exp (-t) : ℂ)) := by
  have hk' := hk
  unfold classK at hk'
  obtain ⟨-, hk2, hkc, -⟩ := hk'
  have hFk := Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hkc
  have hF := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hFc := Zeta23.EF.integrable_paperFT_mul_cos hFk t
  have e : ∀ r : ℝ, Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ)
      = ((Real.exp (-t) : ℂ) * Zeta23.paperFT k r
          - (Real.exp (-t / 2) : ℂ) * (Zeta23.paperFT k r * (Real.cos (r * t) : ℂ))) * (1 - (Real.exp (-t) : ℂ))⁻¹ := by
    intro r
    push_cast
    ring
  simp_rw [e]
  rw [integral_mul_const, integral_sub (hF.const_mul _) (hFc.const_mul _), integral_const_mul, integral_const_mul]
  have h0 := inversion_zero hk
  have h1 := inversion_cos hk t
  rw [← h0, ← h1]
  ring

/-- **Step 10. Gauss's integral for the control's archimedean term, proved:** the statement `GaussArchQ` holds, from Step 9's
bracket, the interchange of the two integrals (Step 10e) and Fourier inversion (Step 10f). -/
theorem gaussArchQ : GaussArchQ := by
  unfold GaussArchQ
  intro k hk
  have hF : Integrable (fun r : ℝ => Zeta23.paperFT k r) := by
    have hk' := hk
    unfold classK at hk'
    obtain ⟨-, hk2, hkc, -⟩ := hk'
    exact Zeta23.EF.integrable_paperFT_ofReal (Zeta23.EF.integrable_fourier_of_contDiff_two hk2 hkc)
  have hI := integrable_gauss_prod hk
  have hJ : Integrable (fun r : ℝ => ∫ t in Ioi (0 : ℝ), Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ)) :=
    hI.integral_prod_left
  have hswap : (∫ r : ℝ, ∫ t in Ioi (0 : ℝ), Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ))
      = ∫ t in Ioi (0 : ℝ), ∫ r : ℝ, Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ) :=
    integral_integral_swap hI
  have hsplit : ∀ r : ℝ, Zeta23.paperFT k r * (Schema.bracketQ r : ℂ)
      = Zeta23.paperFT k r * ((2 * (Real.log (Real.sqrt 23 / (2 * Real.pi)) - Real.eulerMascheroniConstant) : ℝ) : ℂ)
        + 2 * ∫ t in Ioi (0 : ℝ), Zeta23.paperFT k r *
          (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ) := by
    intro r
    have hc : (∫ t in Ioi (0 : ℝ),
        (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ))
        = (((∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t))) : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [bracketQ_eq r, integral_const_mul, hc]
    generalize (∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t))) = I
    have hl : Real.log (Real.sqrt 23 / (2 * Real.pi)) = -Real.log (2 * Real.pi / Real.sqrt 23) := by
      rw [← Real.log_inv, inv_div]
    rw [hl]
    push_cast
    ring
  have hT : (∫ t in Ioi (0 : ℝ), ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r *
      (((Real.exp (-t) - Real.exp (-t / 2) * Real.cos (r * t)) / (1 - Real.exp (-t)) : ℝ) : ℂ))
      = ∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * k 0 - (Real.exp (-t / 2) : ℂ) * k t) / (1 - (Real.exp (-t) : ℂ)) := by
    congr 1
    funext t
    exact integral_paperFT_mul_gauss hk t
  have h0 := inversion_zero hk
  unfold Schema.archTermQ
  simp_rw [hsplit]
  rw [integral_add (hF.mul_const _) (hJ.const_mul _), integral_mul_const, integral_const_mul, hswap, ← hT,
    integral_const_mul, ← h0]
  push_cast
  ring

end GaussArchQSteps
end B321
end SIDEExplicitFormula
