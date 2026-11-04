/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/IncGamma.lean
THIS PROGRAMME'S WORK (act b740, ruling (R350)(3), relay data/b740_s5cd_statements.txt S5c) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S5c, THE UPPER INCOMPLETE GAMMA ON `[1, ∞)`. `incGamma1 w a = ∫_{t > 1} t^(w − 1) e^(−a t) dt` for `a > 0` and every `w`: integrable, and at
most `e^(−a)/a` in norm when `Re w ≤ 1` (rows (c1)-(c3), general). For the kernel: `lamM w` against the box's finite sum of these integrals,
within `1e-30`, by `tail_le`, the tail of `θ` that decays in `t` (row (c5)); each shell bounded (row (c6)). No value of `zqFn` is computed
here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Split
import SIDEExplicitFormula.Schema.ZQ.OffZero.Tail
import SIDEExplicitFormula.Schema.ZQ.Continuation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Complex.ExponentialBounds

open Set MeasureTheory Filter

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **(c1)** The upper incomplete gamma on `[1, ∞)`: `∫_{t > 1} t^(w − 1) e^(−a t) dt`. -/
def incGamma1 (w : ℂ) (a : ℝ) : ℂ := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)

theorem incGamma1_kernel_continuousOn (w : ℂ) (a : ℝ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · exact Complex.continuousAt_ofReal_cpow_const t (w - 1) (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))
  · exact (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)).continuousAt

theorem norm_incGamma1_kernel (w : ℂ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)‖ = t ^ (w.re - 1) * Real.exp (-(a * t)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.sub_re, Complex.one_re]

/-- **(c2)** The integrand is integrable on `(1, ∞)` for every `w`. -/
theorem incGamma1_integrableOn (w : ℂ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)) (Ioi 1) := by
  have hk : (-1 : ℝ) < max (w.re - 1) 0 := by linarith [le_max_right (w.re - 1) 0]
  have hg : IntegrableOn (fun t : ℝ => t ^ max (w.re - 1) 0 * Real.exp (-a * t ^ (1 : ℝ))) (Ioi 1) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hk one_pos ha).mono_set (Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hg (((incGamma1_kernel_continuousOn w a).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
    measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
  have ht1 : (1 : ℝ) < t := ht
  show ‖(t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)‖ ≤ t ^ max (w.re - 1) 0 * Real.exp (-a * t ^ (1 : ℝ))
  rw [norm_incGamma1_kernel w a (one_pos.trans ht1), Real.rpow_one, neg_mul]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht1.le (le_max_left _ _)) (Real.exp_pos _).le

/-- **(c3)** For `Re w ≤ 1`, `‖incGamma1 w a‖ ≤ e^(−a)/a`. -/
theorem norm_incGamma1_le {w : ℂ} (hw : w.re ≤ 1) {a : ℝ} (ha : 0 < a) : ‖incGamma1 w a‖ ≤ Real.exp (-a) / a := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 1) := exp_neg_integrableOn_Ioi 1 ha
  have hb : ∀ t ∈ Ioi (1 : ℝ), ‖(t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)‖ ≤ Real.exp (-a * t) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    rw [norm_incGamma1_kernel w a (one_pos.trans ht1), neg_mul]
    have h1 : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
    calc t ^ (w.re - 1) * Real.exp (-(a * t)) ≤ 1 * Real.exp (-(a * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(a * t)) := one_mul _
  have h := norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Ioi hb)
  have e : ∫ t in Ioi (1 : ℝ), Real.exp (-a * t) = Real.exp (-a) / a := by
    rw [integral_exp_mul_Ioi (by linarith : -a < 0) 1, mul_one, neg_div_neg_eq]
  unfold incGamma1
  rw [← e]
  exact h

/-- `θ − 1` on the box: the finite sum of the exponentials off `0`. -/
theorem thetaTr_sub_one (t : ℝ) :
    thetaTr (cc * t) - 1 = ∑ p ∈ trBox.erase 0, Real.exp (-(lam * qR p * t)) := by
  have h := Finset.add_sum_erase trBox (fun p => Real.exp (-(Real.pi * (cc * t)) * qR p)) zero_mem_trBox
  simp only [qR_zero, mul_zero, Real.exp_zero] at h
  rw [thetaTr, ← h, add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← pi_mul_cc]
  congr 1
  ring

theorem shell_pos {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < lam * qR p :=
  mul_pos lam_pos (zero_lt_one.trans_le (one_le_qR hp))

theorem shell_integrableOn (w : ℂ) {p : ℤ × ℤ} (hp : p ∈ trBox.erase 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (Real.exp (-(lam * qR p * t)) : ℂ)) (Ioi 1) :=
  incGamma1_integrableOn w (shell_pos (Finset.ne_of_mem_erase hp))

/-- The box's finite sum of incomplete gammas is the integral of the truncation. -/
theorem sum_incGamma1_eq (w : ℂ) :
    ∑ p ∈ trBox.erase 0, incGamma1 w (lam * qR p)
      = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((thetaTr (cc * t) - 1 : ℝ) : ℂ) := by
  calc ∑ p ∈ trBox.erase 0, incGamma1 w (lam * qR p)
      = ∫ t in Ioi (1 : ℝ), ∑ p ∈ trBox.erase 0, (t : ℂ) ^ (w - 1) * (Real.exp (-(lam * qR p * t)) : ℂ) :=
        (integral_finsetSum _ (fun p hp => shell_integrableOn w hp)).symm
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((thetaTr (cc * t) - 1 : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        simp only [thetaTr_sub_one, Complex.ofReal_sum, Finset.mul_sum]

theorem trunc_integrableOn (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((thetaTr (cc * t) - 1 : ℝ) : ℂ)) (Ioi 1) := by
  refine (integrable_finsetSum (trBox.erase 0) (fun p hp => shell_integrableOn w hp)).congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t _ => ?_)
  simp only [thetaTr_sub_one, Complex.ofReal_sum, Finset.mul_sum]

/-- The tail off the box, decaying in `t`: at most `10 e^(B/2) e^(−B t)`, `B = lam · 225/2`. -/
theorem tail_integrand_le {t : ℝ} (ht : 1 ≤ t) :
    thetaU (cc * t) - thetaTr (cc * t) ≤ 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t)) := by
  have hcc := cc_pos
  obtain ⟨_, h1⟩ := tail_le (u := cc * t) (by nlinarith)
  have e : Real.exp (-Real.pi * (cc * t - cc / 2) * (225 / 2))
      = Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t) := by
    rw [← Real.exp_add, ← pi_mul_cc]
    congr 1
    ring
  calc thetaU (cc * t) - thetaTr (cc * t) ≤ Real.exp (-Real.pi * (cc * t - cc / 2) * (225 / 2)) * thetaU (cc / 2) := h1
    _ ≤ Real.exp (-Real.pi * (cc * t - cc / 2) * (225 / 2)) * 10 :=
        mul_le_mul_of_nonneg_left thetaU_half_le (Real.exp_pos _).le
    _ = 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t)) := by rw [e]; ring

theorem norm_tail_le {w : ℂ} (hw : w.re ≤ 1) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖(t : ℂ) ^ (w - 1) * ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ)‖
      ≤ 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t)) := by
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := one_pos.trans ht1
  have hcc := cc_pos
  obtain ⟨h0, _⟩ := tail_le (u := cc * t) (by nlinarith)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_of_nonneg h0, Complex.sub_re,
    Complex.one_re]
  have h1 : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
  calc t ^ (w.re - 1) * (thetaU (cc * t) - thetaTr (cc * t)) ≤ 1 * (thetaU (cc * t) - thetaTr (cc * t)) :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t)) := by
        rw [one_mul]
        exact tail_integrand_le ht1.le

theorem tail_bound_integrableOn :
    IntegrableOn (fun t : ℝ => 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t))) (Ioi 1) :=
  Integrable.const_mul (Integrable.const_mul (exp_neg_integrableOn_Ioi 1 (mul_pos lam_pos (by norm_num : (0 : ℝ) < 225 / 2))) _) _

theorem tail_integrableOn {w : ℂ} (hw : w.re ≤ 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ)) (Ioi 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1)) (Ioi 0) := fun t ht =>
    (Complex.continuousAt_ofReal_cpow_const t (w - 1) (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
  have h2 : Continuous (fun t : ℝ => ((thetaTr (cc * t) : ℝ) : ℂ)) := by
    unfold thetaTr
    fun_prop
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ)) (Ioi 0) := by
    refine (h1.mul (thetaC_continuousOn.sub h2.continuousOn)).congr (fun t _ => ?_)
    simp only [Pi.mul_apply, Pi.sub_apply, thetaC, Complex.ofReal_sub]
  refine Integrable.mono' tail_bound_integrableOn ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
    measurableSet_Ioi) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => norm_tail_le hw ht)

theorem lam_gt : 13 / 10 < lam := by
  have h23 : Real.sqrt 23 < 24 / 5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs := sqrt23_pos
  unfold lam
  rw [lt_div_iff₀ hs]
  linarith [Real.pi_gt_d2]

theorem tail_numeric :
    10 * (Real.exp (lam * (225 / 2) / 2) * (Real.exp (-(lam * (225 / 2))) / (lam * (225 / 2)))) ≤ 1 / 10 ^ 30 := by
  have hl := lam_gt
  have hB0 : 146 < lam * (225 / 2) := by linarith
  have e : Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2))) = Real.exp (-(lam * (225 / 2) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h73 : Real.exp (-(lam * (225 / 2) / 2)) ≤ Real.exp (-73) := Real.exp_le_exp.mpr (by linarith)
  have hE : (27 / 10 : ℝ) ^ 73 ≤ Real.exp 73 := by
    have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h := pow_le_pow_left₀ (by norm_num) h1 73
    rw [← Real.exp_nat_mul] at h
    have e2 : ((73 : ℕ) : ℝ) * 1 = 73 := by norm_num
    rwa [e2] at h
  have hx : Real.exp (-73) * Real.exp 73 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hx0 := Real.exp_pos (-73)
  have hq : Real.exp (-73) ≤ 1 / (27 / 10) ^ 73 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hE hx0.le]
  calc 10 * (Real.exp (lam * (225 / 2) / 2) * (Real.exp (-(lam * (225 / 2))) / (lam * (225 / 2))))
      = 10 * Real.exp (-(lam * (225 / 2) / 2)) / (lam * (225 / 2)) := by
        rw [← e]
        ring
    _ ≤ 10 * (1 / (27 / 10) ^ 73) / 146 :=
        div_le_div₀ (by positivity) (by linarith) (by norm_num) hB0.le
    _ ≤ 1 / 10 ^ 30 := by norm_num

/-- **(c5)** `lamM w` against the box's finite sum of incomplete gammas, within `1e-30`, for `Re w ≤ 1`. -/
theorem lamM_sub_trunc {w : ℂ} (hw : w.re ≤ 1) :
    ‖lamM w - ∑ p ∈ trBox.erase 0, incGamma1 w (lam * qR p)‖ ≤ 1 / 10 ^ 30 := by
  have hG := trunc_integrableOn w
  have hH := tail_integrableOn hw
  have hsplit : lamM w = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((thetaTr (cc * t) - 1 : ℝ) : ℂ))
      + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ) := by
    rw [lamM_eq, ← integral_add hG hH]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [thetaC, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hsplit, sum_incGamma1_eq, add_sub_cancel_left]
  have hB : 0 < lam * (225 / 2) := mul_pos lam_pos (by norm_num)
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (1 : ℝ), 10 * (Real.exp (lam * (225 / 2) / 2) * Real.exp (-(lam * (225 / 2)) * t)) :=
        norm_integral_le_of_norm_le tail_bound_integrableOn
          (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => norm_tail_le hw ht))
    _ = 10 * (Real.exp (lam * (225 / 2) / 2) * (Real.exp (-(lam * (225 / 2))) / (lam * (225 / 2)))) := by
        rw [integral_const_mul, integral_const_mul, integral_exp_mul_Ioi (a := -(lam * (225 / 2))) (by linarith) 1, mul_one,
          neg_div_neg_eq]
    _ ≤ 1 / 10 ^ 30 := tail_numeric

/-- **(c6)** Each shell off `0`: `‖incGamma1 w (lam · qR p)‖ ≤ e^(−lam qR p)/(lam qR p)` for `Re w ≤ 1`. -/
theorem norm_shell_le {w : ℂ} (hw : w.re ≤ 1) {p : ℤ × ℤ} (hp : p ≠ 0) :
    ‖incGamma1 w (lam * qR p)‖ ≤ Real.exp (-(lam * qR p)) / (lam * qR p) :=
  norm_incGamma1_le hw (shell_pos hp)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
