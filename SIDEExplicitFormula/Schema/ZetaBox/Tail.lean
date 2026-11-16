/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZetaBox/Tail.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(b), W-ORD-ZETA-BOX Z2; the plan relay data/b744_zetabox_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z2, THE TAIL BEYOND THE FIRST SHELL. `θ(t) − 1 = Σ_{n ≥ 1} 2 e^(−π n² t)` (Mathlib's cosine kernel at `a = 0`); the terms `n ≥ 2` are at most
`2 e^(−12 t) / (1 − e^(−12))` for `t ≥ 1` (`π (n + 2)² ≥ 12 (n + 1)`, a geometric series), so for `Re w ≤ 1`
`‖M w − 2 incGamma1 w π‖ ≤ 2 e^(−12) / (12 (1 − e^(−12))) ≤ 11/10^7` (OffZero/IncGamma.lean :198 `lamM_sub_trunc`'s form). No value of `M` is
computed here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZetaBox.Split
import SIDEExplicitFormula.Schema.ZQ.OffZero.Shells

open Set Filter MeasureTheory HurwitzZeta

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZetaBox

open ZQ.OffZero

/-! ## Z2 -- the tail beyond the first shell -/

/-- `θ(t) − 1 = Σ_{n ≥ 0} 2 e^(−π (n + 1)² t)`, from the cosine kernel at `a = 0`. -/
theorem zK_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)) (evenKernel 0 t - 1) := by
  have h := hasSum_nat_cosKernel₀ 0 ht
  have hc : cosKernel ((0 : ℝ) : UnitAddCircle) t = evenKernel 0 t := by
    rw [evenKernel_eq_cosKernel_of_zero]
    first
    | rfl
    | simp
  rw [hc] at h
  simpa only [mul_zero, zero_mul, Real.cos_zero, mul_one] using h

/-- The theta less one and its first shell. -/
def zE (t : ℝ) : ℝ := evenKernel 0 t - 1 - 2 * Real.exp (-(Real.pi * t))

theorem zE_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 2) ^ 2 * t)) (zE t) := by
  have h := (hasSum_nat_add_iff' 1).mpr (zK_hasSum ht)
  have e1 : zE t = evenKernel 0 t - 1 - ∑ i ∈ Finset.range 1, 2 * Real.exp (-Real.pi * ((i : ℝ) + 1) ^ 2 * t) := by
    rw [Finset.sum_range_one, zE]
    norm_num
  rw [e1]
  refine h.congr_fun fun n => ?_
  show 2 * Real.exp (-Real.pi * ((n : ℝ) + 2) ^ 2 * t) = 2 * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * t)
  congr 2
  push_cast
  ring

theorem zE_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ zE t :=
  HasSum.nonneg (fun n => by positivity) (zE_hasSum ht)

/-- `e^(−12) ≤ 62/10^7`. -/
theorem zexp12 : Real.exp (-12) ≤ 62 / 10 ^ 7 := by
  have h := exp_neg_nat_le 12
  push_cast at h
  exact h.trans (by norm_num)

/-- The terms `n ≥ 2`, a geometric series: `zE t ≤ 2 e^(−12 t) / (1 − e^(−12))` for `t ≥ 1`. -/
theorem zE_le {t : ℝ} (ht : 1 ≤ t) : zE t ≤ 2 / (1 - Real.exp (-12)) * Real.exp (-12 * t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hr0 : 0 ≤ Real.exp (-12 * t) := (Real.exp_pos _).le
  have hre : Real.exp (-12 * t) ≤ Real.exp (-12) := Real.exp_le_exp.mpr (by linarith)
  have he := zexp12
  have hg : HasSum (fun n : ℕ => 2 * Real.exp (-12 * t) * Real.exp (-12 * t) ^ n)
      (2 * Real.exp (-12 * t) * (1 - Real.exp (-12 * t))⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left (2 * Real.exp (-12 * t))
  have hterm : ∀ n : ℕ, 2 * Real.exp (-Real.pi * ((n : ℝ) + 2) ^ 2 * t)
      ≤ 2 * Real.exp (-12 * t) * Real.exp (-12 * t) ^ n := by
    intro n
    have e : 2 * Real.exp (-12 * t) * Real.exp (-12 * t) ^ n = 2 * Real.exp (-12 * t + (n : ℝ) * (-12 * t)) := by
      rw [Real.exp_add, Real.exp_nat_mul]
      ring
    rw [e]
    have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hA : 0 ≤ ((n : ℝ) + 2) ^ 2 * t := by positivity
    have h1 := mul_le_mul_of_nonneg_right hp hA
    have h2 : 0 ≤ (n : ℝ) ^ 2 * t := by positivity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
  have hle := hasSum_le hterm (zE_hasSum ht0) hg
  calc zE t ≤ 2 * Real.exp (-12 * t) * (1 - Real.exp (-12 * t))⁻¹ := hle
    _ ≤ 2 * Real.exp (-12 * t) * (1 - Real.exp (-12))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) (by linarith)) (by positivity)
    _ = 2 / (1 - Real.exp (-12)) * Real.exp (-12 * t) := by ring

theorem zE_cont : ContinuousOn zE (Ioi 0) :=
  ((continuousOn_evenKernel 0).sub continuousOn_const).sub
    (by fun_prop : Continuous fun t : ℝ => 2 * Real.exp (-(Real.pi * t))).continuousOn

/-- The bound's integrand. -/
def zBnd (t : ℝ) : ℝ := 2 / (1 - Real.exp (-12)) * Real.exp (-12 * t)

theorem zBnd_int : IntegrableOn zBnd (Ioi 1) :=
  Integrable.const_mul (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 12)) _

theorem norm_zR_le {w : ℂ} (hw : w.re ≤ 1) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖(t : ℂ) ^ (w - 1) * ((zE t : ℝ) : ℂ)‖ ≤ zBnd t := by
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := one_pos.trans ht1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_of_nonneg (zE_nonneg ht0),
    Complex.sub_re, Complex.one_re]
  have h1 : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
  calc t ^ (w.re - 1) * zE t ≤ 1 * zE t := mul_le_mul_of_nonneg_right h1 (zE_nonneg ht0)
    _ = zE t := one_mul _
    _ ≤ zBnd t := zE_le ht1.le

theorem zR_int {w : ℂ} (hw : w.re ≤ 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((zE t : ℝ) : ℂ)) (Ioi 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1)) (Ioi 0) := fun t ht =>
    (Complex.continuousAt_ofReal_cpow_const t (w - 1) (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((zE t : ℝ) : ℂ)) (Ioi 0) :=
    h1.mul (Complex.continuous_ofReal.comp_continuousOn zE_cont)
  refine Integrable.mono' zBnd_int ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => norm_zR_le hw ht)

theorem zTail_numeric : 2 / (1 - Real.exp (-12)) * (Real.exp (-12) / 12) ≤ 11 / 10 ^ 7 := by
  have he := zexp12
  have h0 := Real.exp_pos (-12)
  rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith

/-- **Z2**: `‖M w − 2 incGamma1 w π‖ ≤ 11/10^7` for `Re w ≤ 1`, the shells `n ≥ 2` bounded under the integral. -/
theorem zM_sub_le {w : ℂ} (hw : w.re ≤ 1) : ‖zM w - 2 * incGamma1 w Real.pi‖ ≤ 11 / 10 ^ 7 := by
  have hG := (incGamma1_integrableOn w Real.pi_pos).const_mul (2 : ℂ)
  have hH := zR_int hw
  have hsplit : zM w = 2 * incGamma1 w Real.pi + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((zE t : ℝ) : ℂ) := by
    rw [zM_eq, incGamma1, ← integral_const_mul, ← integral_add hG hH]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [zE, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [hsplit, add_sub_cancel_left]
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * ((zE t : ℝ) : ℂ)‖ ≤ ∫ t in Ioi (1 : ℝ), zBnd t :=
        norm_integral_le_of_norm_le zBnd_int
          (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => norm_zR_le hw ht))
    _ = 2 / (1 - Real.exp (-12)) * (Real.exp (-12) / 12) := by
        unfold zBnd
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-12 : ℝ) < 0) 1, mul_one, neg_div_neg_eq]
    _ ≤ 11 / 10 ^ 7 := zTail_numeric

end ZetaBox
end Schema
end SIDEExplicitFormula
