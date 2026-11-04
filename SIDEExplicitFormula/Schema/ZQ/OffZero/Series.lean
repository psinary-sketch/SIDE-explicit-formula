/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Series.lean
THIS PROGRAMME'S WORK (act b741, ruling (R351)(3)(b), relay data/b741_c7_plan.txt (2) (R-S), (5) G1) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G1, THE SERIES ROUTE'S GENERAL ROWS. (c4') `(1/a)^w Γ(w)` splits as the lower piece `∫_{(0,1]} t^(w − 1) e^(−a t) dt` plus `incGamma1 w a`
(`Re w > 0`, `a > 0`), from Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`; the lower piece against its series
`Σ_{k<n} (−a)^k/(k! (w + k))` within `2 a^n/(n! (Re w + n))` when `2a ≤ n + 1` (Complex.exp_bound' under the integral); `incGamma1` Lipschitz in
`a` on `[m, ∞)`, `m > 1`; `(1/r)^w = (2^w)^j (1/(2^j r))^w`. No value is computed here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.IncGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open Set MeasureTheory Filter

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **(c4')** The lower piece: `∫_{(0,1]} t^(w − 1) e^(−a t) dt`. -/
def lowInt (w : ℂ) (a : ℝ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)

theorem lowInt_integrableOn {w : ℂ} (hw : 0 < w.re) (a : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ)) (Ioc 0 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (w - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have h2 := h1.mul_continuousOn (g := fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ))
    (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)).continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h2

/-- **(c4')** For `Re w > 0`, `a > 0`: `(1/a)^w Γ(w) = lowInt w a + incGamma1 w a`. -/
theorem Gamma_split {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 0 < a) :
    (1 / (a : ℂ)) ^ w * Complex.Gamma w = lowInt w a + incGamma1 w a := by
  have h : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ) = (1 / (a : ℂ)) ^ w * Complex.Gamma w := by
    rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi hw ha]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [← h, ← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (lowInt_integrableOn hw a) (incGamma1_integrableOn w ha)]
  rfl

theorem cpow_mul_pow_eq {w : ℂ} {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (t : ℂ) ^ (w - 1) * (t : ℂ) ^ k = (t : ℂ) ^ (w - 1 + k) := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_natCast]

/-- Each term of the lower series: `∫_{(0,1]} t^(w − 1 + k) dt = 1/(w + k)`. -/
theorem integral_cpow_Ioc {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1 + k) = 1 / (w + k) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : -1 < (w - 1 + k).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re]
    linarith
  have hne : w + k ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h'
    linarith
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr)]
  have e : w - 1 + k + 1 = w + k := by ring
  rw [e, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

theorem poly_integrableOn {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1 + k)) (Ioc 0 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (intervalIntegral.intervalIntegrable_cpow' ?_)
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re]
  linarith

/-- The exponential's Taylor polynomial at `−a t`, of degree `< n`. -/
def expPoly (a : ℝ) (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range n, (-((a : ℂ) * t)) ^ k / k.factorial

theorem kernel_poly_eq {w : ℂ} {a t : ℝ} (ht : 0 < t) (n : ℕ) :
    (t : ℂ) ^ (w - 1) * expPoly a n t
      = ∑ k ∈ Finset.range n, (((-a) ^ k / k.factorial : ℝ) : ℂ) * (t : ℂ) ^ (w - 1 + k) := by
  rw [expPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← cpow_mul_pow_eq ht k]
  push_cast
  ring

theorem integral_kernel_poly {w : ℂ} (hw : 0 < w.re) (a : ℝ) (n : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) * expPoly a n t
      = ∑ k ∈ Finset.range n, (((-a) ^ k / k.factorial : ℝ) : ℂ) / (w + k) := by
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => kernel_poly_eq (w := w) (a := a) ht.1 n),
    integral_finsetSum _ (fun k _ => Integrable.const_mul (poly_integrableOn hw k) _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_const_mul, integral_cpow_Ioc hw k, mul_one_div]

/-- **(c4')** The lower piece against its series: within `2 a^n/(n! (Re w + n))` when `2a ≤ n + 1`. -/
theorem lowInt_sub_sum_le {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 2 * a ≤ n + 1) :
    ‖lowInt w a - ∑ k ∈ Finset.range n, (((-a) ^ k / k.factorial : ℝ) : ℂ) / (w + k)‖
      ≤ 2 * a ^ n / (n.factorial * (w.re + n)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hP : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * expPoly a n t) (Ioc 0 1) := by
    refine IntegrableOn.congr_fun (integrable_finsetSum (Finset.range n) (fun k _ => Integrable.const_mul
      (poly_integrableOn hw k) (((-a) ^ k / k.factorial : ℝ) : ℂ))) ?_ measurableSet_Ioc
    intro t ht
    exact (kernel_poly_eq ht.1 n).symm
  rw [← integral_kernel_poly hw a n, lowInt, ← integral_sub (lowInt_integrableOn hw a) hP]
  have hg : IntegrableOn (fun t : ℝ => 2 * a ^ n / n.factorial * t ^ (w.re - 1 + n)) (Ioc 0 1) :=
    Integrable.const_mul ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))) _
  refine (MeasureTheory.norm_integral_le_of_norm_le hg
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))).trans (le_of_eq ?_)
  · show ‖(t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ) - (t : ℂ) ^ (w - 1) * expPoly a n t‖
        ≤ 2 * a ^ n / n.factorial * t ^ (w.re - 1 + n)
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hx : ‖-((a : ℂ) * t)‖ = a * t := by
      rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg ht0.le]
    have hb : ‖-((a : ℂ) * t)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
      rw [hx, Nat.cast_succ, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left ht1 ha]
    have he := Complex.exp_bound' hb
    rw [hx] at he
    have hE : ((Real.exp (-(a * t)) : ℝ) : ℂ) = Complex.exp (-((a : ℂ) * t)) := by
      simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    rw [← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re, hE, expPoly]
    calc t ^ (w.re - 1) * ‖Complex.exp (-((a : ℂ) * t)) - ∑ k ∈ Finset.range n, (-((a : ℂ) * t)) ^ k / k.factorial‖
        ≤ t ^ (w.re - 1) * ((a * t) ^ n / n.factorial * 2) :=
          mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht0.le _)
      _ = 2 * a ^ n / n.factorial * t ^ (w.re - 1 + n) := by
          rw [Real.rpow_add ht0, Real.rpow_natCast, mul_pow]
          ring
  · have hr : -1 < w.re - 1 + n := by linarith
    have hne : w.re + n ≠ 0 := (by linarith : 0 < w.re + n).ne'
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr)]
    have e : w.re - 1 + n + 1 = w.re + n := by ring
    rw [e, Real.one_rpow, Real.zero_rpow hne, sub_zero]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp <;> ring

/-- `|e^(−u) − e^(−v)| ≤ |u − v| e^(−M)` for `u, v ≥ M`. -/
theorem abs_exp_neg_sub_le {u v M : ℝ} (hu : M ≤ u) (hv : M ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| * Real.exp (-M) := by
  have key : ∀ x y : ℝ, M ≤ x → x ≤ y → |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| * Real.exp (-M) := by
    intro x y hx hxy
    have h1 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : 1 - (y - x) ≤ Real.exp (-(y - x)) := Real.one_sub_le_exp_neg _
    have h3 : Real.exp (-x) ≤ Real.exp (-M) := Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    have hpos := Real.exp_pos (-x)
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp (-x) - Real.exp (-y)), abs_of_nonpos (by linarith : x - y ≤ 0)]
    calc Real.exp (-x) - Real.exp (-y) = Real.exp (-x) * (1 - Real.exp (-(y - x))) := by rw [h1]; ring
      _ ≤ Real.exp (-x) * (y - x) := mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ ≤ Real.exp (-M) * (y - x) := mul_le_mul_of_nonneg_right h3 (by linarith)
      _ = -(x - y) * Real.exp (-M) := by ring
  rcases le_total u v with h | h
  · exact key u v hu h
  · rw [abs_sub_comm, abs_sub_comm u v]
    exact key v u hv h

theorem norm_kernel_sub_le {w : ℂ} (hw : w.re ≤ 1) {a b m : ℝ} (ha : m ≤ a) (hb : m ≤ b) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖(t : ℂ) ^ (w - 1) * (Real.exp (-(a * t)) : ℂ) - (t : ℂ) ^ (w - 1) * (Real.exp (-(b * t)) : ℂ)‖
      ≤ |a - b| * Real.exp (-1) * Real.exp (-(m - 1) * t) := by
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := one_pos.trans ht1
  rw [← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.sub_re, Complex.one_re]
  have h1 : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
  have h2 := abs_exp_neg_sub_le (u := a * t) (v := b * t) (M := m * t) (by nlinarith) (by nlinarith)
  have h3 : |a * t - b * t| = |a - b| * t := by rw [← sub_mul, abs_mul, abs_of_pos ht0]
  have h4 : t * Real.exp (-(m * t)) ≤ Real.exp (-1) * Real.exp (-(m - 1) * t) := by
    have h5 : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
    calc t * Real.exp (-(m * t)) ≤ Real.exp (t - 1) * Real.exp (-(m * t)) :=
          mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = Real.exp (-1) * Real.exp (-(m - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  have h0 : 0 ≤ |Real.exp (-(a * t)) - Real.exp (-(b * t))| := abs_nonneg _
  calc t ^ (w.re - 1) * |Real.exp (-(a * t)) - Real.exp (-(b * t))|
      ≤ 1 * |Real.exp (-(a * t)) - Real.exp (-(b * t))| := mul_le_mul_of_nonneg_right h1 h0
    _ ≤ |a * t - b * t| * Real.exp (-(m * t)) := by rw [one_mul]; exact h2
    _ = |a - b| * (t * Real.exp (-(m * t))) := by rw [h3]; ring
    _ ≤ |a - b| * (Real.exp (-1) * Real.exp (-(m - 1) * t)) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    _ = |a - b| * Real.exp (-1) * Real.exp (-(m - 1) * t) := by ring

/-- `incGamma1` is Lipschitz in `a` on `[m, ∞)`, `m > 1`, for `Re w ≤ 1`. -/
theorem incGamma1_sub_le {w : ℂ} (hw : w.re ≤ 1) {a b m : ℝ} (hm : 1 < m) (ha : m ≤ a) (hb : m ≤ b) :
    ‖incGamma1 w a - incGamma1 w b‖ ≤ |a - b| * Real.exp (-1) * (Real.exp (-(m - 1)) / (m - 1)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hg : IntegrableOn (fun t : ℝ => |a - b| * Real.exp (-1) * Real.exp (-(m - 1) * t)) (Ioi 1) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 1 (by linarith : (0 : ℝ) < m - 1)) _
  unfold incGamma1
  rw [← integral_sub (incGamma1_integrableOn w ha0) (incGamma1_integrableOn w hb0)]
  refine (MeasureTheory.norm_integral_le_of_norm_le hg
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => norm_kernel_sub_le hw ha hb ht))).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -(m - 1) < 0) 1, mul_one, neg_div_neg_eq]

/-- `(1/r)^w = (2^w)^j (1/(2^j r))^w` for `r > 0`. -/
theorem one_div_cpow_two_pow {r : ℝ} (hr : 0 < r) (w : ℂ) (j : ℕ) :
    (((1 / r : ℝ)) : ℂ) ^ w = ((2 : ℂ) ^ w) ^ j * (((1 / (2 ^ j * r) : ℝ)) : ℂ) ^ w := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : ((1 / (2 ^ j * r) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((1 / (2 ^ (j + 1) * r) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [pow_succ]
      field_simp
    rw [ih, h1, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), pow_succ]
    push_cast
    ring

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
