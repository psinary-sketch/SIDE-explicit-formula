import SIDEExplicitFormula.Window.Instance

/-!
# The autocorrelation at `log n` as an integral of the spline against its dilate

For every choice of weights `c`, the autocorrelation `windowKOf c = weilTest (phiC (gWin c)) (phiC (gWin c))` at `x` is
`exp (x / 2)` times the integral over `y > 1` of `splineH c (exp x * y) * splineH c y`: the convolution written out, the
variable translated by `x`, the factor `exp (x / 2)` taken out, the line cut to `t > 0` where the spline at `exp t` is not `0`,
and `y = exp t` substituted (`integral_comp_exp_Ioi`). At `x = log n`, `n > 0`, this reads
`windowKOf c (log n) = sqrt n * ∫ y > 1, splineH c (n * y) * splineH c y`, so `n ^ (-1/2) k (log n)` is the integral of `H (y) H (n y)`.
No integrability is used: each step is an equality of Bochner integrals.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- The autocorrelation written out: the integral of `gWin c t * gWin c (t - x)`. -/
theorem windowKOf_eq_integral_shift (c : ℕ → ℝ) (x : ℝ) :
    windowKOf c x = ((∫ t, gWin c t * gWin c (t - x) : ℝ) : ℂ) := by
  unfold windowKOf Zeta23.EF.weilTest
  rw [convolution_def, ← integral_complex_ofReal]
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply', Zeta23.EF.tilde, B321.phiC, neg_sub, Complex.conj_ofReal, Complex.ofReal_mul]

/-- The product of the logarithmic spline at `s + x` and at `s`, its exponentials gathered. -/
theorem gWin_add_mul_gWin (c : ℕ → ℝ) (x s : ℝ) :
    gWin c (s + x) * gWin c s =
      Real.exp (x / 2) * (Real.exp s * (splineH c (Real.exp x * Real.exp s) * splineH c (Real.exp s))) := by
  have h1 : Real.exp ((s + x) / 2) * Real.exp (s / 2) = Real.exp (x / 2) * Real.exp s := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (s + x) = Real.exp x * Real.exp s := by
    rw [Real.exp_add, mul_comm]
  show Real.exp ((s + x) / 2) * splineH c (Real.exp (s + x)) * (Real.exp (s / 2) * splineH c (Real.exp s)) =
    Real.exp (x / 2) * (Real.exp s * (splineH c (Real.exp x * Real.exp s) * splineH c (Real.exp s)))
  rw [h2]
  linear_combination (splineH c (Real.exp x * Real.exp s) * splineH c (Real.exp s)) * h1

/-- **The autocorrelation as an integral over `y > 1`**, for every choice of weights:
`windowKOf c x = exp (x / 2) * ∫ y > 1, splineH c (exp x * y) * splineH c y`. -/
theorem windowKOf_eq_integral (c : ℕ → ℝ) (x : ℝ) :
    windowKOf c x =
      ((Real.exp (x / 2) * ∫ y in Set.Ioi 1, splineH c (Real.exp x * y) * splineH c y : ℝ) : ℂ) := by
  rw [windowKOf_eq_integral_shift]
  congr 1
  have htr : ∫ t, gWin c t * gWin c (t - x) = ∫ s, gWin c (s + x) * gWin c s := by
    have h := integral_add_right_eq_self (μ := volume) (fun t => gWin c t * gWin c (t - x)) x
    simp only [add_sub_cancel_right] at h
    exact h.symm
  have hzero : ∀ s : ℝ, s ∉ Set.Ioi (0 : ℝ) →
      Real.exp s * (splineH c (Real.exp x * Real.exp s) * splineH c (Real.exp s)) = 0 := by
    intro s hs
    have hs' : s ≤ 0 := not_lt.mp (fun h => hs (Set.mem_Ioi.mpr h))
    have he : Real.exp s ≤ 1 := by
      calc Real.exp s ≤ Real.exp 0 := Real.exp_le_exp.mpr hs'
        _ = 1 := Real.exp_zero
    rw [splineH_eq_zero c (Real.exp s) (Or.inl he), mul_zero, mul_zero]
  have hexp := integral_comp_exp_Ioi (fun y => splineH c (Real.exp x * y) * splineH c y) 0
  simp only [smul_eq_mul, Real.exp_zero] at hexp
  rw [htr]
  simp only [gWin_add_mul_gWin]
  rw [integral_const_mul, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hexp]

/-- **The autocorrelation at `log n`**, `n > 0`, for every choice of weights:
`windowKOf c (log n) = sqrt n * ∫ y > 1, splineH c (n * y) * splineH c y`. -/
theorem windowKOf_log (c : ℕ → ℝ) {n : ℝ} (hn : 0 < n) :
    windowKOf c (Real.log n) =
      ((Real.sqrt n * ∫ y in Set.Ioi 1, splineH c (n * y) * splineH c y : ℝ) : ℂ) := by
  rw [windowKOf_eq_integral, Real.exp_log hn]
  have hs : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [hs]

/-- **The window's autocorrelation at `log n`**, `n > 0`: `windowK (log n) = sqrt n * ∫ y > 1, windowH (n * y) * windowH y`. -/
theorem windowK_log {n : ℝ} (hn : 0 < n) :
    windowK (Real.log n) = ((Real.sqrt n * ∫ y in Set.Ioi 1, windowH (n * y) * windowH y : ℝ) : ℂ) :=
  windowKOf_log coeff hn

end Window
end SIDEExplicitFormula
