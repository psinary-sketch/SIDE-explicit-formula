import SIDEExplicitFormula.Window.Coeffs
import SIDEExplicitFormula.Window.Spline

/-!
# The window at its banked coefficients

`windowH`, the spline of `SIDEExplicitFormula.Window.Spline` at the coefficients `coeff` that
`SIDEExplicitFormula.Window.Coeffs` holds from relay data/b765_window.json; `windowG v = exp (v / 2) * windowH (exp v)`;
and `windowK = weilTest windowG windowG`. The window is twice continuously differentiable and `0` outside `[1, 1024]`;
its autocorrelation is in `classK` and `0` where `|u| > log 1024`.
-/

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- The window: the spline at the banked coefficients. -/
def windowH : ℝ → ℝ := splineH coeff

/-- The window in the logarithmic variable. -/
def windowG : ℝ → ℝ := gWin coeff

/-- The window's autocorrelation, `weilTest windowG windowG`. -/
def windowK : ℝ → ℂ := Zeta23.EF.weilTest (B321.phiC windowG) (B321.phiC windowG)

theorem windowG_eq (v : ℝ) : windowG v = Real.exp (v / 2) * windowH (Real.exp v) := rfl

/-- **The window is twice continuously differentiable.** -/
theorem windowH_contDiff : ContDiff ℝ 2 windowH := contDiff_splineH coeff

/-- **The window is `0` outside `[1, 1024]`.** -/
theorem windowH_eq_zero (y : ℝ) (hy : y < 1 ∨ 1024 < y) : windowH y = 0 :=
  splineH_eq_zero coeff y (hy.imp le_of_lt le_of_lt)

/-- **The window's autocorrelation is in `classK`.** -/
theorem windowK_classK : B321.classK windowK := windowKOf_classK coeff

/-- **The window's autocorrelation is `0` where `|u| > log 1024`.** -/
theorem windowK_eq_zero (u : ℝ) (hu : Real.log 1024 < |u|) : windowK u = 0 :=
  windowKOf_eq_zero coeff u hu

end Window
end SIDEExplicitFormula
