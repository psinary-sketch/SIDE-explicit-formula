import SIDEExplicitFormula.Window.Pole
import SIDEExplicitFormula.Window.KFast
import SIDEExplicitFormula.Window.PoleData

/-!
# The pole term at the window: the integral of its spline as data

`intH_ok` evaluates the coefficient tree's halving sum by the kernel and reads it equal to `intHNum` (PoleData.lean, written by relay
tools/b766_poledata.py). With KFast.lean's `sumDC_eq` and `aGet_eq`, the sum of the window's coefficients is `intHNum / 10 ^ coeffScale`,
so the integral of its spline over `y > 1` is `intHNum / (16 * 10 ^ coeffScale)`, and the pole term at the window is twice that times
the sum of `coeff j * rhoLog j`. (R376)(4)(d) L8, its data half in part: the sum of `coeff j * rhoLog j` as the certificate's
combination over primes is not proved here.
-/

open MeasureTheory

namespace SIDEExplicitFormula
namespace Window

set_option maxHeartbeats 0 in
/-- The coefficient tree's halving sum over its 16365 places is `intHNum`, by the kernel's evaluation. -/
theorem intH_ok : sumDC aGet 16 16365 14 = intHNum := by decide +kernel

/-- The sum of the integer numerators over `16 ≤ j ≤ 16380` is `intHNum`. -/
theorem sum_coeffInt : ∑ j ∈ Finset.Icc 16 16380, coeffInt j = intHNum := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, ← intH_ok,
    sumDC_eq aGet 14 16 16365 (by norm_num)]
  refine Finset.sum_congr (by norm_num) (fun i _ => ?_)
  rw [aGet_eq]

/-- The sum of the window's coefficients is `intHNum / 10 ^ coeffScale`. -/
theorem sum_coeff : ∑ j ∈ Finset.Icc 16 16380, coeff j = (intHNum : ℝ) / 10 ^ coeffScale := by
  simp only [coeff]
  rw [← sum_coeffInt, Int.cast_sum, Finset.sum_div]

/-- **The integral of the window's spline over `y > 1`** is `intHNum / (16 * 10 ^ coeffScale)`. -/
theorem integral_splineH_window :
    ∫ y in Set.Ioi 1, splineH coeff y = (intHNum : ℝ) / (16 * 10 ^ coeffScale) := by
  rw [integral_splineH, sum_coeff]
  ring

/-- **The pole term at the window**, its first factor as data. -/
theorem poleTerm_windowK_intH :
    B321.poleTerm windowK =
      ((2 * (((intHNum : ℝ) / (16 * 10 ^ coeffScale)) * ∑ j ∈ Finset.Icc 16 16380, coeff j * rhoLog j) : ℝ) : ℂ) := by
  rw [poleTerm_windowK, sum_coeff]
  congr 1
  ring

end Window
end SIDEExplicitFormula
