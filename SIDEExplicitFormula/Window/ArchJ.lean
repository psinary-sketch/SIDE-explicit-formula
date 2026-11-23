import SIDEExplicitFormula.Window.KValues

/-!
# Gauss's integral at the window, read in `x = e ^ t`

b767, (R377)(4)(b), L9's remainder, its part a. `windowKOf_eq_integral` (KValues.lean) gives `k (t) = e ^ (t / 2) K (e ^ t)` with
`K x = ∫ y > 1, H (x y) H (y)`. Gauss's integral over `t > 0`, `∫ (e ^ (-t) k (0) - e ^ (-t / 2) k (t)) / (1 - e ^ (-t)) dt`, the
second summand of `archTermQ_windowK` (Arch.lean), is read in `x = e ^ t` as `∫ x > 1, (K 1 - x K x) / (x (x - 1)) dx`.
No integrability is used: each step is an equality of Bochner integrals.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- The window's `K`: `K x = ∫ y > 1, H (x y) H (y)`. -/
def windowKx (x : ℝ) : ℝ := ∫ y in Set.Ioi 1, windowH (x * y) * windowH y

/-- The window's autocorrelation through `K`: `k (t) = e ^ (t / 2) K (e ^ t)`. -/
theorem windowK_eq_Kx (t : ℝ) : windowK t = ((Real.exp (t / 2) * windowKx (Real.exp t) : ℝ) : ℂ) :=
  windowKOf_eq_integral coeff t

/-- Gauss's integrand at the window, its casts gathered into one real value. -/
theorem archJ_integrand_real (t : ℝ) :
    ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) / (1 - (Real.exp (-t) : ℂ)) =
      (((Real.exp (-t) * windowKx 1 - Real.exp (-t / 2) * (Real.exp (t / 2) * windowKx (Real.exp t))) /
        (1 - Real.exp (-t)) : ℝ) : ℂ) := by
  rw [windowK_eq_Kx 0, windowK_eq_Kx t]
  simp only [zero_div, Real.exp_zero, one_mul]
  first
    | (push_cast; done)
    | (push_cast; ring)

/-- The pointwise identity, in `E = e ^ (t / 2) > 1`. -/
theorem archJ_pt_E (K1 Kx E : ℝ) (hE : 1 < E) :
    ((E ^ 2)⁻¹ * K1 - E⁻¹ * (E * Kx)) / (1 - (E ^ 2)⁻¹) = E ^ 2 * ((K1 - E ^ 2 * Kx) / (E ^ 2 * (E ^ 2 - 1))) := by
  have hE0 : E ≠ 0 := (by linarith : (0 : ℝ) < E).ne'
  have hE2 : E ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < E ^ 2 - 1).ne'
  first
    | (field_simp; done)
    | (field_simp; ring)

/-- Gauss's integrand at `t > 0` is `e ^ t g (e ^ t)`, with `g x = (K 1 - x K x) / (x (x - 1))`. -/
theorem archJ_pt {t : ℝ} (ht : 0 < t) :
    (Real.exp (-t) * windowKx 1 - Real.exp (-t / 2) * (Real.exp (t / 2) * windowKx (Real.exp t))) / (1 - Real.exp (-t)) =
      Real.exp t * ((windowKx 1 - Real.exp t * windowKx (Real.exp t)) / (Real.exp t * (Real.exp t - 1))) := by
  have hE1 : 1 < Real.exp (t / 2) := by
    have h := Real.add_one_lt_exp (by linarith : (0 : ℝ) < t / 2).ne'
    linarith
  have ht2 : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [sq, ← Real.exp_add, add_halves]
  have hneg : Real.exp (-t) = (Real.exp (t / 2) ^ 2)⁻¹ := by
    rw [Real.exp_neg, ht2]
  have hneg2 : Real.exp (-t / 2) = (Real.exp (t / 2))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  rw [hneg, hneg2, ht2]
  exact archJ_pt_E _ _ _ hE1

/-- **Gauss's integral at the window, in `x = e ^ t`**:
`∫ t > 0, (e ^ (-t) k (0) - e ^ (-t / 2) k (t)) / (1 - e ^ (-t)) = ∫ x > 1, (K 1 - x K x) / (x (x - 1))`. -/
theorem archJ_eq_ratio :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((∫ x in Set.Ioi (1 : ℝ), (windowKx 1 - x * windowKx x) / (x * (x - 1)) : ℝ) : ℂ) := by
  have hpt : Set.EqOn
      (fun t : ℝ => ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) / (1 - (Real.exp (-t) : ℂ)))
      (fun t : ℝ => ((Real.exp t * ((windowKx 1 - Real.exp t * windowKx (Real.exp t)) /
        (Real.exp t * (Real.exp t - 1))) : ℝ) : ℂ))
      (Set.Ioi 0) := by
    intro t ht
    show ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) / (1 - (Real.exp (-t) : ℂ)) =
      ((Real.exp t * ((windowKx 1 - Real.exp t * windowKx (Real.exp t)) / (Real.exp t * (Real.exp t - 1))) : ℝ) : ℂ)
    rw [archJ_integrand_real, archJ_pt (Set.mem_Ioi.mp ht)]
  have hexp := integral_comp_exp_Ioi (fun x : ℝ => (windowKx 1 - x * windowKx x) / (x * (x - 1))) 0
  simp only [smul_eq_mul, Real.exp_zero] at hexp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal, hexp]

end Window
end SIDEExplicitFormula
