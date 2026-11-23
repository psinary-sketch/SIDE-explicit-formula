import SIDEExplicitFormula.Window.ArchPiece

/-!
# L9b, its second part: the band term in the spline's basis

`lgI a d` is the integral of `B(v) B(v + d) log (v + a)` over the line. One pair of the window's splines gives
`∫ B(16 u - i) B(16 u - j) log (16 u) du = Lg(i, i - j) / 16` (`integral_cubicB_affine_band`), so the band term of
`archJ_eq_split` is `(1/16) ∑_i ∑_j c_i c_j Lg(i, i - j)` (`integral_windowH_sq_log`); and `Lg(a, d) = 0` where `|d| ≥ 4`, the two
splines' supports meeting in no open set (`lgI_eq_zero_of_ge`, `lgI_eq_zero_of_le`), so only the band `|i - j| ≤ 3` remains.
-/

namespace SIDEExplicitFormula.Window

open MeasureTheory

/-- `Lg(a, d)`: the integral of `B(v) B(v + d) log (v + a)` over the line. -/
noncomputable def lgI (a d : ℝ) : ℝ := ∫ v, cubicB v * cubicB (v + d) * Real.log (v + a)

/-- One term of the band: `∫ B(16 u - i) B(16 u - j) log (16 u) du = Lg(i, i - j) / 16`. -/
theorem integral_cubicB_affine_band (i j : ℕ) :
    ∫ u, cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * u) = 1 / 16 * lgI i ((i : ℝ) - j) := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => cubicB (x - i) * cubicB (x - j) * Real.log x) 16
  have h16 : |(16 : ℝ)⁻¹| = 1 / 16 := by norm_num
  rw [h16, smul_eq_mul] at h
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => cubicB (x - i) * cubicB (x - j) * Real.log x) (i : ℝ)
  simp only [add_sub_cancel_right] at ht
  rw [h, ← ht]
  unfold lgI
  simp only [add_sub_assoc]

/-- Each term of the band is integrable, the logarithm read where the first spline lives, `u ≥ 1`. -/
theorem integrable_band_term (i j : ℕ) (hi : 16 ≤ i) :
    Integrable (fun u : ℝ => coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * u))) := by
  have hB := continuous_cubicB
  have hB1 : Continuous (fun u : ℝ => cubicB (16 * u - i)) := by fun_prop
  have hB2 : Continuous (fun u : ℝ => cubicB (16 * u - j)) := by fun_prop
  have hlog : Continuous (fun u : ℝ => Real.log (16 * max u 1)) :=
    (continuous_const.mul (continuous_id.max continuous_const)).log
      (fun x => (mul_pos (by norm_num : (0 : ℝ) < 16) (lt_of_lt_of_le zero_lt_one (le_max_right x 1))).ne')
  have hc : Continuous (fun u : ℝ =>
      coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * max u 1))) :=
    continuous_const.mul ((hB1.mul hB2).mul hlog)
  have hi' : (16 : ℝ) ≤ i := by exact_mod_cast hi
  have heq : (fun u : ℝ => coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * u))) =
      fun u => coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * max u 1)) := by
    funext u
    rcases le_or_gt 1 u with hu | hu
    · rw [max_eq_left hu]
    · have h0 : cubicB (16 * u - i) = 0 := cubicB_eq_zero_of_nonpos (by linarith)
      simp only [h0, zero_mul, mul_zero]
  rw [heq]
  have hsupp : Function.support (fun u : ℝ =>
      coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * max u 1))) ⊆
      Function.support (fun y : ℝ => cubicB (16 * y - i)) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp only [h0, zero_mul, mul_zero])
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_cubicB_affine (a := 16) (by norm_num) (i : ℝ)).mono hsupp)

/-- **L9b, the band term in the basis**: `∫_{u > 1} H² log (16 u) = (1/16) ∑_i ∑_j c_i c_j Lg(i, i - j)`. -/
theorem integral_windowH_sq_log :
    ∫ u in Set.Ioi (1 : ℝ), windowH u * windowH u * Real.log (16 * u) =
      1 / 16 * ∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ Finset.Icc 16 16380, coeff i * coeff j * lgI i ((i : ℝ) - j) := by
  have hfull : ∫ u in Set.Ioi (1 : ℝ), windowH u * windowH u * Real.log (16 * u) =
      ∫ u, windowH u * windowH u * Real.log (16 * u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hu' : u ≤ 1 := not_lt.mp (fun h => hu (Set.mem_Ioi.mpr h))
    rw [windowH_eq_zero_le hu', zero_mul, zero_mul]
  have hsplit : ∀ u : ℝ, windowH u * windowH u * Real.log (16 * u) =
      ∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ Finset.Icc 16 16380,
        coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * u)) := by
    intro u
    unfold windowH splineH
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hint : ∀ i ∈ Finset.Icc 16 16380, Integrable (fun u : ℝ => ∑ j ∈ Finset.Icc 16 16380,
      coeff i * coeff j * (cubicB (16 * u - i) * cubicB (16 * u - j) * Real.log (16 * u))) := by
    intro i hi
    exact integrable_finsetSum _ (fun j _ => integrable_band_term i j (Finset.mem_Icc.mp hi).1)
  rw [hfull]
  simp only [hsplit]
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [integral_finsetSum _ (fun j _ => integrable_band_term i j (Finset.mem_Icc.mp hi).1), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_cubicB_affine_band]
  ring

/-- `Lg(a, d) = 0` for `d ≥ 4`. -/
theorem lgI_eq_zero_of_ge {a d : ℝ} (hd : 4 ≤ d) : lgI a d = 0 := by
  unfold lgI
  have h : ∀ v : ℝ, cubicB v * cubicB (v + d) * Real.log (v + a) = 0 := by
    intro v
    rcases le_or_gt v 0 with hv | hv
    · rw [cubicB_eq_zero_of_nonpos hv, zero_mul, zero_mul]
    · rw [cubicB_eq_zero_of_ge (by linarith : 4 ≤ v + d), mul_zero, zero_mul]
  simp only [h, integral_zero]

/-- `Lg(a, d) = 0` for `d ≤ -4`. -/
theorem lgI_eq_zero_of_le {a d : ℝ} (hd : d ≤ -4) : lgI a d = 0 := by
  unfold lgI
  have h : ∀ v : ℝ, cubicB v * cubicB (v + d) * Real.log (v + a) = 0 := by
    intro v
    rcases le_or_gt 4 v with hv | hv
    · rw [cubicB_eq_zero_of_ge hv, zero_mul, zero_mul]
    · rw [cubicB_eq_zero_of_nonpos (by linarith : v + d ≤ 0), mul_zero, zero_mul]
  simp only [h, integral_zero]

end SIDEExplicitFormula.Window
