import SIDEExplicitFormula.Window.ArchJ

/-!
# Gauss's integral at the window as a double integral

b767, (R377)(4)(b), L9's remainder, its part a continued. For `x > 0`,
`K 1 - x K x = ∫ u > 1, H u (H u - H (u / x))` (`u = x y` in `K x = ∫ y > 1, H (x y) H y`). Over `x > 1` and `u > 1` the
integrand `H u (H u - H (u / x)) / (x (x - 1))` is bounded by `C u |H u| / x ^ 2`, `C` a Lipschitz constant of `H` (`C²` with compact
support), so the order of integration changes; `w = u / x` takes `x > 1` to `0 < w < u`:
`∫ x > 1, (K 1 - x K x) / (x (x - 1)) = ∫ u > 1, H u ∫_0^u (H u - H w) / (u - w) dw`, and with `archJ_eq_ratio` (ArchJ.lean),
Gauss's integral at the window is that double integral.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

theorem windowH_eq_zero_le {y : ℝ} (hy : y ≤ 1) : windowH y = 0 :=
  splineH_eq_zero coeff y (Or.inl hy)

theorem windowH_eq_zero_of_not_mem {y : ℝ} (hy : y ∉ Set.Icc (1 : ℝ) 1024) : windowH y = 0 := by
  apply windowH_eq_zero
  by_contra h
  push_neg at h
  exact hy ⟨h.1, h.2⟩

theorem hasCompactSupport_of_windowH {f : ℝ → ℝ} (hf : ∀ y, windowH y = 0 → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc (fun y hy => hf y (windowH_eq_zero_of_not_mem hy))

theorem integrableOn_of_windowH {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ y, windowH y = 0 → f y = 0)
    (s : Set ℝ) : IntegrableOn f s :=
  (hc.integrable_of_hasCompactSupport (hasCompactSupport_of_windowH hf)).integrableOn

theorem windowH_continuous : Continuous windowH := windowH_contDiff.continuous

theorem windowH_lipschitz : ∃ C, LipschitzWith C windowH :=
  ContDiff.lipschitzWith_of_hasCompactSupport (hasCompactSupport_of_windowH (fun _ h => h)) windowH_contDiff
    (by first | simp | norm_num | decide)

/-- `K x` over the whole line, `H y` being `0` for `y ≤ 1`. -/
theorem windowKx_full (x : ℝ) : windowKx x = ∫ y, windowH (x * y) * windowH y := by
  unfold windowKx
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hy' : y ≤ 1 := not_lt.mp (fun h => hy (Set.mem_Ioi.mpr h))
  rw [windowH_eq_zero_le hy', mul_zero]

theorem windowKx_one : windowKx 1 = ∫ u in Set.Ioi (1 : ℝ), windowH u * windowH u := by
  unfold windowKx
  simp only [one_mul]

/-- `x K x = ∫ u > 1, H u H (u / x)` for `x > 0`, by `u = x y`. -/
theorem mul_windowKx {x : ℝ} (hx : 0 < x) :
    x * windowKx x = ∫ u in Set.Ioi (1 : ℝ), windowH u * windowH (u / x) := by
  have hsub := Measure.integral_comp_mul_left (fun u => windowH u * windowH (u / x)) x
  simp only [mul_div_cancel_left₀ _ hx.ne', smul_eq_mul] at hsub
  rw [windowKx_full, hsub, abs_of_pos (inv_pos.mpr hx), ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hu' : u ≤ 1 := not_lt.mp (fun h => hu (Set.mem_Ioi.mpr h))
  rw [windowH_eq_zero_le hu', zero_mul]

/-- `K 1 - x K x = ∫ u > 1, H u (H u - H (u / x))` for `x > 0`. -/
theorem K1_sub_mul {x : ℝ} (hx : 0 < x) :
    windowKx 1 - x * windowKx x = ∫ u in Set.Ioi (1 : ℝ), windowH u * (windowH u - windowH (u / x)) := by
  have hc := windowH_continuous
  have h1 : IntegrableOn (fun u => windowH u * windowH u) (Set.Ioi (1 : ℝ)) :=
    integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, zero_mul]) _
  have h2 : IntegrableOn (fun u => windowH u * windowH (u / x)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, zero_mul]) _
  rw [mul_windowKx hx, windowKx_one, ← integral_sub h1 h2]
  congr 1
  funext u
  ring

/-- The bound that changes the order of integration: `C u |H u| / x ^ 2` for `x, u > 1`. -/
theorem archJ_bound {C : NNReal} (hC : LipschitzWith C windowH) {x u : ℝ} (hx : 1 < x) (hu : 1 < u) :
    ‖windowH u * (windowH u - windowH (u / x)) / (x * (x - 1))‖ ≤ (x ^ 2)⁻¹ * ((C : ℝ) * u * |windowH u|) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hx1ne : x - 1 ≠ 0 := hx1.ne'
  have hd : |u - u / x| = u * (x - 1) / x := by
    rw [abs_of_nonneg (sub_nonneg.mpr (div_le_self hu0.le hx.le))]
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hL : |windowH u - windowH (u / x)| ≤ (C : ℝ) * (u * (x - 1) / x) := by
    have h := hC.dist_le_mul u (u / x)
    rw [Real.dist_eq, Real.dist_eq, hd] at h
    exact h
  have hpos : 0 < x * (x - 1) := mul_pos hx0 hx1
  have hR : (x ^ 2)⁻¹ * ((C : ℝ) * u * |windowH u|) =
      |windowH u| * ((C : ℝ) * (u * (x - 1) / x)) / (x * (x - 1)) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hpos, hR]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hpos.le

/-- The integrand of the double integral is integrable over `x > 1`, `u > 1`. -/
theorem archJ_integrable :
    Integrable (Function.uncurry fun x u : ℝ => windowH u * (windowH u - windowH (u / x)) / (x * (x - 1)))
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
  obtain ⟨C, hC⟩ := windowH_lipschitz
  have hc := windowH_continuous
  have hm : Measurable windowH := hc.measurable
  have h1 : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Ioi 1) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1) (by norm_num) (by norm_num)
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hx))
    show x ^ (-2 : ℝ) = (x ^ 2)⁻¹
    rw [Real.rpow_neg hx0, Real.rpow_two]
  have h2 : IntegrableOn (fun u : ℝ => (C : ℝ) * u * |windowH u|) (Set.Ioi 1) :=
    integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, abs_zero, mul_zero]) _
  have hg := Integrable.mul_prod h1 h2
  refine hg.mono' ?_ ?_
  · have hmeas : Measurable
        (fun p : ℝ × ℝ => windowH p.2 * (windowH p.2 - windowH (p.2 / p.1)) / (p.1 * (p.1 - 1))) := by
      first
        | fun_prop
        | exact ((hm.comp measurable_snd).mul ((hm.comp measurable_snd).sub
            (hm.comp (measurable_snd.div measurable_fst)))).div (measurable_fst.mul (measurable_fst.sub_const 1))
    exact hmeas.aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact archJ_bound hC (Set.mem_Ioi.mp (Set.mem_prod.mp hp).1) (Set.mem_Ioi.mp (Set.mem_prod.mp hp).2)

/-- The pointwise identity of the substitution `w = u / x`. -/
theorem archJ_sub_pt (A u x : ℝ) (hu : 0 < u) (hx : 1 < x) :
    |u * -(x ^ 2)⁻¹| * (A / (u - u * x⁻¹)) = A / (x * (x - 1)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxne : x ≠ 0 := hx0.ne'
  have hx1ne : x - 1 ≠ 0 := (sub_pos.mpr hx).ne'
  have hune : u ≠ 0 := hu.ne'
  have habs : |u * -(x ^ 2)⁻¹| = u * (x ^ 2)⁻¹ := by
    rw [mul_neg, abs_neg, abs_of_pos (mul_pos hu (inv_pos.mpr (pow_pos hx0 2)))]
  have hd : u - u * x⁻¹ = u * (x - 1) / x := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [habs, hd]
  first
    | (field_simp; done)
    | (field_simp; ring)

/-- **The inner integral by `w = u / x`**: `∫ x > 1, (H u - H (u / x)) / (x (x - 1)) = ∫_0^u (H u - H w) / (u - w)`. -/
theorem archJ_inner {u : ℝ} (hu : 0 < u) :
    (∫ x in Set.Ioi (1 : ℝ), (windowH u - windowH (u / x)) / (x * (x - 1))) =
      ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w) := by
  have himg : (fun y : ℝ => u * y⁻¹) '' Set.Ioi 1 = Set.Ioo 0 u := by
    ext w
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy0 : 0 < y := lt_trans zero_lt_one hy
      refine ⟨mul_pos hu (inv_pos.mpr hy0), ?_⟩
      calc u * y⁻¹ < u * 1 := mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hy) hu
        _ = u := mul_one u
    · rintro ⟨hw0, hwu⟩
      have hw : w ≠ 0 := hw0.ne'
      have hu' : u ≠ 0 := hu.ne'
      refine ⟨u * w⁻¹, ?_, ?_⟩
      · rw [← div_eq_mul_inv, one_lt_div hw0]
        exact hwu
      · first
          | (rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hu', one_mul])
          | (field_simp; done)
          | (field_simp; ring)
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ),
      HasDerivWithinAt (fun y : ℝ => u * y⁻¹) (u * -(t ^ 2)⁻¹) (Set.Ioi 1) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_trans zero_lt_one (Set.mem_Ioi.mp ht)).ne'
    exact ((hasDerivAt_inv ht0).const_mul u).hasDerivWithinAt
  have hinj : Set.InjOn (fun y : ℝ => u * y⁻¹) (Set.Ioi 1) := by
    intro a _ b _ hab
    exact inv_inj.mp (mul_left_cancel₀ hu.ne' hab)
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun w => (windowH u - windowH w) / (u - w))
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le hu.le, integral_Ioc_eq_integral_Ioo, hcv]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  show (windowH u - windowH (u / x)) / (x * (x - 1)) =
    |u * -(x ^ 2)⁻¹| • ((windowH u - windowH (u * x⁻¹)) / (u - u * x⁻¹))
  simp only [smul_eq_mul]
  rw [archJ_sub_pt _ u x hu (Set.mem_Ioi.mp hx), div_eq_mul_inv u x]

/-- **`∫ x > 1, (K 1 - x K x) / (x (x - 1)) = ∫ u > 1, H u ∫_0^u (H u - H w) / (u - w)`**. -/
theorem archJ_ratio_eq_double :
    (∫ x in Set.Ioi (1 : ℝ), (windowKx 1 - x * windowKx x) / (x * (x - 1))) =
      ∫ u in Set.Ioi (1 : ℝ), windowH u * ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w) := by
  have h1 : (∫ x in Set.Ioi (1 : ℝ), (windowKx 1 - x * windowKx x) / (x * (x - 1))) =
      ∫ x in Set.Ioi (1 : ℝ), ∫ u in Set.Ioi (1 : ℝ),
        windowH u * (windowH u - windowH (u / x)) / (x * (x - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
    show (windowKx 1 - x * windowKx x) / (x * (x - 1)) =
      ∫ u in Set.Ioi (1 : ℝ), windowH u * (windowH u - windowH (u / x)) / (x * (x - 1))
    rw [K1_sub_mul hx0, integral_div]
  rw [h1, integral_integral_swap archJ_integrable]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (Set.mem_Ioi.mp hu)
  show (∫ x in Set.Ioi (1 : ℝ), windowH u * (windowH u - windowH (u / x)) / (x * (x - 1))) =
    windowH u * ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w)
  rw [← archJ_inner hu0, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  show windowH u * (windowH u - windowH (u / x)) / (x * (x - 1)) =
    windowH u * ((windowH u - windowH (u / x)) / (x * (x - 1)))
  rw [mul_div_assoc]

/-- **L9a, Gauss's integral at the window as a double integral**:
`∫ t > 0, (e ^ (-t) k (0) - e ^ (-t / 2) k (t)) / (1 - e ^ (-t)) = ∫ u > 1, H u ∫_0^u (H u - H w) / (u - w) dw du`. -/
theorem archJ_eq_double :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((∫ u in Set.Ioi (1 : ℝ), windowH u * ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w) : ℝ) : ℂ) := by
  rw [archJ_eq_ratio, archJ_ratio_eq_double]

end Window
end SIDEExplicitFormula
