import SIDEExplicitFormula.Window.KValues

/-!
# The integral of the spline against its dilate, in the B-spline basis

For every choice of weights `c` and every `n ≥ 1`,
`∫ splineH c (n y) * splineH c y dy = (1/16) * ∑_j ∑_m c_j c_m κ_n(j - n m)`, where `κ_n(e) = ∫ B(u) B(n u - e) du` (`kappaB`):
the product of the two finite sums expanded, each term continuous with compact support, and each term moved to `u = 16 y - m`.
With the autocorrelation at `log n` (`windowKOf_log`), `windowKOf c (log n) = sqrt n * (1/16) * ∑_j ∑_m c_j c_m κ_n(j - n m)`;
`κ_n(e)` is `0` unless `-4 < e < 4 n`.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- `κ_n(e) = ∫ B(u) B(n u - e) du`, `B` the cubic B-spline on `[0, 4]`. -/
def kappaB (n : ℕ) (e : ℤ) : ℝ := ∫ u, cubicB u * cubicB ((n : ℝ) * u - e)

theorem continuous_cubicB : Continuous cubicB := contDiff_cubicB.continuous

/-- For `a > 0`, `cubicB (a y - b)` is `0` outside `[b / a, (b + 4) / a]`. -/
theorem support_cubicB_affine {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Function.support (fun y : ℝ => cubicB (a * y - b)) ⊆ Set.Icc (b / a) ((b + 4) / a) := by
  intro y hy
  rw [Function.mem_support] at hy
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    have h' : y * a < b := (lt_div_iff₀ ha).mp (not_le.mp h)
    exact hy (cubicB_eq_zero_of_nonpos (by nlinarith))
  · by_contra h
    have h' : b + 4 < y * a := (div_lt_iff₀ ha).mp (not_le.mp h)
    exact hy (cubicB_eq_zero_of_ge (by nlinarith))

theorem hasCompactSupport_cubicB_affine {a : ℝ} (ha : 0 < a) (b : ℝ) :
    HasCompactSupport (fun y : ℝ => cubicB (a * y - b)) := by
  show IsCompact (tsupport _)
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (support_cubicB_affine ha b) isClosed_Icc)

/-- One term of the expansion: `∫ B(16 n y - j) B(16 y - m) dy = κ_n(j - n m) / 16`. -/
theorem integral_cubicB_mul_cubicB (n j m : ℕ) :
    ∫ y, cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m) = (1 / 16) * kappaB n ((j : ℤ) - n * m) := by
  have e1 : ∫ y, cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m) =
      (1 / 16) * ∫ x, cubicB ((n : ℝ) * x - j) * cubicB (x - m) := by
    have h := Measure.integral_comp_mul_left (fun x : ℝ => cubicB ((n : ℝ) * x - j) * cubicB (x - m)) 16
    have h16 : |(16 : ℝ)⁻¹| = 1 / 16 := by norm_num
    rw [h16, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext y
    show cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m) = cubicB ((n : ℝ) * (16 * y) - j) * cubicB (16 * y - m)
    rw [show (16 : ℝ) * ((n : ℝ) * y) = (n : ℝ) * (16 * y) by ring]
  have e2 : ∫ x, cubicB ((n : ℝ) * x - j) * cubicB (x - m) = kappaB n ((j : ℤ) - n * m) := by
    have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cubicB ((n : ℝ) * x - j) * cubicB (x - m)) (m : ℝ)
    rw [← h]
    unfold kappaB
    congr 1
    funext u
    show cubicB ((n : ℝ) * (u + m) - j) * cubicB (u + m - m) = cubicB u * cubicB ((n : ℝ) * u - (((j : ℤ) - n * m : ℤ) : ℝ))
    have ha : (n : ℝ) * (u + m) - j = (n : ℝ) * u - (((j : ℤ) - n * m : ℤ) : ℝ) := by push_cast; ring
    have hb : u + (m : ℝ) - m = u := by ring
    rw [ha, hb, mul_comm]
  rw [e1, e2]

/-- **The integral of the spline against its dilate in the B-spline basis**, for every choice of weights and `n ≥ 1`. -/
theorem integral_splineH_mul (c : ℕ → ℝ) (n : ℕ) :
    ∫ y, splineH c (n * y) * splineH c y =
      (1 / 16) * ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380, c j * c m * kappaB n ((j : ℤ) - n * m) := by
  have hexp : ∀ y : ℝ, splineH c (n * y) * splineH c y =
      ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
        c j * c m * (cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m)) := by
    intro y
    unfold splineH
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun m _ => ?_))
    ring
  have hint : ∀ j m : ℕ,
      Integrable (fun y : ℝ => c j * c m * (cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m))) := by
    intro j m
    have hB := continuous_cubicB
    have hc : Continuous (fun y : ℝ => c j * c m * (cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m))) := by
      fun_prop
    refine hc.integrable_of_hasCompactSupport ?_
    refine (hasCompactSupport_cubicB_affine (a := 16) (by norm_num) (m : ℝ)).mono ?_
    exact (Function.support_mul_subset_right _ _).trans (Function.support_mul_subset_right _ _)
  calc ∫ y, splineH c (n * y) * splineH c y
      = ∫ y, ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
          c j * c m * (cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m)) := by
        congr 1
        funext y
        exact hexp y
    _ = ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
          ∫ y, c j * c m * (cubicB (16 * ((n : ℝ) * y) - j) * cubicB (16 * y - m)) := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [integral_finsetSum]
          intro m _
          exact hint j m
        · intro j _
          exact integrable_finsetSum _ (fun m _ => hint j m)
    _ = ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
          c j * c m * ((1 / 16) * kappaB n ((j : ℤ) - n * m)) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun m _ => ?_))
        rw [integral_const_mul, integral_cubicB_mul_cubicB]
    _ = (1 / 16) * ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380, c j * c m * kappaB n ((j : ℤ) - n * m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring

/-- **The autocorrelation at `log n` in the B-spline basis**, for every choice of weights and `n ≥ 1`. -/
theorem windowKOf_log_eq_basis (c : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    windowKOf c (Real.log n) =
      ((Real.sqrt n * ((1 / 16) * ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
        c j * c m * kappaB n ((j : ℤ) - n * m)) : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [windowKOf_log c hn', ← integral_splineH_mul c n]
  congr 2
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hy' : y ≤ 1 := not_lt.mp (fun h => hy (Set.mem_Ioi.mpr h))
  rw [splineH_eq_zero c y (Or.inl hy'), mul_zero]

/-- **The window's autocorrelation at `log n` in the B-spline basis**, `n ≥ 1`. -/
theorem windowK_log_eq_basis {n : ℕ} (hn : 0 < n) :
    windowK (Real.log n) =
      ((Real.sqrt n * ((1 / 16) * ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380,
        coeff j * coeff m * kappaB n ((j : ℤ) - n * m)) : ℝ) : ℂ) :=
  windowKOf_log_eq_basis coeff hn

/-- `κ_n(e) = 0` unless `-4 < e < 4 n`: the two splines' supports do not meet. -/
theorem kappaB_eq_zero (n : ℕ) (e : ℤ) (he : e ≤ -4 ∨ 4 * (n : ℤ) ≤ e) : kappaB n e = 0 := by
  have hz : (fun u : ℝ => cubicB u * cubicB ((n : ℝ) * u - e)) = fun _ => 0 := by
    funext u
    rcases le_or_lt u 0 with hu | hu
    · rw [cubicB_eq_zero_of_nonpos hu, zero_mul]
    rcases le_or_lt 4 u with hu4 | hu4
    · rw [cubicB_eq_zero_of_ge hu4, zero_mul]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases he with he | he
    · have he' : (e : ℝ) ≤ -4 := by exact_mod_cast he
      rw [cubicB_eq_zero_of_ge (by nlinarith), mul_zero]
    · have he' : 4 * (n : ℝ) ≤ e := by exact_mod_cast he
      rw [cubicB_eq_zero_of_nonpos (by nlinarith), mul_zero]
  unfold kappaB
  rw [hz, integral_zero]

end Window
end SIDEExplicitFormula
