import SIDEExplicitFormula.Window.KappaClosed
import SIDEExplicitFormula.PoleAutocorrelation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The pole term of the window in the B-spline basis (b766, `(R376)`(4)(d), the plan's L8)

For every choice of weights `c`, the pole term of the autocorrelation `windowKOf c` is twice the integral of the spline times the
integral of the spline over `y`: the transforms at `-i/2` and at `i/2` are the integrals of the logarithmic spline against
`exp (v / 2)` and `exp (-v / 2)` (B321's `poleTerm_weilTest`), read through `y = exp v`. In the basis, the spline's integral is
`(1/16) ∑ c_j`, the B-spline's integral being 1, and its integral over `y` is `∑ c_j ρ(j)`, where `ρ(j) = ∫ B(u) / (u + j) du` is the
fourth difference of `a^3 log a` at `j` over 6, the polynomial parts cancelling in the fourth difference. Nothing here depends on the
values of `c`.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-! ## The pole term as a product of two integrals -/

/-- The transform of the logarithmic spline at `-i/2`: the integral of `gWin c v * exp (v / 2)`. -/
theorem paperFT_gWin_neg_half_I (c : ℕ → ℝ) :
    Zeta23.paperFT (fun u => (gWin c u : ℂ)) (-Complex.I / 2) = ((∫ u, gWin c u * Real.exp (u / 2) : ℝ) : ℂ) := by
  rw [B321.paperFT_neg_half_I, ← integral_complex_ofReal]
  congr 1
  funext u
  simp only [Complex.ofReal_mul]

/-- The transform of the logarithmic spline at `i/2`: the integral of `gWin c v * exp (-v / 2)`. -/
theorem paperFT_gWin_half_I (c : ℕ → ℝ) :
    Zeta23.paperFT (fun u => (gWin c u : ℂ)) (Complex.I / 2) = ((∫ u, gWin c u * Real.exp (-u / 2) : ℝ) : ℂ) := by
  rw [B321.paperFT_half_I, ← integral_complex_ofReal]
  congr 1
  funext u
  simp only [Complex.ofReal_mul]

/-- **The pole term of the autocorrelation**, for every choice of weights: twice the product of the integrals of `gWin c` against
`exp (v / 2)` and against `exp (-v / 2)`. -/
theorem poleTerm_windowKOf_exp (c : ℕ → ℝ) :
    B321.poleTerm (windowKOf c) =
      ((2 * ((∫ u, gWin c u * Real.exp (u / 2)) * ∫ u, gWin c u * Real.exp (-u / 2)) : ℝ) : ℂ) := by
  have hh : ContDiff ℝ 2 (fun u => (gWin c u : ℂ)) := Complex.ofRealCLM.contDiff.comp (contDiff_gWin c)
  have hhs : HasCompactSupport (fun u => (gWin c u : ℂ)) :=
    (hasCompactSupport_gWin c).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  rw [show windowKOf c = Zeta23.EF.weilTest (fun u => (gWin c u : ℂ)) (fun u => (gWin c u : ℂ)) from rfl,
    B321.poleTerm_weilTest hh hhs, paperFT_gWin_neg_half_I, paperFT_gWin_half_I, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ## The two integrals through `y = exp v` -/

/-- The integral of `gWin c v * exp (v / 2)` is the integral of the spline over `y > 1`. -/
theorem integral_gWin_mul_exp (c : ℕ → ℝ) :
    ∫ u, gWin c u * Real.exp (u / 2) = ∫ y in Set.Ioi 1, splineH c y := by
  have e1 : (fun u => gWin c u * Real.exp (u / 2)) = fun u => Real.exp u * splineH c (Real.exp u) := by
    funext u
    have h : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
      rw [← Real.exp_add]
      congr 1
      ring
    show Real.exp (u / 2) * splineH c (Real.exp u) * Real.exp (u / 2) = Real.exp u * splineH c (Real.exp u)
    linear_combination splineH c (Real.exp u) * h
  have hzero : ∀ s : ℝ, s ∉ Set.Ioi (0 : ℝ) → Real.exp s * splineH c (Real.exp s) = 0 := by
    intro s hs
    have hs' : s ≤ 0 := not_lt.mp (fun h => hs (Set.mem_Ioi.mpr h))
    have he : Real.exp s ≤ 1 := by
      calc Real.exp s ≤ Real.exp 0 := Real.exp_le_exp.mpr hs'
        _ = 1 := Real.exp_zero
    rw [splineH_eq_zero c (Real.exp s) (Or.inl he), mul_zero]
  have hexp := integral_comp_exp_Ioi (splineH c) 0
  simp only [smul_eq_mul, Real.exp_zero] at hexp
  rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hexp]

/-- The integral of `gWin c v * exp (-v / 2)` is the integral of the spline over `y`, over `y > 1`. -/
theorem integral_gWin_mul_exp_neg (c : ℕ → ℝ) :
    ∫ u, gWin c u * Real.exp (-u / 2) = ∫ y in Set.Ioi 1, splineH c y / y := by
  have e1 : (fun u => gWin c u * Real.exp (-u / 2)) =
      fun u => Real.exp u * (splineH c (Real.exp u) / Real.exp u) := by
    funext u
    have h : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
      rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
    have hne : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
    show Real.exp (u / 2) * splineH c (Real.exp u) * Real.exp (-u / 2) =
      Real.exp u * (splineH c (Real.exp u) / Real.exp u)
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hne]
    linear_combination splineH c (Real.exp u) * h
  have hzero : ∀ s : ℝ, s ∉ Set.Ioi (0 : ℝ) → Real.exp s * (splineH c (Real.exp s) / Real.exp s) = 0 := by
    intro s hs
    have hs' : s ≤ 0 := not_lt.mp (fun h => hs (Set.mem_Ioi.mpr h))
    have he : Real.exp s ≤ 1 := by
      calc Real.exp s ≤ Real.exp 0 := Real.exp_le_exp.mpr hs'
        _ = 1 := Real.exp_zero
    rw [splineH_eq_zero c (Real.exp s) (Or.inl he), zero_div, mul_zero]
  have hexp := integral_comp_exp_Ioi (fun y => splineH c y / y) 0
  simp only [smul_eq_mul, Real.exp_zero] at hexp
  rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hexp]

/-! ## The integral of the B-spline -/

theorem hasDerivAt_tpow4_shift (k u : ℝ) :
    HasDerivAt (fun x : ℝ => (max (x - k) 0) ^ 4 / 4) (tpow3 (u - k)) u := by
  have h := ((hasDerivAt_maxPow (m := 4) (by norm_num) (u - k)).comp_sub_const u k).div_const 4
  refine h.congr_deriv ?_
  unfold tpow3
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  ring

/-- `∫_0^4 tpow3 (u - k) du = (4 - k)^4 / 4` for `0 ≤ k ≤ 4`. -/
theorem integral_tpow3_shift {k : ℝ} (hk0 : 0 ≤ k) (hk4 : k ≤ 4) :
    ∫ u in (0 : ℝ)..4, tpow3 (u - k) = (4 - k) ^ 4 / 4 := by
  have h3 := contDiff_tpow3.continuous
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_tpow4_shift k u)
    ((by fun_prop : Continuous (fun u : ℝ => tpow3 (u - k))).intervalIntegrable _ _)]
  show (max (4 - k) 0) ^ 4 / 4 - (max (0 - k) 0) ^ 4 / 4 = (4 - k) ^ 4 / 4
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 4 - k), max_eq_right (by linarith : (0 : ℝ) - k ≤ 0)]
  ring

theorem integral_cubicB_Icc : ∫ u in (0 : ℝ)..4, cubicB u = 1 := by
  have h3 := contDiff_tpow3.continuous
  simp only [cubicB_eq_sum]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  have hk : ∀ k ∈ Finset.range 5,
      ∫ u in (0 : ℝ)..4, (bw k : ℝ) * tpow3 (u - k) = (bw k : ℝ) * ((4 - k) ^ 4 / 4) := by
    intro k hk
    have hk4 : (k : ℝ) ≤ 4 := by
      have h5 := Finset.mem_range.mp hk
      exact_mod_cast (by omega : k ≤ 4)
    rw [intervalIntegral.integral_const_mul, integral_tpow3_shift (Nat.cast_nonneg k) hk4]
  rw [Finset.sum_congr rfl hk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat]
  norm_num

/-- **The B-spline's integral is 1.** -/
theorem integral_cubicB : ∫ u, cubicB u = 1 := by
  calc ∫ u, cubicB u = ∫ u in (0 : ℝ)..4, cubicB u := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro u hu
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
        rcases hu with hu | hu
        · exact cubicB_eq_zero_of_nonpos hu
        · exact cubicB_eq_zero_of_ge hu.le
    _ = 1 := integral_cubicB_Icc

/-- One term of the spline's integral: `∫ B(16 y - j) dy = 1/16`. -/
theorem integral_cubicB_affine (j : ℕ) : ∫ y, cubicB (16 * y - j) = 1 / 16 := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => cubicB (x - j)) 16
  have h16 : |(16 : ℝ)⁻¹| = 1 / 16 := by norm_num
  rw [h16, smul_eq_mul] at h
  have ht := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cubicB (x - j)) (j : ℝ)
  simp only [add_sub_cancel_right] at ht
  rw [h, ← ht, integral_cubicB, mul_one]

/-- **The spline's integral**, for every choice of weights: `(1/16) ∑ c_j`. -/
theorem integral_splineH (c : ℕ → ℝ) :
    ∫ y in Set.Ioi 1, splineH c y = (1 / 16) * ∑ j ∈ Finset.Icc 16 16380, c j := by
  have hB := continuous_cubicB
  have hzero : ∀ y : ℝ, y ∉ Set.Ioi (1 : ℝ) → splineH c y = 0 := by
    intro y hy
    exact splineH_eq_zero c y (Or.inl (not_lt.mp (fun h => hy (Set.mem_Ioi.mpr h))))
  have hint : ∀ j : ℕ, Integrable (fun y : ℝ => c j * cubicB (16 * y - j)) := by
    intro j
    have hc : Continuous (fun y : ℝ => c j * cubicB (16 * y - j)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_cubicB_affine (a := 16) (by norm_num) (j : ℝ)).mono (Function.support_mul_subset_right _ _))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  unfold splineH
  rw [integral_finsetSum _ (fun j _ => hint j), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_cubicB_affine]
  ring

/-! ## `ρ(j)`, the integral of the B-spline over `u + j` -/

/-- `ρ(j)`: the fourth difference of `a^3 log a` at `j`, over `6`. -/
def rhoLog (j : ℝ) : ℝ := (∑ k ∈ Finset.range 5, (bw k : ℝ) * ((k : ℝ) + j) ^ 3 * Real.log ((k : ℝ) + j)) / 6

/-- An antiderivative of `(u - k)^3 / (u + j)` where `u + j ≠ 0`. -/
def poleG (k j u : ℝ) : ℝ :=
  (u - k) ^ 3 / 3 - (k + j) * (u - k) ^ 2 / 2 + (k + j) ^ 2 * (u - k) - (k + j) ^ 3 * Real.log (u + j)

theorem hasDerivAt_poleG (k j u : ℝ) (hu : u + j ≠ 0) :
    HasDerivAt (poleG k j) ((u - k) ^ 3 / (u + j)) u := by
  have hA : HasDerivAt (fun y : ℝ => y - k) 1 u := (hasDerivAt_id' u).sub_const k
  have hL : HasDerivAt (fun y : ℝ => Real.log (y + j)) (1 / (u + j)) u :=
    ((hasDerivAt_id' u).add_const j).log hu
  have h := ((((hA.pow 3).div_const 3).sub (((hA.pow 2).const_mul (k + j)).div_const 2)).add
    (hA.const_mul ((k + j) ^ 2))).sub (hL.const_mul ((k + j) ^ 3))
  unfold poleG
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring

theorem continuousOn_tpow3_div (k j : ℝ) (hj : 0 < j) :
    ContinuousOn (fun u : ℝ => tpow3 (u - k) / (u + j)) (Set.Ici 0) := by
  have h3 := contDiff_tpow3.continuous
  refine ContinuousOn.div (f := fun u : ℝ => tpow3 (u - k)) (g := fun u : ℝ => u + j)
    (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop)) (fun u hu => ?_)
  have hu' : 0 ≤ u := Set.mem_Ici.mp hu
  show u + j ≠ 0
  exact (by linarith : (0 : ℝ) < u + j).ne'

theorem intervalIntegrable_of_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  refine (hf.mono (fun u hu => ?_)).intervalIntegrable
  rcases Set.mem_uIcc.mp hu with h | h
  · exact Set.mem_Ici.mpr (by linarith [h.1])
  · exact Set.mem_Ici.mpr (by linarith [h.1])

/-- `∫_0^4 tpow3 (u - k) / (u + j) du`, `0 ≤ k ≤ 4`, `j > 0`, by the antiderivative from `k`. -/
theorem integral_tpow3_div {k j : ℝ} (hk0 : 0 ≤ k) (hk4 : k ≤ 4) (hj : 0 < j) :
    ∫ u in (0 : ℝ)..4, tpow3 (u - k) / (u + j) = poleG k j 4 - poleG k j k := by
  have hc := continuousOn_tpow3_div k j hj
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_Ici hc le_rfl hk0) (intervalIntegrable_of_Ici hc hk0 (by norm_num : (0 : ℝ) ≤ 4))
  have e1 : ∫ u in (0 : ℝ)..k, tpow3 (u - k) / (u + j) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => ?_), intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le hk0] at hu
    show tpow3 (u - k) / (u + j) = 0
    rw [tpow3_of_nonpos (show u - k ≤ 0 by linarith [hu.2]), zero_div]
  have hne : ∀ u ∈ Set.uIcc k 4, u + j ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hk4] at hu
    exact (by linarith [hu.1] : (0 : ℝ) < u + j).ne'
  have hpc : ContinuousOn (fun u : ℝ => (u - k) ^ 3 / (u + j)) (Set.uIcc k 4) :=
    ContinuousOn.div (f := fun u : ℝ => (u - k) ^ 3) (g := fun u : ℝ => u + j)
      (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop)) hne
  have e2 : ∫ u in k..4, tpow3 (u - k) / (u + j) = poleG k j 4 - poleG k j k := by
    rw [intervalIntegral.integral_congr (g := fun u => (u - k) ^ 3 / (u + j)) (fun u hu => ?_)]
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hasDerivAt_poleG k j u (hne u hu))
        hpc.intervalIntegrable
    · rw [Set.uIcc_of_le hk4] at hu
      show tpow3 (u - k) / (u + j) = (u - k) ^ 3 / (u + j)
      rw [tpow3_of_nonneg (show 0 ≤ u - k by linarith [hu.1])]
  rw [← hsplit, e1, e2, zero_add]

/-- **`ρ(j)` in closed form**: `∫ B(u) / (u + j) du` is the fourth difference of `a^3 log a` at `j` over `6`, `j > 0`. -/
theorem integral_cubicB_div {j : ℝ} (hj : 0 < j) : ∫ u, cubicB u / (u + j) = rhoLog j := by
  have hI : ∫ u, cubicB u / (u + j) = ∫ u in (0 : ℝ)..4, cubicB u / (u + j) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with hu | hu
    · rw [cubicB_eq_zero_of_nonpos hu, zero_div]
    · rw [cubicB_eq_zero_of_ge hu.le, zero_div]
  have hexp : ∀ u : ℝ, cubicB u / (u + j) = ∑ k ∈ Finset.range 5, (bw k : ℝ) / 6 * (tpow3 (u - k) / (u + j)) := by
    intro u
    rw [cubicB_eq_sum, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hI]
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    apply intervalIntegrable_of_Ici _ le_rfl (by norm_num : (0 : ℝ) ≤ 4)
    exact continuousOn_const.mul (continuousOn_tpow3_div (k : ℝ) j hj))]
  have hk : ∀ k ∈ Finset.range 5, ∫ u in (0 : ℝ)..4, (bw k : ℝ) / 6 * (tpow3 (u - k) / (u + j)) =
      (bw k : ℝ) / 6 * (poleG k j 4 - poleG k j k) := by
    intro k hk
    have hk4 : (k : ℝ) ≤ 4 := by
      have h5 := Finset.mem_range.mp hk
      exact_mod_cast (by omega : k ≤ 4)
    rw [intervalIntegral.integral_const_mul, integral_tpow3_div (Nat.cast_nonneg k) hk4 hj]
  rw [Finset.sum_congr rfl hk]
  unfold rhoLog poleG
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat]
  ring

/-- One term of the spline's integral over `y`: `∫ B(16 y - j) / y dy = ρ(j)`, `j ≥ 1`. -/
theorem integral_cubicB_affine_div (j : ℕ) (hj : 1 ≤ j) : ∫ y, cubicB (16 * y - j) / y = rhoLog j := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  have h := Measure.integral_comp_mul_left (fun x : ℝ => 16 * (cubicB (x - j) / x)) 16
  have h16 : |(16 : ℝ)⁻¹| = 1 / 16 := by norm_num
  rw [h16, smul_eq_mul] at h
  have ht := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cubicB (x - j) / x) (j : ℝ)
  simp only [add_sub_cancel_right] at ht
  calc ∫ y, cubicB (16 * y - j) / y = ∫ y, 16 * (cubicB (16 * y - j) / (16 * y)) := by
        congr 1
        funext y
        ring
    _ = 1 / 16 * ∫ x, 16 * (cubicB (x - j) / x) := h
    _ = ∫ x, cubicB (x - j) / x := by
        rw [integral_const_mul]
        ring
    _ = ∫ u, cubicB u / (u + j) := ht.symm
    _ = rhoLog j := integral_cubicB_div hj'

/-- **The spline's integral over `y`**, for every choice of weights: `∑ c_j ρ(j)`. -/
theorem integral_splineH_div (c : ℕ → ℝ) :
    ∫ y in Set.Ioi 1, splineH c y / y = ∑ j ∈ Finset.Icc 16 16380, c j * rhoLog j := by
  have hB := continuous_cubicB
  have hzero : ∀ y : ℝ, y ∉ Set.Ioi (1 : ℝ) → splineH c y / y = 0 := by
    intro y hy
    rw [splineH_eq_zero c y (Or.inl (not_lt.mp (fun h => hy (Set.mem_Ioi.mpr h)))), zero_div]
  have hmax : ∀ j : ℕ, 16 ≤ j → ∀ y : ℝ, cubicB (16 * y - j) / y = cubicB (16 * y - j) / max y 1 := by
    intro j hj y
    by_cases hy : 1 ≤ y
    · rw [max_eq_left hy]
    · have h16 : (16 : ℝ) ≤ j := by exact_mod_cast hj
      rw [cubicB_eq_zero_of_nonpos (show 16 * y - (j : ℝ) ≤ 0 by linarith [not_le.mp hy]), zero_div, zero_div]
  have hint : ∀ j ∈ Finset.Icc 16 16380, Integrable (fun y : ℝ => c j * (cubicB (16 * y - j) / y)) := by
    intro j hj
    have hj16 : 16 ≤ j := (Finset.mem_Icc.mp hj).1
    have e : (fun y : ℝ => c j * (cubicB (16 * y - j) / y)) = fun y => c j * (cubicB (16 * y - j) / max y 1) := by
      funext y
      rw [hmax j hj16 y]
    rw [e]
    have hc : Continuous (fun y : ℝ => c j * (cubicB (16 * y - j) / max y 1)) := by
      refine continuous_const.mul (Continuous.div (f := fun y : ℝ => cubicB (16 * y - j)) (g := fun y : ℝ => max y 1)
        (by fun_prop) (continuous_id.max continuous_const) (fun y => ?_))
      show max y 1 ≠ 0
      exact (lt_of_lt_of_le one_pos (le_max_right y 1)).ne'
    refine hc.integrable_of_hasCompactSupport ?_
    refine (hasCompactSupport_cubicB_affine (a := 16) (by norm_num) (j : ℝ)).mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    apply hy
    rw [h0, zero_div, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hsum : (fun y : ℝ => splineH c y / y) =
      fun y => ∑ j ∈ Finset.Icc 16 16380, c j * (cubicB (16 * y - j) / y) := by
    funext y
    unfold splineH
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsum, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj1 : 1 ≤ j := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  rw [integral_const_mul, integral_cubicB_affine_div j hj1]

/-! ## The pole term in the basis -/

/-- **The pole term of the autocorrelation in the B-spline basis**, for every choice of weights:
`2 ((1/16) ∑ c_j) (∑ c_j ρ(j))`. -/
theorem poleTerm_windowKOf (c : ℕ → ℝ) :
    B321.poleTerm (windowKOf c) =
      ((2 * (((1 / 16) * ∑ j ∈ Finset.Icc 16 16380, c j) * ∑ j ∈ Finset.Icc 16 16380, c j * rhoLog j) : ℝ) : ℂ) := by
  rw [poleTerm_windowKOf_exp, integral_gWin_mul_exp, integral_gWin_mul_exp_neg, integral_splineH, integral_splineH_div]

/-- **The window's pole term** in the B-spline basis: `2 (∫ H) (∫ H / y)` with `∫ H = (1/16) ∑ c_j` and
`∫ H / y = ∑ c_j ρ(j)`. -/
theorem poleTerm_windowK :
    B321.poleTerm windowK =
      ((2 * (((1 / 16) * ∑ j ∈ Finset.Icc 16 16380, coeff j) * ∑ j ∈ Finset.Icc 16 16380, coeff j * rhoLog j) : ℝ) : ℂ) :=
  poleTerm_windowKOf coeff

end Window
end SIDEExplicitFormula
