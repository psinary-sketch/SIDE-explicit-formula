import SIDEExplicitFormula.PowerWindow

/-!
# The cubic B-spline window and its autocorrelation, for every choice of weights

The cubic B-spline `cubicB` on `[0, 4]` with integer knots, written by truncated cubes; for weights `c`, the spline
`splineH c y = ∑ j ∈ [16, 16380], c j * cubicB (16 * y - j)`; its logarithmic form `gWin c v = exp (v / 2) * splineH c (exp v)`;
and the autocorrelation `windowKOf c = weilTest (phiC (gWin c)) (phiC (gWin c))`. For every `c`: the spline is twice
continuously differentiable and `0` where `y ≤ 1` or `1024 ≤ y`; the autocorrelation is in `classK` and `0` where
`|u| > log 1024`. Nothing here depends on the values of `c`.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- The truncated cube `max x 0 ^ 3`. -/
def tpow3 (x : ℝ) : ℝ := (max x 0) ^ 3

/-- The cubic B-spline on `[0, 4]` with integer knots: the fourth difference of truncated cubes over `3!`. -/
def cubicB (x : ℝ) : ℝ :=
  (tpow3 x - 4 * tpow3 (x - 1) + 6 * tpow3 (x - 2) - 4 * tpow3 (x - 3) + tpow3 (x - 4)) / 6

/-- The spline with weights `c` on the knots `j / 16`, `j` from 16 to 16380. -/
def splineH (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑ j ∈ Finset.Icc 16 16380, c j * cubicB (16 * y - j)

/-- The spline in the logarithmic variable: `exp (v / 2) * splineH c (exp v)`. -/
def gWin (c : ℕ → ℝ) (v : ℝ) : ℝ := Real.exp (v / 2) * splineH c (Real.exp v)

/-- The autocorrelation of the logarithmic spline. -/
def windowKOf (c : ℕ → ℝ) : ℝ → ℂ := Zeta23.EF.weilTest (B321.phiC (gWin c)) (B321.phiC (gWin c))

/-! ## The truncated powers -/

/-- The derivative of `max y 0 ^ m`, `m ≥ 2`, at every point: `m * max x 0 ^ (m - 1)`. -/
theorem hasDerivAt_maxPow {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max y 0) ^ m) ((m : ℝ) * (max x 0) ^ (m - 1)) x := by
  have hm1 : m - 1 ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : (fun y : ℝ => (max y 0) ^ m) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      show (max y 0) ^ m = 0
      rw [max_eq_right (Set.mem_Iio.mp hy).le, zero_pow hm0]
    rw [max_eq_right hx.le, zero_pow hm1, mul_zero]
    exact (hasDerivAt_const _ _ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x).congr_of_eventuallyEq hev
  · subst hx
    rw [max_self, zero_pow hm1, mul_zero]
    have hleft : HasDerivWithinAt (fun y : ℝ => (max y 0) ^ m) 0 (Set.Iic 0) 0 := by
      refine (hasDerivWithinAt_const _ _ _ : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic 0) 0).congr
        (fun y hy => ?_) ?_
      · show (max y 0) ^ m = 0
        rw [max_eq_right (Set.mem_Iic.mp hy), zero_pow hm0]
      · show (max (0 : ℝ) 0) ^ m = 0
        rw [max_self, zero_pow hm0]
    have hright : HasDerivWithinAt (fun y : ℝ => (max y 0) ^ m) 0 (Set.Ici 0) 0 := by
      have h := (hasDerivAt_pow m (0 : ℝ)).hasDerivWithinAt (s := Set.Ici (0 : ℝ))
      rw [zero_pow hm1, mul_zero] at h
      refine h.congr (fun y hy => ?_) ?_
      · show (max y 0) ^ m = y ^ m
        rw [max_eq_left (Set.mem_Ici.mp hy)]
      · show (max (0 : ℝ) 0) ^ m = (0 : ℝ) ^ m
        rw [max_self]
    have hu := hleft.union hright
    rw [Set.Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · have hev : (fun y : ℝ => (max y 0) ^ m) =ᶠ[nhds x] fun y => y ^ m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      show (max y 0) ^ m = y ^ m
      rw [max_eq_left (Set.mem_Ioi.mp hy).le]
    rw [max_eq_left hx.le]
    exact (hasDerivAt_pow m x).congr_of_eventuallyEq hev

theorem hasDerivAt_tpow3 (x : ℝ) : HasDerivAt tpow3 (3 * (max x 0) ^ 2) x :=
  (hasDerivAt_maxPow (m := 3) (by norm_num) x).congr_deriv (by norm_num)

theorem hasDerivAt_three_mul_sq_max (x : ℝ) :
    HasDerivAt (fun y : ℝ => 3 * (max y 0) ^ 2) (3 * (2 * max x 0)) x :=
  ((hasDerivAt_maxPow (m := 2) le_rfl x).const_mul 3).congr_deriv (by norm_num)

/-- **The truncated cube is `C^2`.** -/
theorem contDiff_tpow3 : ContDiff ℝ 2 tpow3 := by
  have hderiv3 : deriv tpow3 = fun x => 3 * (max x 0) ^ 2 := funext fun x => (hasDerivAt_tpow3 x).deriv
  have hderiv2 : deriv (fun y : ℝ => 3 * (max y 0) ^ 2) = fun x => 3 * (2 * max x 0) :=
    funext fun x => (hasDerivAt_three_mul_sq_max x).deriv
  have h1 : ContDiff ℝ 1 (fun y : ℝ => 3 * (max y 0) ^ 2) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hasDerivAt_three_mul_sq_max x).differentiableAt, ?_⟩
    rw [hderiv2]
    exact continuous_const.mul (continuous_const.mul (continuous_id.max continuous_const))
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from one_add_one_eq_two.symm, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_tpow3 x).differentiableAt, by simp, ?_⟩
  rw [hderiv3]
  exact h1

/-! ## The B-spline -/

theorem tpow3_of_nonpos {t : ℝ} (ht : t ≤ 0) : tpow3 t = 0 := by
  show (max t 0) ^ 3 = 0
  rw [max_eq_right ht]
  norm_num

theorem tpow3_of_nonneg {t : ℝ} (ht : 0 ≤ t) : tpow3 t = t ^ 3 := by
  show (max t 0) ^ 3 = t ^ 3
  rw [max_eq_left ht]

/-- **The B-spline is `C^2`.** -/
theorem contDiff_cubicB : ContDiff ℝ 2 cubicB := by
  have h := contDiff_tpow3
  have hs : ∀ a : ℝ, ContDiff ℝ 2 (fun x : ℝ => tpow3 (x - a)) := fun a => h.comp (contDiff_id.sub contDiff_const)
  show ContDiff ℝ 2 (fun x : ℝ =>
    (tpow3 x - 4 * tpow3 (x - 1) + 6 * tpow3 (x - 2) - 4 * tpow3 (x - 3) + tpow3 (x - 4)) / 6)
  exact ((((h.sub (contDiff_const.mul (hs 1))).add (contDiff_const.mul (hs 2))).sub
    (contDiff_const.mul (hs 3))).add (hs 4)).div_const 6

/-- The B-spline vanishes at and left of its first knot. -/
theorem cubicB_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : cubicB x = 0 := by
  show (tpow3 x - 4 * tpow3 (x - 1) + 6 * tpow3 (x - 2) - 4 * tpow3 (x - 3) + tpow3 (x - 4)) / 6 = 0
  rw [tpow3_of_nonpos hx, tpow3_of_nonpos (show x - 1 ≤ 0 by linarith), tpow3_of_nonpos (show x - 2 ≤ 0 by linarith),
    tpow3_of_nonpos (show x - 3 ≤ 0 by linarith), tpow3_of_nonpos (show x - 4 ≤ 0 by linarith)]
  norm_num

/-- The B-spline vanishes at and right of its last knot: the fourth difference of a cubic is `0`. -/
theorem cubicB_eq_zero_of_ge {x : ℝ} (hx : 4 ≤ x) : cubicB x = 0 := by
  show (tpow3 x - 4 * tpow3 (x - 1) + 6 * tpow3 (x - 2) - 4 * tpow3 (x - 3) + tpow3 (x - 4)) / 6 = 0
  rw [tpow3_of_nonneg (show 0 ≤ x by linarith), tpow3_of_nonneg (show 0 ≤ x - 1 by linarith),
    tpow3_of_nonneg (show 0 ≤ x - 2 by linarith), tpow3_of_nonneg (show 0 ≤ x - 3 by linarith),
    tpow3_of_nonneg (show 0 ≤ x - 4 by linarith)]
  ring

/-! ## The spline -/

/-- **The spline is `C^2`**, for every choice of weights. -/
theorem contDiff_splineH (c : ℕ → ℝ) : ContDiff ℝ 2 (splineH c) := by
  have hj : ∀ j ∈ Finset.Icc 16 16380, ContDiff ℝ 2 (fun y : ℝ => c j * cubicB (16 * y - j)) := fun j _ =>
    contDiff_const.mul (contDiff_cubicB.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  show ContDiff ℝ 2 (fun y : ℝ => ∑ j ∈ Finset.Icc 16 16380, c j * cubicB (16 * y - j))
  exact ContDiff.sum hj

/-- **The spline is `0` where `y ≤ 1` or `1024 ≤ y`**, for every choice of weights. -/
theorem splineH_eq_zero (c : ℕ → ℝ) (y : ℝ) (hy : y ≤ 1 ∨ 1024 ≤ y) : splineH c y = 0 := by
  show ∑ j ∈ Finset.Icc 16 16380, c j * cubicB (16 * y - j) = 0
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have h16 : (16 : ℝ) ≤ j := by exact_mod_cast hj.1
  have h16380 : (j : ℝ) ≤ 16380 := by exact_mod_cast hj.2
  rcases hy with hy | hy
  · rw [cubicB_eq_zero_of_nonpos (show 16 * y - (j : ℝ) ≤ 0 by linarith), mul_zero]
  · rw [cubicB_eq_zero_of_ge (show 4 ≤ 16 * y - (j : ℝ) by linarith), mul_zero]

/-! ## The logarithmic spline -/

theorem contDiff_gWin (c : ℕ → ℝ) : ContDiff ℝ 2 (gWin c) := by
  show ContDiff ℝ 2 (fun v : ℝ => Real.exp (v / 2) * splineH c (Real.exp v))
  exact (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul ((contDiff_splineH c).comp Real.contDiff_exp)

theorem gWin_eq_zero (c : ℕ → ℝ) (v : ℝ) (hv : v ≤ 0 ∨ Real.log 1024 ≤ v) : gWin c v = 0 := by
  have hy : Real.exp v ≤ 1 ∨ 1024 ≤ Real.exp v := by
    rcases hv with hv | hv
    · left
      calc Real.exp v ≤ Real.exp 0 := Real.exp_le_exp.mpr hv
        _ = 1 := Real.exp_zero
    · right
      calc (1024 : ℝ) = Real.exp (Real.log 1024) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp v := Real.exp_le_exp.mpr hv
  show Real.exp (v / 2) * splineH c (Real.exp v) = 0
  rw [splineH_eq_zero c _ hy, mul_zero]

theorem support_gWin (c : ℕ → ℝ) : Function.support (gWin c) ⊆ Set.Icc 0 (Real.log 1024) := by
  intro v hv
  by_contra hn
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hn
  exact (Function.mem_support.mp hv) (gWin_eq_zero c v (hn.imp le_of_lt le_of_lt))

theorem hasCompactSupport_gWin (c : ℕ → ℝ) : HasCompactSupport (gWin c) := by
  show IsCompact (tsupport (gWin c))
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (support_gWin c) isClosed_Icc)

theorem support_phiC_gWin (c : ℕ → ℝ) : Function.support (B321.phiC (gWin c)) ⊆ Set.Icc 0 (Real.log 1024) := by
  intro v hv
  apply support_gWin c
  rw [Function.mem_support] at hv ⊢
  intro h0
  exact hv (by
    show ((gWin c v : ℝ) : ℂ) = 0
    rw [h0, Complex.ofReal_zero])

/-! ## The autocorrelation -/

/-- **The autocorrelation is in `classK`**, for every choice of weights. -/
theorem windowKOf_classK (c : ℕ → ℝ) : B321.classK (windowKOf c) :=
  B321.classK_of_real_even (contDiff_gWin c) (hasCompactSupport_gWin c)

theorem tsupport_windowKOf_subset (c : ℕ → ℝ) :
    tsupport (windowKOf c) ⊆ Set.Icc (-Real.log 1024) (Real.log 1024) := by
  have hts : tsupport (B321.phiC (gWin c)) ⊆ Set.Icc 0 (Real.log 1024) :=
    closure_minimal (support_phiC_gWin c) isClosed_Icc
  refine closure_minimal ?_ isClosed_Icc
  unfold windowKOf
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  have ha' := hts (subset_tsupport _ ha)
  have hb' := Zeta23.EF.support_tilde_subset _ hb
  have hb'' := hts (Set.mem_neg.mp hb')
  simp only [Set.mem_Icc] at ha' hb'' ⊢
  constructor <;> linarith [ha'.1, ha'.2, hb''.1, hb''.2]

/-- **The autocorrelation is `0` where `|u| > log 1024`**, for every choice of weights. -/
theorem windowKOf_eq_zero (c : ℕ → ℝ) (u : ℝ) (hu : Real.log 1024 < |u|) : windowKOf c u = 0 := by
  by_contra hne
  have hx := tsupport_windowKOf_subset c (subset_tsupport _ (Function.mem_support.mpr hne))
  rw [Set.mem_Icc] at hx
  have := abs_le.mpr ⟨hx.1, hx.2⟩
  linarith

end Window
end SIDEExplicitFormula
