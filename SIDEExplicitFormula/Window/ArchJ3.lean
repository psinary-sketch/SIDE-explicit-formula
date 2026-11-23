import SIDEExplicitFormula.Window.ArchJ2

/-!
# The inner integral at the window in closed form

b767, (R377)(4)(b), L9's remainder, its part b begun. For a truncated cube with its knot at `m ≥ 0` and `u > 0`,
`∫_0^u (tpow3 (16 u - m) - tpow3 (16 w - m)) / (u - w) dw = tpow3 (16 u - m) (log (16 u) - log (16 u - m) + 11/6)`:
where `16 w < m` the cube is off and the quotient integrates to a logarithm; beyond, the quotient of the difference of two cubes is a
quadratic in `w`, integrating to `(11/6) (16 u - m)^3`. The window's `H` is a sum of such cubes (`cubicB_eq_sum`), so for `u > 0`
`∫_0^u (H u - H w) / (u - w) dw = H u (log (16 u) + 11/6) - ∑_j c_j ℓ (16 u - j)`, `ℓ` the fourth difference of `tpow3 v log v` over 6,
and Gauss's integral at the window is `(11/6) K(1) + ∫ H² log (16 u) - (1/16) ∑_i ∑_j c_i c_j λ(i - j)`,
`λ(d) = ∫ B(x) ℓ(x + d) dx`.
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- `tpow3 x * log x`, continuous: `0` where `x ≤ 0`. -/
def tlog (x : ℝ) : ℝ := tpow3 x * Real.log x

theorem tlog_eq (x : ℝ) : tlog x = (max x 0) ^ 2 * (max x 0 * Real.log (max x 0)) := by
  unfold tlog tpow3
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx]
    simp
  · rw [max_eq_left hx]
    ring

theorem continuous_tlog : Continuous tlog := by
  have h : tlog = fun x : ℝ => (max x 0) ^ 2 * (max x 0 * Real.log (max x 0)) := funext tlog_eq
  rw [h]
  have hm : Continuous (fun x : ℝ => max x 0) := continuous_id.max continuous_const
  exact (hm.pow 2).mul (Real.continuous_mul_log.comp hm)

/-- `ℓ(v)`: the fourth difference of `tpow3 v log v`, over 6. -/
def ellLog (v : ℝ) : ℝ := (∑ k ∈ Finset.range 5, (bw k : ℝ) * tlog (v - k)) / 6

theorem continuous_ellLog : Continuous ellLog := by
  unfold ellLog
  exact (continuous_finset_sum _ (fun k _ =>
    continuous_const.mul (continuous_tlog.comp (continuous_id.sub continuous_const)))).div_const 6

/-- The quotient of two cubes where both are on, away from `w = u`. -/
theorem tpow3_quot_eq {m u w : ℝ} (hw0 : m < 16 * w) (hwu : w < u) :
    (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w) =
      16 * ((16 * u - m) ^ 2 + (16 * u - m) * (16 * w - m) + (16 * w - m) ^ 2) := by
  have h1 : 0 ≤ 16 * u - m := by linarith
  have h2 : 0 ≤ 16 * w - m := by linarith
  have hne : u - w ≠ 0 := (sub_pos.mpr hwu).ne'
  rw [tpow3_of_nonneg h1, tpow3_of_nonneg h2, div_eq_iff hne]
  ring

theorem hasDerivAt_quotG (X m w : ℝ) :
    HasDerivAt (fun w : ℝ => X ^ 2 * (16 * w - m) + X * (16 * w - m) ^ 2 / 2 + (16 * w - m) ^ 3 / 3)
      (16 * (X ^ 2 + X * (16 * w - m) + (16 * w - m) ^ 2)) w := by
  have hY : HasDerivAt (fun w : ℝ => 16 * w - m) (16 * 1) w := ((hasDerivAt_id' w).const_mul 16).sub_const m
  have h := ((hY.const_mul (X ^ 2)).add (((hY.pow 2).const_mul X).div_const 2)).add ((hY.pow 3).div_const 3)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- **One truncated cube's inner integral**: for `m ≥ 0`, `u > 0`, the quotient is interval integrable on `[0, u]` and
`∫_0^u (tpow3 (16 u - m) - tpow3 (16 w - m)) / (u - w) dw = tpow3 (16 u - m) (log (16 u) - log (16 u - m) + 11/6)`. -/
theorem inner_tpow3 {m u : ℝ} (hm : 0 ≤ m) (hu : 0 < u) :
    IntervalIntegrable (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)) volume 0 u ∧
    ∫ w in (0 : ℝ)..u, (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w) =
      tpow3 (16 * u - m) * (Real.log (16 * u) - Real.log (16 * u - m) + 11 / 6) := by
  rcases le_or_lt (16 * u) m with hmu | hmu
  · have hz : Set.EqOn (fun _ : ℝ => (0 : ℝ)) (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w))
        (Set.uIcc 0 u) := by
      intro w hw
      rw [Set.uIcc_of_le hu.le] at hw
      show (0 : ℝ) = (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)
      rw [tpow3_of_nonpos (by linarith : 16 * u - m ≤ 0), tpow3_of_nonpos (by linarith [hw.2] : 16 * w - m ≤ 0),
        sub_zero, zero_div]
    refine ⟨(intervalIntegrable_congr (hz.mono Set.uIoc_subset_uIcc)).mp intervalIntegrable_const, ?_⟩
    rw [← intervalIntegral.integral_congr hz, intervalIntegral.integral_zero,
      tpow3_of_nonpos (by linarith : 16 * u - m ≤ 0), zero_mul]
  · have hX : 0 < 16 * u - m := by linarith
    have hw00 : (0 : ℝ) ≤ m / 16 := div_nonneg hm (by norm_num)
    have hw0u : m / 16 < u := by linarith
    -- where the cube is off, `[0, m / 16]`
    have hp1 : Set.EqOn (fun w : ℝ => (16 * u - m) ^ 3 / (u - w))
        (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)) (Set.uIcc 0 (m / 16)) := by
      intro w hw
      rw [Set.uIcc_of_le hw00] at hw
      have hw' : 16 * w - m ≤ 0 := by linarith [hw.2]
      show (16 * u - m) ^ 3 / (u - w) = (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)
      rw [tpow3_of_nonpos hw', tpow3_of_nonneg hX.le, sub_zero]
    have hne1 : ∀ w ∈ Set.uIcc 0 (m / 16), u - w ≠ 0 := by
      intro w hw
      rw [Set.uIcc_of_le hw00] at hw
      exact (by linarith [hw.2] : (0 : ℝ) < u - w).ne'
    have hc1 : ContinuousOn (fun w : ℝ => (16 * u - m) ^ 3 / (u - w)) (Set.uIcc 0 (m / 16)) :=
      ContinuousOn.div (f := fun _ : ℝ => (16 * u - m) ^ 3) (g := fun w : ℝ => u - w) continuousOn_const
        (Continuous.continuousOn (by fun_prop)) hne1
    have hd1 : ∀ w ∈ Set.uIcc 0 (m / 16),
        HasDerivAt (fun w : ℝ => -((16 * u - m) ^ 3 * Real.log (16 * u - 16 * w))) ((16 * u - m) ^ 3 / (u - w)) w := by
      intro w hw
      have hne := hne1 w hw
      rw [Set.uIcc_of_le hw00] at hw
      have hpos : 16 * u - 16 * w ≠ 0 := (by linarith [hw.2] : (0 : ℝ) < 16 * u - 16 * w).ne'
      have hL : HasDerivAt (fun w : ℝ => 16 * u - 16 * w) (-(16 * 1)) w :=
        ((hasDerivAt_id' w).const_mul 16).const_sub (16 * u)
      have h := ((hL.log hpos).const_mul ((16 * u - m) ^ 3)).neg
      refine h.congr_deriv ?_
      have h16 : 16 * u - 16 * w = 16 * (u - w) := by ring
      rw [h16]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have hi1 : ∫ w in (0 : ℝ)..(m / 16), (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w) =
        (16 * u - m) ^ 3 * (Real.log (16 * u) - Real.log (16 * u - m)) := by
      rw [← intervalIntegral.integral_congr hp1, intervalIntegral.integral_eq_sub_of_hasDerivAt hd1 hc1.intervalIntegrable]
      have h16 : (16 : ℝ) * u - 16 * (m / 16) = 16 * u - m := by ring
      simp only [mul_zero, sub_zero, h16]
      ring
    have hI1 : IntervalIntegrable (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)) volume 0 (m / 16) :=
      (intervalIntegrable_congr (hp1.mono Set.uIoc_subset_uIcc)).mp hc1.intervalIntegrable
    -- where the cube is on, `[m / 16, u]`
    have hp2 : Set.EqOn (fun w : ℝ => 16 * ((16 * u - m) ^ 2 + (16 * u - m) * (16 * w - m) + (16 * w - m) ^ 2))
        (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)) (Set.uIoo (m / 16) u) := by
      intro w hw
      rw [Set.uIoo_of_le hw0u.le] at hw
      exact (tpow3_quot_eq (by linarith [hw.1]) hw.2).symm
    have hc2 : Continuous (fun w : ℝ => 16 * ((16 * u - m) ^ 2 + (16 * u - m) * (16 * w - m) + (16 * w - m) ^ 2)) := by
      fun_prop
    have hI2 : IntervalIntegrable (fun w : ℝ => (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w)) volume (m / 16) u :=
      (hc2.intervalIntegrable (m / 16) u).congr_uIoo hp2
    have hi2 : ∫ w in (m / 16)..u, (tpow3 (16 * u - m) - tpow3 (16 * w - m)) / (u - w) = 11 / 6 * (16 * u - m) ^ 3 := by
      rw [← intervalIntegral.integral_congr_uIoo hp2,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hasDerivAt_quotG (16 * u - m) m w)
          (hc2.intervalIntegrable (m / 16) u)]
      show (16 * u - m) ^ 2 * (16 * u - m) + (16 * u - m) * (16 * u - m) ^ 2 / 2 + (16 * u - m) ^ 3 / 3 -
          ((16 * u - m) ^ 2 * (16 * (m / 16) - m) + (16 * u - m) * (16 * (m / 16) - m) ^ 2 / 2 +
            (16 * (m / 16) - m) ^ 3 / 3) = 11 / 6 * (16 * u - m) ^ 3
      ring
    refine ⟨hI1.trans hI2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hi1, hi2, tpow3_of_nonneg hX.le]
    ring

/-- The window's `H` as a sum of truncated cubes. -/
theorem windowH_eq_sum (y : ℝ) : windowH y = ∑ j ∈ Finset.Icc 16 16380, ∑ k ∈ Finset.range 5,
    coeff j * ((bw k : ℝ) / 6) * tpow3 (16 * y - ((j : ℝ) + k)) := by
  unfold windowH splineH
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cubicB_eq_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sub_sub]
  ring

theorem inner_sum_eq (u : ℝ) :
    ∑ j ∈ Finset.Icc 16 16380, ∑ k ∈ Finset.range 5, coeff j * ((bw k : ℝ) / 6) *
      (tpow3 (16 * u - ((j : ℝ) + k)) * (Real.log (16 * u) - Real.log (16 * u - ((j : ℝ) + k)) + 11 / 6)) =
    windowH u * (Real.log (16 * u) + 11 / 6) - ∑ j ∈ Finset.Icc 16 16380, coeff j * ellLog (16 * u - j) := by
  rw [windowH_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold ellLog tlog
  rw [Finset.sum_mul, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [sub_sub]
  ring

/-- **The inner integral at the window**: for `u > 0`,
`∫_0^u (H u - H w) / (u - w) dw = H u (log (16 u) + 11/6) - ∑_j c_j ℓ (16 u - j)`. -/
theorem windowH_inner {u : ℝ} (hu : 0 < u) :
    ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w) =
      windowH u * (Real.log (16 * u) + 11 / 6) - ∑ j ∈ Finset.Icc 16 16380, coeff j * ellLog (16 * u - j) := by
  have hm : ∀ j k : ℕ, (0 : ℝ) ≤ (j : ℝ) + k := fun j k => by positivity
  have hexp : ∀ w : ℝ, (windowH u - windowH w) / (u - w) = ∑ j ∈ Finset.Icc 16 16380, ∑ k ∈ Finset.range 5,
      coeff j * ((bw k : ℝ) / 6) * ((tpow3 (16 * u - ((j : ℝ) + k)) - tpow3 (16 * w - ((j : ℝ) + k))) / (u - w)) := by
    intro w
    rw [windowH_eq_sum u, windowH_eq_sum w, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hint : ∀ j k : ℕ, IntervalIntegrable (fun w : ℝ => coeff j * ((bw k : ℝ) / 6) *
      ((tpow3 (16 * u - ((j : ℝ) + k)) - tpow3 (16 * w - ((j : ℝ) + k))) / (u - w))) volume 0 u :=
    fun j k => (inner_tpow3 (hm j k) hu).1.const_mul _
  have hsum : ∀ j : ℕ, IntervalIntegrable (fun w : ℝ => ∑ k ∈ Finset.range 5, coeff j * ((bw k : ℝ) / 6) *
      ((tpow3 (16 * u - ((j : ℝ) + k)) - tpow3 (16 * w - ((j : ℝ) + k))) / (u - w))) volume 0 u := by
    intro j
    have h := IntervalIntegrable.sum (Finset.range 5) (fun k _ => hint j k)
    convert h using 1
    funext w
    simp only [Finset.sum_apply]
  have hterm : ∀ j k : ℕ, ∫ w in (0 : ℝ)..u, coeff j * ((bw k : ℝ) / 6) *
      ((tpow3 (16 * u - ((j : ℝ) + k)) - tpow3 (16 * w - ((j : ℝ) + k))) / (u - w)) =
      coeff j * ((bw k : ℝ) / 6) *
        (tpow3 (16 * u - ((j : ℝ) + k)) * (Real.log (16 * u) - Real.log (16 * u - ((j : ℝ) + k)) + 11 / 6)) := by
    intro j k
    rw [intervalIntegral.integral_const_mul, (inner_tpow3 (hm j k) hu).2]
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hsum j), ← inner_sum_eq u]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun k _ => hint j k)]
  exact Finset.sum_congr rfl (fun k _ => hterm j k)

/-- `λ(d) = ∫ B(x) ℓ(x + d) dx`. -/
def lamI (d : ℝ) : ℝ := ∫ x, cubicB x * ellLog (x + d)

/-- One term of the far part: `∫ B(16 u - i) ℓ(16 u - j) du = λ(i - j) / 16`. -/
theorem integral_cubicB_affine_ellLog (i j : ℕ) :
    ∫ u, cubicB (16 * u - i) * ellLog (16 * u - j) = 1 / 16 * lamI ((i : ℝ) - j) := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => cubicB (x - i) * ellLog (x - j)) 16
  have h16 : |(16 : ℝ)⁻¹| = 1 / 16 := by norm_num
  rw [h16, smul_eq_mul] at h
  have ht := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cubicB (x - i) * ellLog (x - j)) (i : ℝ)
  simp only [add_sub_cancel_right] at ht
  rw [h, ← ht]
  unfold lamI
  simp only [add_sub_assoc]

theorem integrableOn_windowH_ellLog (j : ℕ) :
    IntegrableOn (fun u : ℝ => windowH u * ellLog (16 * u - j)) (Set.Ioi 1) := by
  have hc := windowH_continuous
  have he := continuous_ellLog
  exact integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, zero_mul]) _

/-- The far part's `j`-th term over the whole spline: `∫_{u > 1} H(u) ℓ(16 u - j) du = (1/16) ∑_i c_i λ(i - j)`. -/
theorem integral_windowH_ellLog (j : ℕ) :
    ∫ u in Set.Ioi (1 : ℝ), windowH u * ellLog (16 * u - j) =
      1 / 16 * ∑ i ∈ Finset.Icc 16 16380, coeff i * lamI ((i : ℝ) - j) := by
  have hB := continuous_cubicB
  have he := continuous_ellLog
  have hfull : ∫ u in Set.Ioi (1 : ℝ), windowH u * ellLog (16 * u - j) = ∫ u, windowH u * ellLog (16 * u - j) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hu' : u ≤ 1 := not_lt.mp (fun h => hu (Set.mem_Ioi.mpr h))
    rw [windowH_eq_zero_le hu', zero_mul]
  have hint : ∀ i : ℕ, Integrable (fun u : ℝ => coeff i * (cubicB (16 * u - i) * ellLog (16 * u - j))) := by
    intro i
    have hc : Continuous (fun u : ℝ => coeff i * (cubicB (16 * u - i) * ellLog (16 * u - j))) := by fun_prop
    have hsupp : Function.support (fun u : ℝ => coeff i * (cubicB (16 * u - i) * ellLog (16 * u - j))) ⊆
        Function.support (fun y : ℝ => cubicB (16 * y - i)) := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0, zero_mul, mul_zero])
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_cubicB_affine (a := 16) (by norm_num) (i : ℝ)).mono hsupp)
  rw [hfull]
  have hsplit : ∀ u : ℝ, windowH u * ellLog (16 * u - j) =
      ∑ i ∈ Finset.Icc 16 16380, coeff i * (cubicB (16 * u - i) * ellLog (16 * u - j)) := by
    intro u
    unfold windowH splineH
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp only [hsplit]
  rw [integral_finsetSum _ (fun i _ => hint i), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, integral_cubicB_affine_ellLog]
  ring

/-- **L9b, Gauss's integral at the window split**: the double integral of `archJ_eq_double` is
`(11/6) K(1) + ∫_{u > 1} H² log (16 u) - (1/16) ∑_j ∑_i c_j c_i λ(i - j)`. -/
theorem archJ_double_split :
    (∫ u in Set.Ioi (1 : ℝ), windowH u * ∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w)) =
      11 / 6 * windowKx 1 + (∫ u in Set.Ioi (1 : ℝ), windowH u * windowH u * Real.log (16 * u)) -
        1 / 16 * ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i * lamI ((i : ℝ) - j) := by
  have hc := windowH_continuous
  have he := continuous_ellLog
  have h1 : ∀ u ∈ Set.Ioi (1 : ℝ), windowH u * (∫ w in (0 : ℝ)..u, (windowH u - windowH w) / (u - w)) =
      (11 / 6 * (windowH u * windowH u) + windowH u * windowH u * Real.log (16 * u)) -
        ∑ j ∈ Finset.Icc 16 16380, coeff j * (windowH u * ellLog (16 * u - j)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (Set.mem_Ioi.mp hu)
    rw [windowH_inner hu0]
    have hS : ∑ j ∈ Finset.Icc 16 16380, coeff j * (windowH u * ellLog (16 * u - j)) =
        windowH u * ∑ j ∈ Finset.Icc 16 16380, coeff j * ellLog (16 * u - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hS]
    ring
  have hA : IntegrableOn (fun u : ℝ => 11 / 6 * (windowH u * windowH u)) (Set.Ioi 1) :=
    integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, mul_zero]) _
  have hlog : Continuous (fun u : ℝ => Real.log (16 * max u 1)) :=
    (continuous_const.mul (continuous_id.max continuous_const)).log
      (fun x => (mul_pos (by norm_num : (0 : ℝ) < 16) (lt_of_lt_of_le zero_lt_one (le_max_right x 1))).ne')
  have hBg : IntegrableOn (fun u : ℝ => windowH u * windowH u * Real.log (16 * max u 1)) (Set.Ioi 1) :=
    integrableOn_of_windowH ((hc.mul hc).mul hlog) (fun y hy => by simp only [hy, zero_mul]) _
  have hB : IntegrableOn (fun u : ℝ => windowH u * windowH u * Real.log (16 * u)) (Set.Ioi 1) := by
    refine hBg.congr_fun (fun u hu => ?_) measurableSet_Ioi
    show windowH u * windowH u * Real.log (16 * max u 1) = windowH u * windowH u * Real.log (16 * u)
    rw [max_eq_left (Set.mem_Ioi.mp hu).le]
  have hCj : ∀ j : ℕ, IntegrableOn (fun u : ℝ => coeff j * (windowH u * ellLog (16 * u - j))) (Set.Ioi 1) :=
    fun j => integrableOn_of_windowH (by fun_prop) (fun y hy => by simp only [hy, zero_mul, mul_zero]) _
  have hC : IntegrableOn (fun u : ℝ => ∑ j ∈ Finset.Icc 16 16380, coeff j * (windowH u * ellLog (16 * u - j)))
      (Set.Ioi 1) :=
    integrableOn_of_windowH (continuous_finset_sum _ (fun j _ => by fun_prop))
      (fun y hy => by simp only [hy, zero_mul, mul_zero, Finset.sum_const_zero]) _
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_sub (Integrable.add hA hB) hC, integral_add hA hB,
    integral_finsetSum _ (fun j _ => hCj j), integral_const_mul, ← windowKx_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_windowH_ellLog]
  ring

/-- **L9b, Gauss's integral at the window in the spline's terms**:
`∫ t > 0, (e ^ (-t) k (0) - e ^ (-t / 2) k (t)) / (1 - e ^ (-t)) =
(11/6) K(1) + ∫_{u > 1} H² log (16 u) - (1/16) ∑_j ∑_i c_j c_i λ(i - j)`. -/
theorem archJ_eq_split :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((11 / 6 * windowKx 1 + (∫ u in Set.Ioi (1 : ℝ), windowH u * windowH u * Real.log (16 * u)) -
        1 / 16 * ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i * lamI ((i : ℝ) - j) : ℝ) : ℂ) := by
  rw [archJ_eq_double, archJ_double_split]

end Window
end SIDEExplicitFormula
