import SIDEExplicitFormula.Window.ArchJ3

/-!
# L9b, its first part: the unit pieces of the closed forms

`gPiece l c` is the integral over `[0, 1]` of `s^l / (s + c)` and `fPiece l c` that of `s^l log (s + c)`, the two closed forms of
the archimedean term's basis (relay tools/b765_window.py :30-:32). For `c > 0`: `G_0 = log (1 + c) - log c` and
`G_(l+1) = 1 / (l + 1) - c G_l` (`gPiece_zero`, `gPiece_succ`), and by parts `F_l = (log (1 + c) - G_(l+1)) / (l + 1)`
(`fPiece_eq`); at `c = 0`, `F_(l+1) = -1 / (l + 2)^2` (`fPiece_zero_succ`). The cubic B-spline on each of its four unit pieces is a
cubic in `s` in `[0, 1]` (`cubicB_piece0` to `cubicB_piece3`), and the truncated `x^3 log x` is `x^3 log x` or `0` by the sign of
`x` (`tlog_of_nonneg`, `tlog_of_nonpos`).
-/

namespace SIDEExplicitFormula.Window

open MeasureTheory

/-- `G_l(c)`: the integral over `[0, 1]` of `s^l / (s + c)`. -/
noncomputable def gPiece (l : ℕ) (c : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, s ^ l / (s + c)

/-- `F_l(c)`: the integral over `[0, 1]` of `s^l log (s + c)`. -/
noncomputable def fPiece (l : ℕ) (c : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, s ^ l * Real.log (s + c)

theorem unit_add_ne_zero {c : ℝ} (hc : 0 < c) : ∀ s ∈ Set.uIcc (0 : ℝ) 1, s + c ≠ 0 := by
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact (by linarith [hs.1] : (0 : ℝ) < s + c).ne'

theorem continuousOn_pow_div_unit (l : ℕ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun s : ℝ => s ^ l / (s + c)) (Set.uIcc 0 1) :=
  ContinuousOn.div (f := fun s : ℝ => s ^ l) (g := fun s : ℝ => s + c)
    (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop)) (unit_add_ne_zero hc)

/-- `G_0(c) = log (1 + c) - log c`, `c > 0`. -/
theorem gPiece_zero {c : ℝ} (hc : 0 < c) : gPiece 0 c = Real.log (1 + c) - Real.log c := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => Real.log (y + c)) (s ^ 0 / (s + c)) s := by
    intro s hs
    have h := ((hasDerivAt_id' s).add_const c).log (unit_add_ne_zero hc s hs)
    refine h.congr_deriv ?_
    rw [pow_zero]
  unfold gPiece
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (continuousOn_pow_div_unit 0 hc).intervalIntegrable, zero_add]

/-- `G_(l+1)(c) = 1 / (l + 1) - c G_l(c)`, `c > 0`. -/
theorem gPiece_succ (l : ℕ) {c : ℝ} (hc : 0 < c) : gPiece (l + 1) c = 1 / ((l : ℝ) + 1) - c * gPiece l c := by
  unfold gPiece
  rw [intervalIntegral.integral_congr (g := fun s => s ^ l - c * (s ^ l / (s + c))) (fun s hs => ?_)]
  · have h0 : (0 : ℝ) ^ (l + 1) = 0 := by rw [pow_succ, mul_zero]
    rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow l)
      ((continuousOn_pow_div_unit l hc).intervalIntegrable.const_mul c),
      intervalIntegral.integral_const_mul, integral_pow, one_pow, h0, sub_zero]
  · have h := unit_add_ne_zero hc s hs
    show s ^ (l + 1) / (s + c) = s ^ l - c * (s ^ l / (s + c))
    field_simp
    ring

/-- `F_l(c) = (log (1 + c) - G_(l+1)(c)) / (l + 1)`, `c > 0`, by parts. -/
theorem fPiece_eq (l : ℕ) {c : ℝ} (hc : 0 < c) :
    fPiece l c = (Real.log (1 + c) - gPiece (l + 1) c) / ((l : ℝ) + 1) := by
  have hl : ((l : ℝ) + 1) ≠ 0 := by positivity
  have hu : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => Real.log (y + c)) (1 / (s + c)) s :=
    fun s hs => ((hasDerivAt_id' s).add_const c).log (unit_add_ne_zero hc s hs)
  have hv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => y ^ (l + 1) / ((l : ℝ) + 1)) (s ^ l) s := by
    intro s _
    refine ((hasDerivAt_pow (l + 1) s).div_const ((l : ℝ) + 1)).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    rw [mul_comm, mul_div_assoc, div_self hl, mul_one]
  have hu' : IntervalIntegrable (fun s : ℝ => 1 / (s + c)) volume 0 1 := by
    have h := (continuousOn_pow_div_unit 0 hc).intervalIntegrable (μ := volume)
    simpa only [pow_zero] using h
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' (intervalIntegral.intervalIntegrable_pow l)
  have e1 : fPiece l c = ∫ s in (0 : ℝ)..1, Real.log (s + c) * s ^ l := by
    unfold fPiece
    exact intervalIntegral.integral_congr (fun s _ => mul_comm _ _)
  have e2 : ∫ s in (0 : ℝ)..1, 1 / (s + c) * (s ^ (l + 1) / ((l : ℝ) + 1)) = gPiece (l + 1) c / ((l : ℝ) + 1) := by
    unfold gPiece
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  have h0 : (0 : ℝ) ^ (l + 1) = 0 := by rw [pow_succ, mul_zero]
  rw [e1, hp, e2, one_pow, h0, zero_div, mul_zero, sub_zero]
  ring

/-- At `c = 0`: `F_(l+1)(0)`, the integral over `[0, 1]` of `s^(l+1) log s`, is `-1 / (l + 2)^2`. -/
theorem fPiece_zero_succ (l : ℕ) : fPiece (l + 1) 0 = -1 / ((l : ℝ) + 2) ^ 2 := by
  have hl : ((l : ℝ) + 2) ≠ 0 := by positivity
  have hsub : l + 2 - 1 = l + 1 := by omega
  have hcont : ContinuousOn
      (fun s : ℝ => s ^ (l + 1) * (s * Real.log s) / ((l : ℝ) + 2) - s ^ (l + 2) / ((l : ℝ) + 2) ^ 2) (Set.Icc 0 1) :=
    ((((continuous_pow (l + 1)).mul Real.continuous_mul_log).div_const _).sub
      ((continuous_pow (l + 2)).div_const _)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => s ^ (l + 1) * (s * Real.log s) / ((l : ℝ) + 2) - s ^ (l + 2) / ((l : ℝ) + 2) ^ 2)
      (x ^ (l + 1) * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h := ((((hasDerivAt_pow (l + 1) x).mul ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0))).div_const
      ((l : ℝ) + 2)).sub ((hasDerivAt_pow (l + 2) x).div_const (((l : ℝ) + 2) ^ 2)))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Nat.add_sub_cancel, hsub]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun s : ℝ => s ^ (l + 1) * Real.log s) volume 0 1 := by
    have heq : (fun s : ℝ => s ^ (l + 1) * Real.log s) = fun s => s ^ l * (s * Real.log s) := by
      funext s
      ring
    rw [heq]
    exact ((continuous_pow l).mul Real.continuous_mul_log).intervalIntegrable 0 1
  have h0 : (0 : ℝ) ^ (l + 2) = 0 := zero_pow (by omega)
  unfold fPiece
  simp only [add_zero]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp only [Real.log_one, mul_zero, zero_mul, one_pow, zero_div, h0]
  ring

/-- The first unit piece: `B(s) = s^3 / 6` for `s` in `[0, 1]`. -/
theorem cubicB_piece0 {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : cubicB s = s ^ 3 / 6 := by
  show (tpow3 s - 4 * tpow3 (s - 1) + 6 * tpow3 (s - 2) - 4 * tpow3 (s - 3) + tpow3 (s - 4)) / 6 = s ^ 3 / 6
  rw [tpow3_of_nonneg h0, tpow3_of_nonpos (show s - 1 ≤ 0 by linarith), tpow3_of_nonpos (show s - 2 ≤ 0 by linarith),
    tpow3_of_nonpos (show s - 3 ≤ 0 by linarith), tpow3_of_nonpos (show s - 4 ≤ 0 by linarith)]
  ring

/-- The second unit piece: `B(s + 1) = (-3 s^3 + 3 s^2 + 3 s + 1) / 6` for `s` in `[0, 1]`. -/
theorem cubicB_piece1 {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    cubicB (s + 1) = (-3 * s ^ 3 + 3 * s ^ 2 + 3 * s + 1) / 6 := by
  show (tpow3 (s + 1) - 4 * tpow3 (s + 1 - 1) + 6 * tpow3 (s + 1 - 2) - 4 * tpow3 (s + 1 - 3) + tpow3 (s + 1 - 4)) / 6 = _
  rw [tpow3_of_nonneg (show 0 ≤ s + 1 by linarith), tpow3_of_nonneg (show 0 ≤ s + 1 - 1 by linarith),
    tpow3_of_nonpos (show s + 1 - 2 ≤ 0 by linarith), tpow3_of_nonpos (show s + 1 - 3 ≤ 0 by linarith),
    tpow3_of_nonpos (show s + 1 - 4 ≤ 0 by linarith)]
  ring

/-- The third unit piece: `B(s + 2) = (3 s^3 - 6 s^2 + 4) / 6` for `s` in `[0, 1]`. -/
theorem cubicB_piece2 {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : cubicB (s + 2) = (3 * s ^ 3 - 6 * s ^ 2 + 4) / 6 := by
  show (tpow3 (s + 2) - 4 * tpow3 (s + 2 - 1) + 6 * tpow3 (s + 2 - 2) - 4 * tpow3 (s + 2 - 3) + tpow3 (s + 2 - 4)) / 6 = _
  rw [tpow3_of_nonneg (show 0 ≤ s + 2 by linarith), tpow3_of_nonneg (show 0 ≤ s + 2 - 1 by linarith),
    tpow3_of_nonneg (show 0 ≤ s + 2 - 2 by linarith), tpow3_of_nonpos (show s + 2 - 3 ≤ 0 by linarith),
    tpow3_of_nonpos (show s + 2 - 4 ≤ 0 by linarith)]
  ring

/-- The fourth unit piece: `B(s + 3) = (1 - s)^3 / 6` for `s` in `[0, 1]`. -/
theorem cubicB_piece3 {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : cubicB (s + 3) = (1 - s) ^ 3 / 6 := by
  show (tpow3 (s + 3) - 4 * tpow3 (s + 3 - 1) + 6 * tpow3 (s + 3 - 2) - 4 * tpow3 (s + 3 - 3) + tpow3 (s + 3 - 4)) / 6 = _
  rw [tpow3_of_nonneg (show 0 ≤ s + 3 by linarith), tpow3_of_nonneg (show 0 ≤ s + 3 - 1 by linarith),
    tpow3_of_nonneg (show 0 ≤ s + 3 - 2 by linarith), tpow3_of_nonneg (show 0 ≤ s + 3 - 3 by linarith),
    tpow3_of_nonpos (show s + 3 - 4 ≤ 0 by linarith)]
  ring

/-- The truncated `x^3 log x` at `x ≥ 0`. -/
theorem tlog_of_nonneg {x : ℝ} (hx : 0 ≤ x) : tlog x = x ^ 3 * Real.log x := by
  unfold tlog
  rw [tpow3_of_nonneg hx]

/-- The truncated `x^3 log x` at `x ≤ 0`. -/
theorem tlog_of_nonpos {x : ℝ} (hx : x ≤ 0) : tlog x = 0 := by
  unfold tlog
  rw [tpow3_of_nonpos hx, zero_mul]

end SIDEExplicitFormula.Window
