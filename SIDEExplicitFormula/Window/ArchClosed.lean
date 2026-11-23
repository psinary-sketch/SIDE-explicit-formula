import SIDEExplicitFormula.Window.ArchBand

/-!
# L9b, its third part: the band's integrals in closed form

`gPiece l c` in closed form by its recurrence (`gPiece_closed`), and with it `fPiece l c` (`fPiece_closed`): each a
rational function of `c` beside `log (1 + c)` and `log c`. `Lg(a, d)` for `d = 0, 1, 2, 3` is a sum over the unit
intervals on which both splines live (`lgI_eq_units`); on each, the product of the two cubic pieces is a polynomial of
degree 6, its coefficients the vectors `bandV k d`, so `Lg(a, d)` is a rational combination of the `fPiece l (k + a)`
(`lgI_closed_zero` to `lgI_closed_three`); and `Lg(a, -d) = Lg(a + d, d)` (`lgI_neg`), which gives the band's other half.
-/

namespace SIDEExplicitFormula.Window

open MeasureTheory

/-- `gPiece l c` in closed form, by its recurrence from `gPiece 0 c = log (1 + c) - log c`. -/
theorem gPiece_closed {c : ℝ} (hc : 0 < c) (l : ℕ) :
    gPiece l c = ∑ m ∈ Finset.range l, (-c) ^ m / ((l : ℝ) - m) +
      (-c) ^ l * (Real.log (1 + c) - Real.log c) := by
  induction l with
  | zero =>
    rw [gPiece_zero hc]
    simp
  | succ l ih =>
    rw [gPiece_succ l hc, ih, Finset.sum_range_succ']
    have hs : ∀ m ∈ Finset.range l, (-c) ^ (m + 1) / (((l + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) =
        -c * ((-c) ^ m / ((l : ℝ) - m)) := by
      intro m _
      rw [show (((l + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) = (l : ℝ) - m by push_cast; ring, pow_succ]
      ring
    rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, pow_zero, pow_succ]
    ring

/-- `fPiece l c` in closed form: `fPiece_eq` with `gPiece_closed`. -/
theorem fPiece_closed (l : ℕ) {c : ℝ} (hc : 0 < c) :
    fPiece l c = (Real.log (1 + c) - (∑ m ∈ Finset.range (l + 1), (-c) ^ m / (((l + 1 : ℕ) : ℝ) - m) +
      (-c) ^ (l + 1) * (Real.log (1 + c) - Real.log c))) / ((l : ℝ) + 1) := by
  rw [fPiece_eq l hc, gPiece_closed hc]

/-- `pieceP m s`: the cubic B-spline on `[m, m + 1]`, read at `m + s`. -/
noncomputable def pieceP : ℕ → ℝ → ℝ
  | 0, s => s ^ 3 / 6
  | 1, s => (-3 * s ^ 3 + 3 * s ^ 2 + 3 * s + 1) / 6
  | 2, s => (3 * s ^ 3 - 6 * s ^ 2 + 4) / 6
  | 3, s => (1 - s) ^ 3 / 6
  | _, _ => 0

/-- The spline at `m + s`, `0 ≤ s ≤ 1`, is its piece `pieceP m s`. -/
theorem cubicB_add_nat {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (m : ℕ) (hm : m ≤ 3) :
    cubicB (s + m) = pieceP m s := by
  interval_cases m
  · simp only [Nat.cast_zero, add_zero, pieceP]
    exact cubicB_piece0 h0 h1
  · simp only [Nat.cast_one, pieceP]
    exact cubicB_piece1 h0 h1
  · simp only [Nat.cast_ofNat, pieceP]
    exact cubicB_piece2 h0 h1
  · simp only [Nat.cast_ofNat, pieceP]
    exact cubicB_piece3 h0 h1

/-- `lgF a d v`, the integrand of `Lg(a, d)`. -/
noncomputable def lgF (a d v : ℝ) : ℝ := cubicB v * cubicB (v + d) * Real.log (v + a)

/-- `bandF a k d s`, the integrand of `Lg(a, d)` on the unit interval `[k, k + 1]`, read at `k + s`. -/
noncomputable def bandF (a : ℝ) (k d : ℕ) (s : ℝ) : ℝ := lgF a d (s + k)

/-- `Lg(a, d)` for `d ≤ 3` as the sum of its integrals over the unit intervals `[k, k + 1]`, `k < 4 - d`. -/
theorem lgI_eq_units {a : ℝ} (ha : 0 < a) (d : ℕ) (hd : d ≤ 3) :
    lgI a d = ∑ k ∈ Finset.range (4 - d), ∫ s in (0 : ℝ)..1, bandF a k d s := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd
  have h4 : ((4 - d : ℕ) : ℝ) = 4 - d := by
    rw [Nat.cast_sub (show d ≤ 4 by omega)]
    norm_num
  have h0le : (0 : ℝ) ≤ 4 - d := by linarith
  have hcont : ∀ k : ℕ, IntervalIntegrable (lgF a d) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k
    apply ContinuousOn.intervalIntegrable
    have hB := continuous_cubicB
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hpos : ∀ x ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), x + a ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact (by linarith [hx.1] : (0 : ℝ) < x + a).ne'
    show ContinuousOn (fun v : ℝ => cubicB v * cubicB (v + d) * Real.log (v + a)) _
    exact (Continuous.continuousOn (by fun_prop) :
      ContinuousOn (fun v : ℝ => cubicB v * cubicB (v + d)) _).mul
      (ContinuousOn.log (Continuous.continuousOn (by fun_prop)) hpos)
  have hzero : ∀ v, v ∉ Set.Ioc (0 : ℝ) (4 - d) → lgF a d v = 0 := by
    intro v hv
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    show cubicB v * cubicB (v + d) * Real.log (v + a) = 0
    rcases hv with hv | hv
    · rw [cubicB_eq_zero_of_nonpos hv, zero_mul, zero_mul]
    · rw [cubicB_eq_zero_of_ge (by linarith : (4 : ℝ) ≤ v + d), mul_zero, zero_mul]
  have hfull : lgI a d = ∫ v in ((0 : ℕ) : ℝ)..((4 - d : ℕ) : ℝ), lgF a d v := by
    rw [Nat.cast_zero, h4, intervalIntegral.integral_of_le h0le,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    rfl
  rw [hfull, ← intervalIntegral.sum_integral_adjacent_intervals (a := (Nat.cast : ℕ → ℝ))
    (fun k _ => hcont k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have key := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1) (lgF a d) (k : ℝ)
  rw [zero_add, add_comm (1 : ℝ) (k : ℝ)] at key
  rw [Nat.cast_add, Nat.cast_one, ← key]
  rfl

/-- A polynomial against `log (s + c)` on `[0, 1]`, `c > 0`: its coefficients against the `fPiece l c`. -/
theorem integral_poly_log {c : ℝ} (hc : 0 < c) {n : ℕ} (p : Fin n → ℝ) :
    ∫ s in (0 : ℝ)..1, (∑ l : Fin n, p l * s ^ (l : ℕ)) * Real.log (s + c) =
      ∑ l : Fin n, p l * fPiece l c := by
  have hI : ∀ l ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun s : ℝ => p l * s ^ (l : ℕ) * Real.log (s + c)) volume 0 1 := by
    intro l _
    apply ContinuousOn.intervalIntegrable
    exact (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun s : ℝ => p l * s ^ (l : ℕ)) _).mul
      (ContinuousOn.log (Continuous.continuousOn (by fun_prop)) (unit_add_ne_zero hc))
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hI]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- One unit interval of the band: where `pieceP k * pieceP (k + d)` has the coefficients `v`, the integral over
`[k, k + 1]` is `∑_l v_l fPiece l (k + a)`. -/
theorem band_unit {a : ℝ} (ha : 0 < a) (k d : ℕ) (hkd : k + d ≤ 3) (v : Fin 7 → ℝ)
    (hv : ∀ s : ℝ, pieceP k s * pieceP (k + d) s = ∑ l : Fin 7, v l * s ^ (l : ℕ)) :
    ∫ s in (0 : ℝ)..1, bandF a k d s = ∑ l : Fin 7, v l * fPiece l ((k : ℝ) + a) := by
  have hc : 0 < (k : ℝ) + a := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [intervalIntegral.integral_congr
    (g := fun s : ℝ => (∑ l : Fin 7, v l * s ^ (l : ℕ)) * Real.log (s + ((k : ℝ) + a))) (fun s hs => ?_)]
  · exact integral_poly_log hc v
  · rw [Set.uIcc_of_le zero_le_one] at hs
    obtain ⟨h0, h1⟩ := hs
    show cubicB (s + k) * cubicB (s + k + d) * Real.log (s + k + a) =
      (∑ l : Fin 7, v l * s ^ (l : ℕ)) * Real.log (s + ((k : ℝ) + a))
    rw [← hv s, cubicB_add_nat h0 h1 k (by omega), add_assoc s (k : ℝ) (d : ℝ), ← Nat.cast_add,
      cubicB_add_nat h0 h1 (k + d) hkd, add_assoc s (k : ℝ) a]

/-- The coefficients of `pieceP k * pieceP (k + d)`, `bandV k d`, each `s^0` to `s^6`. -/
noncomputable def bandV00 : Fin 7 → ℝ := ![0, 0, 0, 0, 0, 0, 1 / 36]
noncomputable def bandV10 : Fin 7 → ℝ := ![1 / 36, 1 / 6, 5 / 12, 1 / 3, -1 / 4, -1 / 2, 1 / 4]
noncomputable def bandV20 : Fin 7 → ℝ := ![4 / 9, 0, -4 / 3, 2 / 3, 1, -1, 1 / 4]
noncomputable def bandV30 : Fin 7 → ℝ := ![1 / 36, -1 / 6, 5 / 12, -5 / 9, 5 / 12, -1 / 6, 1 / 36]
noncomputable def bandV01 : Fin 7 → ℝ := ![0, 0, 0, 1 / 36, 1 / 12, 1 / 12, -1 / 12]
noncomputable def bandV11 : Fin 7 → ℝ := ![1 / 9, 1 / 3, 1 / 6, -3 / 4, -1 / 4, 3 / 4, -1 / 4]
noncomputable def bandV21 : Fin 7 → ℝ := ![1 / 9, -1 / 3, 1 / 6, 17 / 36, -3 / 4, 5 / 12, -1 / 12]
noncomputable def bandV02 : Fin 7 → ℝ := ![0, 0, 0, 1 / 9, 0, -1 / 6, 1 / 12]
noncomputable def bandV12 : Fin 7 → ℝ := ![1 / 36, 0, -1 / 12, -1 / 9, 5 / 12, -1 / 3, 1 / 12]
noncomputable def bandV03 : Fin 7 → ℝ := ![0, 0, 0, 1 / 36, -1 / 12, 1 / 12, -1 / 36]

theorem bandV00_spec (s : ℝ) : pieceP 0 s * pieceP 0 s = ∑ l : Fin 7, bandV00 l * s ^ (l : ℕ) := by
  simp only [bandV00, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV10_spec (s : ℝ) : pieceP 1 s * pieceP 1 s = ∑ l : Fin 7, bandV10 l * s ^ (l : ℕ) := by
  simp only [bandV10, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV20_spec (s : ℝ) : pieceP 2 s * pieceP 2 s = ∑ l : Fin 7, bandV20 l * s ^ (l : ℕ) := by
  simp only [bandV20, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV30_spec (s : ℝ) : pieceP 3 s * pieceP 3 s = ∑ l : Fin 7, bandV30 l * s ^ (l : ℕ) := by
  simp only [bandV30, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV01_spec (s : ℝ) : pieceP 0 s * pieceP 1 s = ∑ l : Fin 7, bandV01 l * s ^ (l : ℕ) := by
  simp only [bandV01, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV11_spec (s : ℝ) : pieceP 1 s * pieceP 2 s = ∑ l : Fin 7, bandV11 l * s ^ (l : ℕ) := by
  simp only [bandV11, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV21_spec (s : ℝ) : pieceP 2 s * pieceP 3 s = ∑ l : Fin 7, bandV21 l * s ^ (l : ℕ) := by
  simp only [bandV21, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV02_spec (s : ℝ) : pieceP 0 s * pieceP 2 s = ∑ l : Fin 7, bandV02 l * s ^ (l : ℕ) := by
  simp only [bandV02, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV12_spec (s : ℝ) : pieceP 1 s * pieceP 3 s = ∑ l : Fin 7, bandV12 l * s ^ (l : ℕ) := by
  simp only [bandV12, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

theorem bandV03_spec (s : ℝ) : pieceP 0 s * pieceP 3 s = ∑ l : Fin 7, bandV03 l * s ^ (l : ℕ) := by
  simp only [bandV03, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  ring

/-- **`Lg(a, 0)` in closed form**, `a > 0`. -/
theorem lgI_closed_zero {a : ℝ} (ha : 0 < a) :
    lgI a 0 = (∑ l : Fin 7, bandV00 l * fPiece l a) + (∑ l : Fin 7, bandV10 l * fPiece l (1 + a)) +
      (∑ l : Fin 7, bandV20 l * fPiece l (2 + a)) + ∑ l : Fin 7, bandV30 l * fPiece l (3 + a) := by
  have h := lgI_eq_units ha 0 (by norm_num)
  rw [Nat.cast_zero] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [band_unit ha 0 0 (by norm_num) bandV00 bandV00_spec, band_unit ha 1 0 (by norm_num) bandV10 bandV10_spec,
    band_unit ha 2 0 (by norm_num) bandV20 bandV20_spec, band_unit ha 3 0 (by norm_num) bandV30 bandV30_spec]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add]

/-- **`Lg(a, 1)` in closed form**, `a > 0`. -/
theorem lgI_closed_one {a : ℝ} (ha : 0 < a) :
    lgI a 1 = (∑ l : Fin 7, bandV01 l * fPiece l a) + (∑ l : Fin 7, bandV11 l * fPiece l (1 + a)) +
      ∑ l : Fin 7, bandV21 l * fPiece l (2 + a) := by
  have h := lgI_eq_units ha 1 (by norm_num)
  rw [Nat.cast_one] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [band_unit ha 0 1 (by norm_num) bandV01 bandV01_spec, band_unit ha 1 1 (by norm_num) bandV11 bandV11_spec,
    band_unit ha 2 1 (by norm_num) bandV21 bandV21_spec]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add]

/-- **`Lg(a, 2)` in closed form**, `a > 0`. -/
theorem lgI_closed_two {a : ℝ} (ha : 0 < a) :
    lgI a 2 = (∑ l : Fin 7, bandV02 l * fPiece l a) + ∑ l : Fin 7, bandV12 l * fPiece l (1 + a) := by
  have h := lgI_eq_units ha 2 (by norm_num)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [band_unit ha 0 2 (by norm_num) bandV02 bandV02_spec, band_unit ha 1 2 (by norm_num) bandV12 bandV12_spec]
  simp only [Nat.cast_zero, Nat.cast_one, zero_add]

/-- **`Lg(a, 3)` in closed form**, `a > 0`. -/
theorem lgI_closed_three {a : ℝ} (ha : 0 < a) :
    lgI a 3 = ∑ l : Fin 7, bandV03 l * fPiece l a := by
  have h := lgI_eq_units ha 3 (by norm_num)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [band_unit ha 0 3 (by norm_num) bandV03 bandV03_spec]
  simp only [Nat.cast_zero, zero_add]

/-- `Lg(a, -d) = Lg(a + d, d)`: the band's other half by the shift `v = w + d`. -/
theorem lgI_neg (a d : ℝ) : lgI a (-d) = lgI (a + d) d := by
  unfold lgI
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => cubicB v * cubicB (v + -d) * Real.log (v + a)) d]
  congr 1
  ext w
  show cubicB (w + d) * cubicB (w + d + -d) * Real.log (w + d + a) =
    cubicB w * cubicB (w + d) * Real.log (w + (a + d))
  rw [show w + d + -d = w by ring, show w + d + a = w + (a + d) by ring,
    mul_comm (cubicB (w + d)) (cubicB w)]

end SIDEExplicitFormula.Window
