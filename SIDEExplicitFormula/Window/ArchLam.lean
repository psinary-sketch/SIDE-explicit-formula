import SIDEExplicitFormula.Window.ArchClosed
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# L9b, its fourth part: the far integrals `λ(d)` in closed form

`λ(d) = ∫ B(x) ℓ(x + d) dx`, `ℓ` the fourth difference of `tlog`, splits over the four unit intervals of the
spline's support (`lamI_eq_units`) and over the five terms of the difference (`lam_piece`). On `[k, k + 1]` the spline
is its piece `pieceP k`, and `tlog (s + c) = (s + c)^3 log (s + c)` where `c ≥ 0` and `0` where `c ≤ -1`; the product
`pieceP k s (s + c)^3` has the coefficients `lamW k c`, polynomials in `c`, so each term is `∑_l lamW k c l * fPiece l c`
(`lam_unit`, `lam_unit_neg`), the logarithm's singularity at `c = 0` integrable (`intervalIntegrable_log_add`). At each
integer `d`, `λ(d)` is the combination `lamI_closed` of the `lamT k (k + d - m)`.
-/

namespace SIDEExplicitFormula.Window

open MeasureTheory

/-- `log (s + c)` is integrable on `[0, 1]` for every `c`, the logarithm's singularity integrable. -/
theorem intervalIntegrable_log_add (c : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.log (s + c)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := c) (b := 1 + c)).comp_add_right c
  simpa using h

/-- `integral_poly_log` for every `c`. -/
theorem integral_poly_log_all (c : ℝ) {n : ℕ} (p : Fin n → ℝ) :
    ∫ s in (0 : ℝ)..1, (∑ l : Fin n, p l * s ^ (l : ℕ)) * Real.log (s + c) =
      ∑ l : Fin n, p l * fPiece l c := by
  have hI : ∀ l ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun s : ℝ => p l * s ^ (l : ℕ) * Real.log (s + c)) volume 0 1 := by
    intro l _
    exact (intervalIntegrable_log_add c).continuousOn_mul
      (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun s : ℝ => p l * s ^ (l : ℕ)) _)
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hI]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- `lamW k c`: the coefficients in `s` of `pieceP k s * (s + c)^3`, each a polynomial in `c`. -/
noncomputable def lamW : ℕ → ℝ → Fin 7 → ℝ
  | 0, c => ![0, 0, 0, (1 / 6) * c ^ 3, (1 / 2) * c ^ 2, (1 / 2) * c, 1 / 6]
  | 1, c => ![(1 / 6) * c ^ 3, (1 / 2) * c ^ 3 + (1 / 2) * c ^ 2,
      (1 / 2) * c ^ 3 + (3 / 2) * c ^ 2 + (1 / 2) * c, (-1 / 2) * c ^ 3 + (3 / 2) * c ^ 2 + (3 / 2) * c + 1 / 6,
      (-3 / 2) * c ^ 2 + (3 / 2) * c + 1 / 2, (-3 / 2) * c + 1 / 2, -1 / 2]
  | 2, c => ![(2 / 3) * c ^ 3, 2 * c ^ 2, (-1) * c ^ 3 + 2 * c, (1 / 2) * c ^ 3 + (-3) * c ^ 2 + 2 / 3,
      (3 / 2) * c ^ 2 + (-3) * c, (3 / 2) * c + (-1), 1 / 2]
  | 3, c => ![(1 / 6) * c ^ 3, (-1 / 2) * c ^ 3 + (1 / 2) * c ^ 2,
      (1 / 2) * c ^ 3 + (-3 / 2) * c ^ 2 + (1 / 2) * c, (-1 / 6) * c ^ 3 + (3 / 2) * c ^ 2 + (-3 / 2) * c + 1 / 6,
      (-1 / 2) * c ^ 2 + (3 / 2) * c + (-1 / 2), (-1 / 2) * c + 1 / 2, -1 / 6]
  | _, _ => fun _ => 0

theorem lamW_spec (k : ℕ) (hk : k ≤ 3) (s c : ℝ) :
    pieceP k s * (s + c) ^ 3 = ∑ l : Fin 7, lamW k c l * s ^ (l : ℕ) := by
  interval_cases k <;>
    simp only [lamW, pieceP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ] <;>
    ring

/-- One term of `λ` where `c ≥ 0`: `∫_0^1 B(k + s) tlog (s + c) ds = ∑_l lamW k c l * fPiece l c`. -/
theorem lam_unit {k : ℕ} (hk : k ≤ 3) {c : ℝ} (hc : 0 ≤ c) :
    ∫ s in (0 : ℝ)..1, cubicB (s + k) * tlog (s + c) = ∑ l : Fin 7, lamW k c l * fPiece l c := by
  rw [intervalIntegral.integral_congr
    (g := fun s : ℝ => (∑ l : Fin 7, lamW k c l * s ^ (l : ℕ)) * Real.log (s + c)) (fun s hs => ?_)]
  · exact integral_poly_log_all c (lamW k c)
  · rw [Set.uIcc_of_le zero_le_one] at hs
    obtain ⟨h0, h1⟩ := hs
    show cubicB (s + k) * tlog (s + c) = (∑ l : Fin 7, lamW k c l * s ^ (l : ℕ)) * Real.log (s + c)
    rw [cubicB_add_nat h0 h1 k hk, tlog_of_nonneg (by linarith : (0 : ℝ) ≤ s + c), ← lamW_spec k hk s c]
    ring

/-- One term of `λ` where `c ≤ -1`: the truncated logarithm is `0` on `[0, 1]`. -/
theorem lam_unit_neg {k : ℕ} {c : ℝ} (hc : c ≤ -1) :
    ∫ s in (0 : ℝ)..1, cubicB (s + k) * tlog (s + c) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) (fun s hs => ?_)]
  · simp
  · rw [Set.uIcc_of_le zero_le_one] at hs
    show cubicB (s + k) * tlog (s + c) = 0
    rw [tlog_of_nonpos (by linarith [hs.2] : s + c ≤ 0), mul_zero]

/-- `λ`'s integrand on `[k, k + 1]` by the five terms of the fourth difference. -/
theorem lam_piece (k : ℕ) (d : ℝ) :
    ∫ s in (0 : ℝ)..1, cubicB (s + k) * ellLog (s + k + d) =
      ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 *
        ∫ s in (0 : ℝ)..1, cubicB (s + k) * tlog (s + ((k : ℝ) + d - m)) := by
  have hB := continuous_cubicB
  have hT := continuous_tlog
  have hpt : ∀ s : ℝ, cubicB (s + k) * ellLog (s + k + d) =
      ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * (cubicB (s + k) * tlog (s + ((k : ℝ) + d - m))) := by
    intro s
    unfold ellLog
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [show s + (k : ℝ) + d - m = s + ((k : ℝ) + d - m) by ring]
    ring
  have hI : ∀ m ∈ Finset.range 5, IntervalIntegrable
      (fun s : ℝ => (bw m : ℝ) / 6 * (cubicB (s + k) * tlog (s + ((k : ℝ) + d - m)))) volume 0 1 :=
    fun m _ => (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum hI]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_const_mul]

/-- `λ(d)` as the sum of its integrals over the spline's four unit intervals. -/
theorem lamI_eq_units (d : ℝ) :
    lamI d = ∑ k ∈ Finset.range 4, ∫ s in (0 : ℝ)..1, cubicB (s + k) * ellLog (s + k + d) := by
  have hB := continuous_cubicB
  have hE := continuous_ellLog
  have hcont : ∀ k : ℕ, IntervalIntegrable (fun x : ℝ => cubicB x * ellLog (x + d)) volume
      (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    fun k => (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hzero : ∀ v, v ∉ Set.Ioc (0 : ℝ) 4 → cubicB v * ellLog (v + d) = 0 := by
    intro v hv
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    rcases hv with hv | hv
    · rw [cubicB_eq_zero_of_nonpos hv, zero_mul]
    · rw [cubicB_eq_zero_of_ge hv.le, zero_mul]
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  have hfull : lamI d = ∫ v in ((0 : ℕ) : ℝ)..((4 : ℕ) : ℝ), cubicB v * ellLog (v + d) := by
    rw [Nat.cast_zero, h4, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4),
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    rfl
  rw [hfull, ← intervalIntegral.sum_integral_adjacent_intervals (a := (Nat.cast : ℕ → ℝ))
    (fun k _ => hcont k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have key := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => cubicB x * ellLog (x + d)) (k : ℝ)
  rw [zero_add, add_comm (1 : ℝ) (k : ℝ)] at key
  rw [Nat.cast_add, Nat.cast_one]
  exact key.symm

/-- `lamT k c`: one term of `λ` at an integer shift `c`, `∑_l lamW k c l * fPiece l c` where `c ≥ 0`, else `0`. -/
noncomputable def lamT (k : ℕ) (c : ℤ) : ℝ := if 0 ≤ c then ∑ l : Fin 7, lamW k c l * fPiece l c else 0

theorem lam_unit_int {k : ℕ} (hk : k ≤ 3) (c : ℤ) :
    ∫ s in (0 : ℝ)..1, cubicB (s + k) * tlog (s + c) = lamT k c := by
  unfold lamT
  split_ifs with h
  · exact lam_unit hk (by exact_mod_cast h)
  · have h1 : c ≤ -1 := by omega
    exact lam_unit_neg (by exact_mod_cast h1)

/-- **`λ(d)` in closed form** at each integer `d`: `∑_(k < 4) ∑_(m < 5) (bw m / 6) lamT k (k + d - m)`. -/
theorem lamI_closed (d : ℤ) :
    lamI d = ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + d - m) := by
  rw [lamI_eq_units]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [lam_piece]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hk3 : k ≤ 3 := by
    have := Finset.mem_range.mp hk
    omega
  have hcast : ((((k : ℤ) + d - m : ℤ)) : ℝ) = (k : ℝ) + d - m := by norm_num
  rw [← lam_unit_int hk3 ((k : ℤ) + d - m), hcast]

end SIDEExplicitFormula.Window
