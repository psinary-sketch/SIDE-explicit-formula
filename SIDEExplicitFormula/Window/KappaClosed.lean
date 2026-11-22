import SIDEExplicitFormula.Window.KBasis

/-!
# `κ_n(e)` in closed form

`κ_n(e) = ∫ B(u) B(n u - e) du` (`kappaB`) written exactly, for `n ≥ 1`. The B-spline is the fourth difference of truncated cubes with
weights `w = (1, -4, 6, -4, 1)` (`cubicB_eq_sum`); on `[0, 4]`, where `B` lives, each product of two truncated cubes integrates by an
explicit antiderivative (`kapF`, `integral_tpow3_mul_tpow3`); and the terms of degree below four cancel in the two fourth differences, so
that `5040 n^4 κ_n(e)` is the integer `∑_k ∑_l w_k w_l max(e + l - k n, 0)^7` (`kapTilde`, `kappaB_eq_kapTilde`).
-/

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Window

/-- The weights of the fourth difference, `(1, -4, 6, -4, 1)`. -/
def bw : ℕ → ℤ
  | 0 => 1
  | 1 => -4
  | 2 => 6
  | 3 => -4
  | 4 => 1
  | _ => 0

/-- `5040 n^4 κ_n(e)`, an integer: `∑_k ∑_l w_k w_l max(e + l - k n, 0)^7`. -/
def kapTilde (n : ℕ) (e : ℤ) : ℤ :=
  ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, bw k * bw l * (max (e + (l : ℤ) - (k : ℤ) * (n : ℤ)) 0) ^ 7

/-- An antiderivative of `(u - k)^3 (n u - f)^3` in `u`. -/
def kapF (n k f u : ℝ) : ℝ :=
  (u - k) ^ 4 * (n * u - f) ^ 3 / 4 - 3 * n / 20 * (u - k) ^ 5 * (n * u - f) ^ 2
    + n ^ 2 / 20 * (u - k) ^ 6 * (n * u - f) - n ^ 3 / 140 * (u - k) ^ 7

/-- The integral over `[0, 4]` of `tpow3 (u - k) * tpow3 (n u - f)`: the antiderivative from where both cubes are on. -/
def kapT (n k f : ℝ) : ℝ := if max k (f / n) ≤ 4 then kapF n k f 4 - kapF n k f (max k (f / n)) else 0

/-- `140 n^4` times the antiderivative at `4`. -/
def kapF4 (n k f : ℝ) : ℝ :=
  35 * n ^ 4 * (4 - k) ^ 4 * (4 * n - f) ^ 3 - 21 * n ^ 5 * (4 - k) ^ 5 * (4 * n - f) ^ 2
    + 7 * n ^ 6 * (4 - k) ^ 6 * (4 * n - f) - n ^ 7 * (4 - k) ^ 7

/-- `140 n^4 kapT n k f` as a polynomial with a truncated seventh power. -/
def kapTt (n k f : ℝ) : ℝ := if f ≤ 4 * n then kapF4 n k f + (max (f - k * n) 0) ^ 7 else 0

/-! ## The B-spline as a fourth difference -/

theorem cubicB_eq_sum (x : ℝ) : cubicB x = (∑ k ∈ Finset.range 5, (bw k : ℝ) * tpow3 (x - k)) / 6 := by
  rw [cubicB]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat, sub_zero]
  ring

theorem cubicB_mul_cubicB_eq (n : ℕ) (e : ℤ) (u : ℝ) :
    cubicB u * cubicB ((n : ℝ) * u - e) = ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
      (bw k : ℝ) * bw l / 36 * (tpow3 (u - k) * tpow3 ((n : ℝ) * u - ((e : ℝ) + l))) := by
  rw [cubicB_eq_sum u, cubicB_eq_sum ((n : ℝ) * u - e), Finset.sum_div, Finset.sum_div, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [show (n : ℝ) * u - (e : ℝ) - (l : ℝ) = (n : ℝ) * u - ((e : ℝ) + l) by ring]
  ring

/-! ## One product of truncated cubes, integrated -/

theorem hasDerivAt_kapF (n k f u : ℝ) :
    HasDerivAt (kapF n k f) ((u - k) ^ 3 * (n * u - f) ^ 3) u := by
  have hA : HasDerivAt (fun y : ℝ => y - k) 1 u := (hasDerivAt_id' u).sub_const k
  have hB : HasDerivAt (fun y : ℝ => n * y - f) (n * 1) u := ((hasDerivAt_id' u).const_mul n).sub_const f
  have h := (((((hA.pow 4).mul (hB.pow 3)).div_const 4).sub
      (((hA.pow 5).const_mul (3 * n / 20)).mul (hB.pow 2))).add
      (((hA.pow 6).const_mul (n ^ 2 / 20)).mul hB)).sub ((hA.pow 7).const_mul (n ^ 3 / 140))
  unfold kapF
  exact h.congr_deriv (by
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub]
    ring)

/-- **One product of truncated cubes over `[0, 4]`**, `n > 0`, `k ≥ 0`. -/
theorem integral_tpow3_mul_tpow3 (n k f : ℝ) (hn : 0 < n) (hk : 0 ≤ k) :
    ∫ u in (0 : ℝ)..4, tpow3 (u - k) * tpow3 (n * u - f) = kapT n k f := by
  have h3 := contDiff_tpow3.continuous
  have hcont : Continuous (fun u : ℝ => tpow3 (u - k) * tpow3 (n * u - f)) := by fun_prop
  have hzero : ∀ u : ℝ, u ≤ max k (f / n) → tpow3 (u - k) * tpow3 (n * u - f) = 0 := by
    intro u hu
    rcases le_max_iff.mp hu with h | h
    · rw [tpow3_of_nonpos (show u - k ≤ 0 by linarith), zero_mul]
    · have h' : u * n ≤ f := (le_div_iff₀ hn).mp h
      rw [tpow3_of_nonpos (show n * u - f ≤ 0 by linarith), mul_zero]
  have hpoly : ∀ u : ℝ, max k (f / n) ≤ u →
      tpow3 (u - k) * tpow3 (n * u - f) = (u - k) ^ 3 * (n * u - f) ^ 3 := by
    intro u hu
    have h1 : k ≤ u := le_trans (le_max_left _ _) hu
    have h2 : f / n ≤ u := le_trans (le_max_right _ _) hu
    have h2' : f ≤ u * n := (div_le_iff₀ hn).mp h2
    rw [tpow3_of_nonneg (show 0 ≤ u - k by linarith), tpow3_of_nonneg (show 0 ≤ n * u - f by linarith)]
  have hlo0 : 0 ≤ max k (f / n) := le_trans hk (le_max_left _ _)
  unfold kapT
  split_ifs with h4
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) 0 (max k (f / n)))
      (hcont.intervalIntegrable (μ := volume) (max k (f / n)) 4)
    have e1 : ∫ u in (0 : ℝ)..(max k (f / n)), tpow3 (u - k) * tpow3 (n * u - f) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => ?_), intervalIntegral.integral_zero]
      rw [Set.uIcc_of_le hlo0] at hu
      exact hzero u hu.2
    have e2 : ∫ u in (max k (f / n))..4, tpow3 (u - k) * tpow3 (n * u - f) =
        kapF n k f 4 - kapF n k f (max k (f / n)) := by
      rw [intervalIntegral.integral_congr (g := fun u => (u - k) ^ 3 * (n * u - f) ^ 3) (fun u hu => ?_)]
      · exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_kapF n k f u)
          ((by fun_prop : Continuous (fun u : ℝ => (u - k) ^ 3 * (n * u - f) ^ 3)).intervalIntegrable _ _)
      · rw [Set.uIcc_of_le h4] at hu
        exact hpoly u hu.1
    rw [← hsplit, e1, e2, zero_add]
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => ?_), intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4)] at hu
    exact hzero u (by linarith [hu.2, not_le.mp h4])

/-! ## κ as a double sum of such integrals -/

theorem kappaB_eq_intervalIntegral (n : ℕ) (e : ℤ) :
    kappaB n e = ∫ u in (0 : ℝ)..4, cubicB u * cubicB ((n : ℝ) * u - e) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
  unfold kappaB
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with hu | hu
  · rw [cubicB_eq_zero_of_nonpos hu, zero_mul]
  · rw [cubicB_eq_zero_of_ge hu.le, zero_mul]

theorem kappaB_eq_sum (n : ℕ) (hn : 0 < n) (e : ℤ) :
    kappaB n e = ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
      (bw k : ℝ) * bw l / 36 * kapT n k ((e : ℝ) + l) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h3 := contDiff_tpow3.continuous
  rw [kappaB_eq_intervalIntegral]
  have hexp : (fun u : ℝ => cubicB u * cubicB ((n : ℝ) * u - e)) = fun u => ∑ k ∈ Finset.range 5,
      ∑ l ∈ Finset.range 5, (bw k : ℝ) * bw l / 36 * (tpow3 (u - k) * tpow3 ((n : ℝ) * u - ((e : ℝ) + l))) := by
    funext u
    exact cubicB_mul_cubicB_eq n e u
  rw [hexp, intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_tpow3_mul_tpow3 _ _ _ hn' (Nat.cast_nonneg k)]

/-! ## Each integral as a polynomial, and the cancellations -/

theorem kapT_eq (n k f : ℝ) (hn : 0 < n) (hk : k ≤ 4) : kapT n k f = kapTt n k f / (140 * n ^ 4) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hiff : max k (f / n) ≤ 4 ↔ f ≤ 4 * n := by
    rw [max_le_iff, div_le_iff₀ hn]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  unfold kapT kapTt
  by_cases h4 : f ≤ 4 * n
  · rw [if_pos (hiff.mpr h4), if_pos h4]
    rcases le_total (f / n) k with hfk | hfk
    · have hfk' : f - k * n ≤ 0 := by
        have h := (div_le_iff₀ hn).mp hfk
        linarith
      rw [max_eq_left hfk, max_eq_right hfk']
      unfold kapF kapF4
      field_simp
      ring
    · have hfk' : 0 ≤ f - k * n := by
        have h := (le_div_iff₀ hn).mp hfk
        linarith
      rw [max_eq_right hfk, max_eq_left hfk']
      unfold kapF kapF4
      field_simp
      ring
  · rw [if_neg (fun h => h4 (hiff.mp h)), if_neg h4, zero_div]

theorem kapTt_eq (n k f : ℝ) (hn : 0 ≤ n) (hk : k ≤ 4) :
    kapTt n k f = kapF4 n k f + (max (f - k * n) 0) ^ 7 -
      (if 4 * n < f then kapF4 n k f + (f - k * n) ^ 7 else 0) := by
  unfold kapTt
  by_cases h : f ≤ 4 * n
  · rw [if_pos h, if_neg (not_lt.mpr h), sub_zero]
  · rw [if_neg h, if_pos (not_le.mp h)]
    have hpos : 0 ≤ f - k * n := by nlinarith [not_le.mp h]
    rw [max_eq_left hpos]
    ring

/-- The fourth difference in `l` of the polynomial part is `0`: it is a cubic in `l`. -/
theorem sum_bw_kapF4 (n k e : ℝ) : ∑ l ∈ Finset.range 5, (bw l : ℝ) * kapF4 n k (e + l) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, kapF4, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat]
  ring

/-- The fourth difference in `k` of the full antiderivative's difference is `0`: `B` vanishes beyond `4`. -/
theorem sum_bw_kapG (n f : ℝ) : ∑ k ∈ Finset.range 5, (bw k : ℝ) * (kapF4 n k f + (f - k * n) ^ 7) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, kapF4, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat]
  ring

theorem sum_sum_bw_kapF4 (n e : ℝ) :
    ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, (bw k : ℝ) * bw l * kapF4 n k (e + l) = 0 := by
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have h : ∀ l : ℕ, (bw k : ℝ) * bw l * kapF4 n k (e + l) = (bw k : ℝ) * ((bw l : ℝ) * kapF4 n k (e + l)) :=
    fun l => mul_assoc _ _ _
  simp only [h]
  rw [← Finset.mul_sum, sum_bw_kapF4, mul_zero]

theorem sum_sum_bw_ite (n e : ℝ) :
    ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, (bw k : ℝ) * bw l *
      (if 4 * n < e + l then kapF4 n k (e + l) + (e + l - k * n) ^ 7 else 0) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  by_cases h : 4 * n < e + l
  · have h' : ∀ k : ℕ, (bw k : ℝ) * bw l *
        (if 4 * n < e + l then kapF4 n k (e + l) + (e + l - k * n) ^ 7 else 0) =
        (bw l : ℝ) * ((bw k : ℝ) * (kapF4 n k (e + l) + (e + l - k * n) ^ 7)) := fun k => by
      rw [if_pos h]
      ring
    simp only [h']
    rw [← Finset.mul_sum, sum_bw_kapG, mul_zero]
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

theorem kapTilde_cast (n : ℕ) (e : ℤ) : (kapTilde n e : ℝ) =
    ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, (bw k : ℝ) * bw l * (max ((e : ℝ) + l - k * n) 0) ^ 7 := by
  unfold kapTilde
  push_cast
  try rfl

/-- **`κ_n(e)` in closed form**: `5040 n^4 κ_n(e)` is the integer `kapTilde n e`, `n ≥ 1`. -/
theorem kappaB_eq_kapTilde (n : ℕ) (hn : 0 < n) (e : ℤ) :
    kappaB n e = (kapTilde n e : ℝ) / (5040 * (n : ℝ) ^ 4) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hk4 : ∀ k ∈ Finset.range 5, (k : ℝ) ≤ 4 := fun k hk => by
    have h := Finset.mem_range.mp hk
    exact_mod_cast (show k ≤ 4 by omega)
  have hsum : ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, (bw k : ℝ) * bw l * kapTt n k ((e : ℝ) + l)
      = (kapTilde n e : ℝ) := by
    have h1 : ∀ k ∈ Finset.range 5, ∀ l ∈ Finset.range 5,
        (bw k : ℝ) * bw l * kapTt n k ((e : ℝ) + l) =
          (bw k : ℝ) * bw l * kapF4 n k ((e : ℝ) + l) + (bw k : ℝ) * bw l * (max ((e : ℝ) + l - k * n) 0) ^ 7
            - (bw k : ℝ) * bw l * (if 4 * (n : ℝ) < (e : ℝ) + l then
                kapF4 n k ((e : ℝ) + l) + ((e : ℝ) + l - k * n) ^ 7 else 0) := by
      intro k hk l _
      rw [kapTt_eq _ _ _ hn'.le (hk4 k hk)]
      ring
    rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => h1 k hk l hl))]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sum_sum_bw_kapF4, sum_sum_bw_ite, zero_add, sub_zero, kapTilde_cast]
  rw [kappaB_eq_sum n hn e, ← hsum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [kapT_eq _ _ _ hn' (hk4 k hk)]
  ring

end Window
end SIDEExplicitFormula
