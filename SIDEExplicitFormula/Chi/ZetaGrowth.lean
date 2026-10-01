/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZetaGrowth.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/RvM/ZetaGrowth.lean, the first module of EF_lit's route after ZetaBounds (relay
data/b569_route.txt: the route enters ZetaBounds only through `norm_riemannZeta_le_of_re_pos`). For primitive or not,
`χ ≠ 1` of modulus `N`:
* `LFunction χ` is entire, so analytic on a neighbourhood of every set (the analogue of `analyticOnNhd_riemannZeta`);
* the half-plane bound `‖L(s, χ)‖ ≤ (N + 1)‖s‖ / Re s` on `0 < Re s`, from the Abel representation
  `LFunction_eq_mul_integral` and the tail bound `norm_integral_tail_le` at `M = 1` (no pole term: ζ's `1/2 + 1/‖1 − s‖`
  is absent);
* linear growth on `Re s ≥ δ`, `|Im s| ≥ 1`, and the two consumer forms (`1/4 ≤ Re s`; `0.15 ≤ Re s`);
* on `Re s ≥ 2`: `‖L(s, χ) − 1‖ ≤ π²/6 − 1` from the Dirichlet series (`χ(1) = 1`, `‖χ(n)‖ ≤ 1`), hence
  `2 − π²/6 ≤ ‖L(s, χ)‖ ≤ π²/6`, `L(s, χ) ≠ 0`, and `1/3 ≤ ‖L(2 + it, χ)‖`.
Nothing here proves GRH or any statement about the zeros of `LFunction χ` in the critical strip.
-/
import SIDEExplicitFormula.Chi.ZetaBoundsStrip
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

open Complex Set MeasureTheory Real

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## Analyticity -/

/-- `LFunction χ` is analytic on a neighbourhood of every set, for `χ ≠ 1` (the analogue of
`analyticOnNhd_riemannZeta`; no pole is excluded). -/
theorem analyticOnNhd_LFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (S : Set ℂ) :
    AnalyticOnNhd ℂ (LFunction χ) S :=
  fun z _ => analyticAt_LFunction h1 z

/-! ## The half-plane bound -/

/-- **The half-plane bound for `χ`.** For `χ ≠ 1` and `0 < Re s`: `‖L(s, χ)‖ ≤ (N + 1)‖s‖ / Re s`. -/
theorem norm_LFunction_le_of_re_pos {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hσ : 0 < s.re) :
    ‖LFunction χ s‖ ≤ ((N : ℝ) + 1) * ‖s‖ / s.re := by
  have hint := norm_integral_tail_le h1 (M := 1) le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hint
  rw [LFunction_eq_mul_integral h1 hσ, norm_mul]
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (((N : ℝ) + 1) / s.re) := by gcongr
    _ = ((N : ℝ) + 1) * ‖s‖ / s.re := by ring

/-- `‖s‖ / Re s ≤ 1 + |Im s| / Re s` for `0 < Re s`. -/
theorem norm_div_re_le {s : ℂ} (hσ : 0 < s.re) : ‖s‖ / s.re ≤ 1 + |s.im| / s.re := by
  have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hσ] at hn
  calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
    _ = 1 + |s.im| / s.re := by field_simp

/-! ## Linear growth in `σ ≥ δ` -/

/-- **Linear growth of `L(s, χ)` in every right half-plane `σ ≥ δ > 0`**, explicit constant:
`‖L(s, χ)‖ ≤ (N + 1)(1 + δ⁻¹)·|Im s|` for `Re s ≥ δ`, `|Im s| ≥ 1`. -/
theorem LFunction_linear_growth {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hσ : δ ≤ s.re) (ht : 1 ≤ |s.im|) : ‖LFunction χ s‖ ≤ ((N : ℝ) + 1) * (1 + δ⁻¹) * |s.im| := by
  have hσpos : 0 < s.re := lt_of_lt_of_le hδ hσ
  have h := norm_LFunction_le_of_re_pos h1 hσpos
  have h2 : ‖s‖ / s.re ≤ (1 + δ⁻¹) * |s.im| := by
    calc ‖s‖ / s.re ≤ 1 + |s.im| / s.re := norm_div_re_le hσpos
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ ≤ |s.im| + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]; linarith
      _ = (1 + δ⁻¹) * |s.im| := by ring
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  calc ‖LFunction χ s‖ ≤ ((N : ℝ) + 1) * ‖s‖ / s.re := h
    _ = ((N : ℝ) + 1) * (‖s‖ / s.re) := by ring
    _ ≤ ((N : ℝ) + 1) * ((1 + δ⁻¹) * |s.im|) := by gcongr
    _ = ((N : ℝ) + 1) * (1 + δ⁻¹) * |s.im| := by ring

/-- ∃-constant form: for every `δ > 0` there is `C > 0` with `‖L(s, χ)‖ ≤ C·|Im s|` whenever `Re s ≥ δ`, `|Im s| ≥ 1`. -/
theorem LFunction_growth {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → 1 ≤ |s.im| → ‖LFunction χ s‖ ≤ C * |s.im| :=
  ⟨((N : ℝ) + 1) * (1 + δ⁻¹), by positivity, fun s hσ ht => LFunction_linear_growth h1 hδ hσ ht⟩

/-- Polynomial-growth form (the shape Zeta23/WeilEF/Landau.lean consumes for ζ), `A = 1`. -/
theorem LFunction_growth_quarter {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖LFunction χ s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C, hC, h⟩ := LFunction_growth h1 (δ := 1 / 4) (by norm_num)
  refine ⟨1, C, hC, fun s h₁ _ h₃ => ?_⟩
  simpa [Real.rpow_one] using h s h₁ h₃

/-- **Consumer interface (the analogue of `zeta_growth_right_at`).** For `0.15 ≤ Re s`:
`‖L(s, χ)‖ ≤ (N + 1)·(20/3)·(|Im s| + 3)`; no distance from a pole is needed. -/
theorem LFunction_growth_right_at {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) :
    ‖LFunction χ s‖ ≤ ((N : ℝ) + 1) * (20 / 3) * (|s.im| + 3) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have hσpos : 0 < s.re := by norm_num at hσ; linarith
  have hσ' : (3 : ℝ) / 20 ≤ s.re := by norm_num at hσ ⊢; linarith
  have h := norm_LFunction_le_of_re_pos h1 hσpos
  have h2 : ‖s‖ / s.re ≤ 20 / 3 * (|s.im| + 3) := by
    have ht : 0 ≤ |s.im| := abs_nonneg _
    calc ‖s‖ / s.re ≤ 1 + |s.im| / s.re := norm_div_re_le hσpos
      _ ≤ 1 + |s.im| / (3 / 20) := by gcongr
      _ ≤ 20 / 3 * (|s.im| + 3) := by linarith
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  calc ‖LFunction χ s‖ ≤ ((N : ℝ) + 1) * (‖s‖ / s.re) := by rw [mul_div_assoc] at h; exact h
    _ ≤ ((N : ℝ) + 1) * (20 / 3 * (|s.im| + 3)) := by gcongr
    _ = ((N : ℝ) + 1) * (20 / 3) * (|s.im| + 3) := by ring

theorem LFunction_growth_right {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, ((N : ℝ) + 1) * (20 / 3), by positivity, LFunction_growth_right_at h1⟩

/-! ## Bounds on `Re s ≥ 2` -/

/-- For `Re s ≥ 2`: `‖L(s, χ) − 1‖ ≤ Σ_{n≥2} n^{−2} = π²/6 − 1`. -/
theorem norm_LFunction_sub_one_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LFunction χ s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  set a : ℕ → ℂ := LSeries.term (fun n => χ n) s with ha
  have hsum : Summable a := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hL : LFunction χ s = ∑' n, a n := by
    rw [LFunction_eq_LSeries χ hs1]
    rfl
  have ha0 : a 0 = 0 := by simp [a]
  have ha1 : a 1 = 1 := by simp [a, map_one]
  have hsum1 : Summable (fun n => a (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hsplit : LFunction χ s - 1 = ∑' n, a (n + 2) := by
    rw [hL, hsum.tsum_eq_zero_add, ha0, hsum1.tsum_eq_zero_add, ha1]
    ring
  have hle : ∀ n : ℕ, ‖a (n + 2)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hpos : 0 < n + 2 := by omega
    rw [ha, LSeries.term_of_ne_zero (by omega), norm_div, Complex.norm_natCast_cpow_of_pos hpos]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    calc ‖χ ((n + 2 : ℕ) : ZMod N)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re
        ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ s.re := by
          gcongr
          exact DirichletCharacter.norm_le_one χ _
      _ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((n : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  have hsum2 : Summable (fun n => a (n + 2)) := (summable_nat_add_iff 2).mpr hsum
  have hb : Summable (fun n => ‖a (n + 2)‖) := htwo.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  rw [hsplit]
  calc ‖∑' n, a (n + 2)‖ ≤ ∑' n, ‖a (n + 2)‖ := norm_tsum_le_tsum_norm hb
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hb.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq

/-- `π²/6 − 1 < 1`. -/
theorem pi_sq_div_six_sub_one_lt_one' : Real.pi ^ 2 / 6 - 1 < 1 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- `1/3 < 2 − π²/6`. -/
theorem one_third_lt_two_sub_pi_sq_div_six' : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- Lower bound at the Jensen disc centre: `2 − π²/6 ≤ ‖L(s, χ)‖` for `Re s ≥ 2`. -/
theorem norm_LFunction_ge_of_two_le_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖LFunction χ s‖ := by
  have h := norm_LFunction_sub_one_le χ hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - LFunction χ s‖ ≤ ‖LFunction χ s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - LFunction χ s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith

/-- **Consumer interface (the analogue of `zeta_lower_bound_two`).** `‖L(2 + it, χ)‖ ≥ 1/3` for all real `t`. -/
theorem LFunction_lower_bound_two (χ : DirichletCharacter ℂ N) :
    ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖LFunction χ (2 + t * I)‖ := by
  intro t
  have h := norm_LFunction_ge_of_two_le_re χ (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six']

/-- `L(s, χ)` does not vanish on `Re s ≥ 2`. -/
theorem LFunction_ne_zero_of_two_le_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) : LFunction χ s ≠ 0 := by
  intro h
  have := norm_LFunction_ge_of_two_le_re χ hs
  rw [h, norm_zero] at this
  linarith [one_third_lt_two_sub_pi_sq_div_six']

/-- Upper bound on `Re s ≥ 2`: `‖L(s, χ)‖ ≤ π²/6`. -/
theorem norm_LFunction_le_of_two_le_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LFunction χ s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := norm_LFunction_sub_one_le χ hs
  have h' : ‖LFunction χ s‖ ≤ ‖LFunction χ s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (LFunction χ s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith

end GRHWeil
end SIDEExplicitFormula
