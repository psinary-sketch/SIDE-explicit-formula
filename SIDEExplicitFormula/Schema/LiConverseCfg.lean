/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/LiConverseCfg.lean
THIS PROGRAMME'S WORK (act b669, ruling (R279)(3)-(4) and the author's word on the route: (P)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CONVERSE OVER A CONFIGURATION, ON THE BOMBIERI-LAGARIAS ROUTE (OPEN_TRAILS :11609, (V1)-(V4); at χ :11732, :11796), STATED
AND ATTEMPTED. (V1) is the configuration's own fields `reflect_mem`, `mult_reflect`. (V2) an off-line point of a configuration in
the open strip has an orbit member `ρ′` with `1 < ‖1 - ρ′⁻¹‖` (`exists_dominant_point`). (V3) for `1 < r` the points with
`r ≤ ‖1 - ρ⁻¹‖` are finitely many (`dominant_finite`; the kernel's finite dominant set for the power-window score,
PowerWindow.lean :398-:403, is another set). (V4) the power-sum lemma, generic -- a lemma of finite sums naming no configuration:
for finitely many distinct `w_i` of modulus `1`, none equal to `1`, with multiplicities `m_i ≥ 1`, the real part of
`Σ m_i w_i ^ n` is at most `-c` for infinitely many `n`, `c = (Σ m_i ^ 2) / (8 Σ m_i)`; attempted by Cesàro means (the
partial sums of each `w_i ^ n` bounded, `norm_geom_sum_le`, `norm_sum_powerSum_le`; the mean square of the power sum and of its
real part are the open steps). (V5) the points off the dominant set contribute at most `C (n + 1)^2 s^n` (`remainder_le`).
The converse `li_nonneg_cfg_imp_online` (S5) under the local count and the open strip, and its instance at χ
`li_nonneg_chi_imp_grh_chi` (S6), are stated; their proofs rest on (V4) and (V5) where those are open.
Nothing here proves GRH or RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.LiCfg
import SIDEExplicitFormula.Chi.LocalCount

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open Zeta23

/-! ## (V2) the strict modulus off the line, and the orbit member -/

/-- Left of the line, `‖ρ‖ < ‖ρ - 1‖`. -/
theorem norm_lt_norm_sub_one_of_re_lt_half {ρ : ℂ} (h : ρ.re < 1 / 2) : ‖ρ‖ < ‖ρ - 1‖ := by
  have hsq : ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  nlinarith [norm_nonneg ρ, norm_nonneg (ρ - 1)]

/-- **(V2), per point:** left of the line and off `0`, `1 < ‖1 - ρ⁻¹‖`. -/
theorem one_lt_norm_one_sub_inv {ρ : ℂ} (h0 : ρ ≠ 0) (h : ρ.re < 1 / 2) : 1 < ‖1 - ρ⁻¹‖ := by
  have he : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [he, norm_div, one_lt_div (norm_pos_iff.mpr h0)]
  exact norm_lt_norm_sub_one_of_re_lt_half h

/-- **(V2), on the configuration:** in the open strip, an off-line point has an orbit member under `ρ ↦ 1 - conj ρ`
(the configuration's `reflect_mem`) with `1 < ‖1 - ρ′⁻¹‖`. -/
theorem exists_dominant_point (Z : ZeroConfig) (hs : B321.HStrip Z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hoff : ρ.re ≠ 1 / 2) : ∃ ρ' ∈ Z.carrier, 1 < ‖1 - ρ'⁻¹‖ := by
  have hne : ∀ σ ∈ Z.carrier, σ ≠ 0 := by
    intro σ hσ e
    have h0 := (hs σ hσ).1
    rw [e, Complex.zero_re] at h0
    exact lt_irrefl _ h0
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact ⟨ρ, hρ, one_lt_norm_one_sub_inv (hne ρ hρ) hlt⟩
  · have hmem : Zeta23.reflect ρ ∈ Z.carrier := Z.reflect_mem ρ hρ
    refine ⟨Zeta23.reflect ρ, hmem, one_lt_norm_one_sub_inv (hne _ hmem) ?_⟩
    unfold Zeta23.reflect
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-! ## (V3) the dominant set is finite -/

/-- **(V3):** for `1 < r`, the points of `Z` with `r ≤ ‖1 - ρ⁻¹‖` are finitely many: `r ‖ρ‖ ≤ ‖ρ - 1‖` and `0 ≤ Re ρ` give
`(r ^ 2 - 1) ‖ρ‖ ^ 2 ≤ 1`, a bounded ordinate, and `finite_window` leaves finitely many points. -/
theorem dominant_finite (Z : ZeroConfig) {r : ℝ} (hr : 1 < r) :
    {ρ : ℂ | ρ ∈ Z.carrier ∧ r ≤ ‖1 - ρ⁻¹‖}.Finite := by
  have hr2 : 0 < r ^ 2 - 1 := by nlinarith
  set K : ℝ := 1 / (r ^ 2 - 1) with hK
  have hKpos : 0 < K := by rw [hK]; exact div_pos one_pos hr2
  refine (Z.finite_window (-(K + 2)) (K + 1)).subset ?_
  rintro ρ ⟨hρ, hle⟩
  have h0 : ρ ≠ 0 := by
    rintro rfl
    rw [inv_zero, sub_zero, norm_one] at hle
    linarith
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
  have he : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [he, norm_div, le_div_iff₀ hn] at hle
  have hsq : r ^ 2 * ‖ρ‖ ^ 2 ≤ ‖ρ - 1‖ ^ 2 := by
    have := mul_le_mul hle hle (mul_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _)
    nlinarith [this]
  have hst := Z.strip ρ hρ
  have hexp : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 - 2 * ρ.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hbd : (r ^ 2 - 1) * ‖ρ‖ ^ 2 ≤ 1 := by nlinarith [hst.1]
  have him : ρ.im ^ 2 ≤ ‖ρ‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm ρ) 2
    rwa [sq_abs] at this
  have hK2 : ρ.im ^ 2 ≤ K := by
    rw [hK, le_div_iff₀ hr2]
    nlinarith
  exact ⟨hρ, by nlinarith [sq_nonneg (ρ.im + 1)], by nlinarith [sq_nonneg (ρ.im - 1)]⟩

/-! ## (V4) the power-sum lemma, generic, attempted by Cesàro means -/

/-- The partial geometric sums of a unimodular `w ≠ 1` are bounded: `‖Σ_{n<N} w ^ n‖ ≤ 2 / ‖w - 1‖`. -/
theorem norm_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ 2 / ‖w - 1‖ := by
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  rw [geom_sum_eq hw1 N, norm_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num

/-- The power sum's partial sums are bounded uniformly in `N`: `‖Σ_{n<N} Σ_i m_i w_i ^ n‖ ≤ Σ_i m_i (2 / ‖w_i - 1‖)` --
the mean of the power sum over `n < N` tends to `0`. -/
theorem norm_sum_powerSum_le {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (hw1 : ∀ i ∈ s, w i ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ∑ i ∈ s, (m i : ℂ) * w i ^ n‖ ≤ ∑ i ∈ s, (m i : ℝ) * (2 / ‖w i - 1‖) := by
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [← Finset.mul_sum, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_geom_sum_le (hw i hi) (hw1 i hi) N) (Nat.cast_nonneg _)

/-- **(V4), the power-sum lemma:** for finitely many distinct `w_i` of modulus `1`, none equal to `1`, with multiplicities
`m_i ≥ 1`, the real part of `Σ_i m_i w_i ^ n` is at most `-(Σ m_i ^ 2) / (8 Σ m_i)` for infinitely many `n`. A lemma of finite
sums: no configuration and no zeta object. The proof's remaining steps are the mean square of the power sum
(`Σ m_i ^ 2` in the mean, the distinct `w_i / w_j` geometric) and of its real part (at least half of it), which with the
bounded mean (`norm_sum_powerSum_le`) force the negative values. -/
theorem powerSum_re_le_neg_infinitely {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) (hw1 : ∀ i ∈ s, w i ≠ 1) (hinj : Set.InjOn w s) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∀ N : ℕ, ∃ n ≥ N, (∑ i ∈ s, (m i : ℂ) * w i ^ n).re ≤
      -((∑ i ∈ s, (m i : ℝ) ^ 2) / (8 * ∑ i ∈ s, (m i : ℝ))) := by
  sorry

/-! ## (V5) the remainder off the dominant set -/

/-- **(V5):** for `1 < s`, the points with `‖1 - ρ⁻¹‖ < s` contribute at most `C (n + 1) ^ 2 s ^ n` to the real part of the
Li sum, under the local count and the open strip. -/
theorem remainder_le (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (hs : B321.HStrip Z) {s : ℝ} (hs1 : 1 < s) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re| ≤
        C * ((n : ℝ) + 1) ^ 2 * s ^ n := by
  sorry

/-! ## (S5) the converse over a configuration -/

/-- **The converse over a configuration (S5):** under the local count and the open strip, `0 ≤ liCoeffCfg Z n` for every `n`
puts every point of `Z` on the line. -/
theorem li_nonneg_cfg_imp_online (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (hs : B321.HStrip Z) :
    (∀ n : ℕ, 0 ≤ liCoeffCfg Z n) → ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  sorry

end Schema

namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- **The converse at χ (S6):** `(∀ n, 0 ≤ liCoeffCfg (chiZeroConfig χ hχ h1) n) → GRH_chi χ`, S5 at `chiZeroConfig` with
χ's local count (`chiZeroConfig_local_count`) and the open strip of its carrier. -/
theorem li_nonneg_chi_imp_grh_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    (∀ n : ℕ, 0 ≤ Schema.liCoeffCfg (chiZeroConfig χ hχ h1) n) → GRH_chi χ := fun h s hs h0 h1' => by
  obtain ⟨A₀, hA₀, hloc⟩ := chiZeroConfig_local_count hχ h1
  have hstrip : B321.HStrip (chiZeroConfig χ hχ h1) := by
    unfold B321.HStrip
    exact fun ρ hρ => ⟨hρ.2.1, hρ.2.2⟩
  exact Schema.li_nonneg_cfg_imp_online (chiZeroConfig χ hχ h1) (A₀ := A₀) ⟨hA₀, hloc⟩ hstrip h s ⟨hs, h0, h1'⟩

end GRHWeil
end SIDEExplicitFormula
