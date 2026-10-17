/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/Remainder.lean
THIS PROGRAMME'S WORK (act b679, ruling (R289)(4)-(6); the plan relay data/b679_strip_plan.txt == 2, == 3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(V5') THE REMAINDER OFF THE DOMINANT SET OVER THE WIDENED CLASS: Schema/LiRemainder.lean's (V5) with the configuration a
`WideConfig` and `Wide.HExcl` in place of `B321.HStrip`. The proof is v0.32's with two constants moved and none of the bound's:
`|Re ρ⁻¹| ≤ (3/2) / ‖ρ‖ ^ 2` from `|Re ρ| < 3/2` (LiRemainder.lean :95's step), and `|γ| ^ 2 ≤ (Im ρ) ^ 2 + 1` from
`(Re ρ - 1/2) ^ 2 < 1` (:150's step); the per-point constant `2` and the constant `2 + 2 (1 + s) ^ 2` hold unchanged. `ρ ≠ 0` comes
from the exclusion's half at `0`. The generic lemmas `one_sub_pow_expand`, `norm_double_geom_le` and `re_one_sub_pow_abs_le` are
LiRemainder.lean's, used as they stand. Nothing here proves GRH or RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Wide.Config
import SIDEExplicitFormula.Schema.LiRemainder

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Wide

open Zeta23

/-- **The term, bounded off the dominant set, in the widened strip:** for `ρ ≠ 0` with `-1/2 < Re ρ < 3/2`, `‖1 - ρ⁻¹‖ ≤ s` and
`1 ≤ s`, `|Re (liTerm n ρ)| ≤ 2 (n + 1) ^ 2 s ^ n (1 / ‖ρ‖ ^ 2)` -- LiRemainder.lean :84's bound, its constant unchanged. -/
theorem liTerm_re_abs_le_pow {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : -1 / 2 < ρ.re) (h2 : ρ.re < 3 / 2) {s : ℝ} (hs1 : 1 ≤ s)
    (hz : ‖1 - ρ⁻¹‖ ≤ s) (n : ℕ) : |(LiWeil.liTerm n ρ).re| ≤ 2 * ((n : ℝ) + 1) ^ 2 * s ^ n * (1 / ‖ρ‖ ^ 2) := by
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
  have hn2 : 0 < ‖ρ‖ ^ 2 := pow_pos hn 2
  have hb := re_one_sub_pow_abs_le ρ⁻¹ hs1 hz n
  have hre : |ρ.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hure : |ρ⁻¹.re| ≤ 3 / 2 * (1 / ‖ρ‖ ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq, abs_div, abs_of_pos hn2, mul_one_div]
    exact div_le_div_of_nonneg_right hre hn2.le
  have hu2 : ‖ρ⁻¹‖ ^ 2 = 1 / ‖ρ‖ ^ 2 := by rw [norm_inv, inv_pow, one_div]
  rw [hu2] at hb
  have hsn : 1 ≤ s ^ n := one_le_pow₀ hs1
  have hq : 0 ≤ 1 / ‖ρ‖ ^ 2 := le_of_lt (one_div_pos.mpr hn2)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (n : ℝ) * |ρ⁻¹.re| ≤ n * (3 / 2 * (1 / ‖ρ‖ ^ 2)) := mul_le_mul_of_nonneg_left hure hn0
  have hkey : 3 / 2 * (n : ℝ) + n ^ 2 * s ^ n ≤ 2 * ((n : ℝ) + 1) ^ 2 * s ^ n := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hsn), mul_nonneg (mul_nonneg hn0 hn0) (le_trans zero_le_one hsn),
      mul_nonneg hn0 (le_trans zero_le_one hsn)]
  have h4 := mul_le_mul_of_nonneg_right hkey hq
  unfold LiWeil.liTerm
  nlinarith

/-- The local count's sum `Σ m_ρ / (1 + |γ| ^ 2)` restricted to (V5')'s set is summable: the set injects into the carrier. -/
theorem summable_rest (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (s : ℝ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s} =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
  have h : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
    zero_sum_inv_sq_wide Z hc.1 hc.2
  have hG : Summable (Z.carrier.indicator (fun ρ : ℂ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))) :=
    (summable_subtype_iff_indicator (f := fun ρ : ℂ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
      (s := Z.carrier)).mp h
  have hS : Summable (fun ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s} =>
      Z.carrier.indicator (fun ρ : ℂ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) (ρ : ℂ)) :=
    hG.subtype (fun ρ : ℂ => ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s)
  exact hS.congr fun ρ => Set.indicator_of_mem ρ.2.1 _

/-- **(V5'), per point:** over the widened class with the exclusion, for `‖1 - ρ⁻¹‖ < s`, `1 < s`,
`|m_ρ Re (liTerm n ρ)| ≤ 2 (2 + 2 (1 + s) ^ 2) (n + 1) ^ 2 s ^ n · m_ρ / (1 + |γ| ^ 2)` -- LiRemainder.lean :125's constant. -/
theorem rest_term_le (Z : WideConfig) (hx : HExcl Z) {s : ℝ} (hs1 : 1 < s) (n : ℕ) {ρ : ℂ}
    (hmem : ρ ∈ Z.carrier) (hlt : ‖1 - ρ⁻¹‖ < s) :
    ‖(Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ ≤
      (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
        ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have hst := Z.strip ρ hmem
    have hρ0 : (ρ : ℂ) ≠ 0 := ne_zero_of_excl hx hmem
    have hb := Wide.liTerm_re_abs_le_pow hρ0 hst.1 hst.2 hs1.le hlt.le n
    have hn : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρ0
    have hn2 : 0 < ‖(ρ : ℂ)‖ ^ 2 := pow_pos hn 2
    have hinv : ‖(ρ : ℂ)⁻¹‖ < 1 + s := by
      calc ‖(ρ : ℂ)⁻¹‖ = ‖1 - (1 - (ρ : ℂ)⁻¹)‖ := by congr 1; ring
        _ ≤ ‖(1 : ℂ)‖ + ‖1 - (ρ : ℂ)⁻¹‖ := norm_sub_le _ _
        _ < 1 + s := by rw [norm_one]; linarith
    have hlow : 1 < (1 + s) * ‖(ρ : ℂ)‖ := by
      have h1 := mul_lt_mul_of_pos_right hinv hn
      rwa [norm_inv, inv_mul_cancel₀ hn.ne'] at h1
    have hlow2 : 1 < (1 + s) ^ 2 * ‖(ρ : ℂ)‖ ^ 2 := by nlinarith [hlow]
    have hγ : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 := by
      rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
      nlinarith [hst.1, hst.2]
    have hρsq : (ρ : ℂ).im ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (ρ : ℂ)) 2
      rwa [sq_abs] at this
    have hq0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
      have := Complex.normSq_nonneg (gammaOf (ρ : ℂ))
      linarith
    have key : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ (2 + 2 * (1 + s) ^ 2) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
      rw [div_le_div_iff₀ hn2 hq0]
      nlinarith [hγ, hρsq, hlow2]
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have hsn : (0 : ℝ) ≤ s ^ n := pow_nonneg (by linarith) n
    have hc2 : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 2 * s ^ n := mul_nonneg (by positivity) hsn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
    calc (Z.mult ρ : ℝ) * |(LiWeil.liTerm n ρ).re|
        ≤ (Z.mult ρ : ℝ) * (2 * ((n : ℝ) + 1) ^ 2 * s ^ n * (1 / ‖(ρ : ℂ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hm
      _ ≤ (Z.mult ρ : ℝ) * (2 * ((n : ℝ) + 1) ^ 2 * s ^ n *
            ((2 + 2 * (1 + s) ^ 2) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hc2) hm
      _ = (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
            ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring

/-- **(V5'):** over the widened class, under the local count and the exclusion, for `1 < s` the points with `‖1 - ρ⁻¹‖ < s`
contribute at most `C (n + 1) ^ 2 s ^ n` to the real part of the Li sum, `C = 2 (2 + 2 (1 + s) ^ 2) Σ m_ρ / (1 + |γ| ^ 2)` over that
set (LiRemainder.lean :175's statement and constant). -/
theorem remainder_le (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (hx : HExcl Z) {s : ℝ} (hs1 : 1 < s) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re| ≤
        C * ((n : ℝ) + 1) ^ 2 * s ^ n := by
  have hg := Wide.summable_rest Z hc s
  refine ⟨2 * (2 + 2 * (1 + s) ^ 2) * ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s},
    (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))), fun n => ?_⟩
  have hbound : ∀ ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, ‖(Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ ≤
      (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
        ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
    fun ρ => Wide.rest_term_le Z hx hs1 n ρ.2.1 ρ.2.2
  have hsumb := hg.mul_left (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n)
  calc |∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re|
      = ‖∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
          ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        tsum_of_norm_bounded hsumb.hasSum hbound
    _ = (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
          ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) :=
        tsum_mul_left
    _ = _ := by ring

end Wide
end Schema
end SIDEExplicitFormula
