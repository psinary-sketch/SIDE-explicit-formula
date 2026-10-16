/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/LiRemainder.lean
THIS PROGRAMME'S WORK (act b673, ruling (R283)(3)-(5); the plan relay data/b673_v4v5_plan.txt == 3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(V5) THE REMAINDER OFF THE DOMINANT SET, two-sided, as the composition consumes it: for `1 < s`, under the local count and the
open strip, the points with `‖1 - ρ⁻¹‖ < s` contribute at most `C (n + 1) ^ 2 s ^ n` in absolute value to `Σ m_ρ Re (liTerm n ρ)`
(`remainder_le`, moved here from Schema/LiConverseCfg.lean at b673, its statement unchanged). The proof: with `u = ρ⁻¹` and
`z = 1 - u`, `1 - z ^ n = n u - u ^ 2 Σ_{j<n} Σ_{l<j} z ^ l` (`one_sub_pow_expand`, two geometric sums); `|Re u| ≤ 1 / ‖ρ‖ ^ 2`
in the strip and `‖z‖ < s`, so `|Re (liTerm n ρ)| ≤ 2 (n + 1) ^ 2 s ^ n / ‖ρ‖ ^ 2` (`liTerm_re_abs_le_pow`); `‖u‖ ≤ 1 + ‖z‖`
bounds `‖ρ‖` below by `1 / (1 + s)`, so `1 / ‖ρ‖ ^ 2 ≤ (2 + 2 (1 + s) ^ 2) / (1 + |γ| ^ 2)`, and the local count sums
`m_ρ / (1 + |γ| ^ 2)` (`WeilEF.zero_sum_inv_sq_gen`). The plan's split at `‖ρ‖ = R0` is not needed: the bound holds at every
point of the set. Nothing here proves GRH or RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.LiCfg

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open Zeta23

/-- `1 - (1 - u) ^ n = n u - u ^ 2 Σ_{j<n} Σ_{l<j} (1 - u) ^ l`. -/
theorem one_sub_pow_expand (u : ℂ) (n : ℕ) :
    1 - (1 - u) ^ n = ((n : ℝ) : ℂ) * u - u ^ 2 * ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l := by
  have hg : ∀ j : ℕ, 1 - (1 - u) ^ j = u * ∑ l ∈ Finset.range j, (1 - u) ^ l := by
    intro j
    have := geom_sum_mul (1 - u) j
    linear_combination this
  have h2 : ∑ j ∈ Finset.range n, (1 - u) ^ j =
      (n : ℂ) - u * ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l := by
    rw [Finset.mul_sum, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    have hc : ∀ j ∈ Finset.range n, (1 - u) ^ j + u * ∑ l ∈ Finset.range j, (1 - u) ^ l = 1 := by
      intro j _
      rw [← hg j]
      ring
    rw [Finset.sum_congr rfl hc]
    simp
  rw [hg n, h2]
  push_cast
  ring

/-- The double geometric sum, bounded: for `‖1 - u‖ ≤ s` and `1 ≤ s`, `‖Σ_{j<n} Σ_{l<j} (1 - u) ^ l‖ ≤ n ^ 2 s ^ n`. -/
theorem norm_double_geom_le (u : ℂ) {s : ℝ} (hs1 : 1 ≤ s) (hz : ‖1 - u‖ ≤ s) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l‖ ≤ (n : ℝ) ^ 2 * s ^ n := by
  have hsn : (0 : ℝ) ≤ s ^ n := pow_nonneg (by linarith) n
  have hterm : ∀ j ∈ Finset.range n, ‖∑ l ∈ Finset.range j, (1 - u) ^ l‖ ≤ (n : ℝ) * s ^ n := by
    intro j hj
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l ∈ Finset.range j, ‖(1 - u) ^ l‖ ≤ ∑ l ∈ Finset.range j, s ^ n := Finset.sum_le_sum fun l hl => by
          rw [norm_pow]
          have hl' : l ≤ n := (Finset.mem_range.mp hl).le.trans hjn
          exact (pow_le_pow_left₀ (norm_nonneg _) hz l).trans (pow_le_pow_right₀ hs1 hl')
      _ = (j : ℝ) * s ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (n : ℝ) * s ^ n := mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) hsn
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range n, ‖∑ l ∈ Finset.range j, (1 - u) ^ l‖ ≤ ∑ j ∈ Finset.range n, (n : ℝ) * s ^ n :=
        Finset.sum_le_sum hterm
    _ = (n : ℝ) ^ 2 * s ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `|Re (1 - (1 - u) ^ n)| ≤ n |Re u| + ‖u‖ ^ 2 n ^ 2 s ^ n` for `‖1 - u‖ ≤ s`, `1 ≤ s`. -/
theorem re_one_sub_pow_abs_le (u : ℂ) {s : ℝ} (hs1 : 1 ≤ s) (hz : ‖1 - u‖ ≤ s) (n : ℕ) :
    |(1 - (1 - u) ^ n).re| ≤ (n : ℝ) * |u.re| + ‖u‖ ^ 2 * ((n : ℝ) ^ 2 * s ^ n) := by
  rw [one_sub_pow_expand, Complex.sub_re, Complex.re_ofReal_mul]
  have h1 : |(n : ℝ) * u.re| = (n : ℝ) * |u.re| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have h2 : |(u ^ 2 * ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l).re| ≤ ‖u‖ ^ 2 * ((n : ℝ) ^ 2 * s ^ n) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_double_geom_le u hs1 hz n) (by positivity)
  have ha := le_abs_self ((n : ℝ) * u.re)
  have hb := neg_abs_le ((n : ℝ) * u.re)
  have hc := le_abs_self (u ^ 2 * ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l).re
  have hd := neg_abs_le (u ^ 2 * ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range j, (1 - u) ^ l).re
  rw [abs_le]
  constructor <;> linarith

/-- **The term, bounded off the dominant set:** in the open strip, for `‖1 - ρ⁻¹‖ ≤ s` and `1 ≤ s`,
`|Re (liTerm n ρ)| ≤ 2 (n + 1) ^ 2 s ^ n (1 / ‖ρ‖ ^ 2)`. -/
theorem liTerm_re_abs_le_pow {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {s : ℝ} (hs1 : 1 ≤ s) (hz : ‖1 - ρ⁻¹‖ ≤ s)
    (n : ℕ) : |(LiWeil.liTerm n ρ).re| ≤ 2 * ((n : ℝ) + 1) ^ 2 * s ^ n * (1 / ‖ρ‖ ^ 2) := by
  have hρ0 : ρ ≠ 0 := by
    intro e
    rw [e, Complex.zero_re] at h0
    exact lt_irrefl _ h0
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hn2 : 0 < ‖ρ‖ ^ 2 := pow_pos hn 2
  have hb := re_one_sub_pow_abs_le ρ⁻¹ hs1 hz n
  have hure : |ρ⁻¹.re| ≤ 1 / ‖ρ‖ ^ 2 := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq, abs_div, abs_of_pos hn2, abs_of_pos h0]
    exact div_le_div_of_nonneg_right h1.le hn2.le
  have hu2 : ‖ρ⁻¹‖ ^ 2 = 1 / ‖ρ‖ ^ 2 := by rw [norm_inv, inv_pow, one_div]
  rw [hu2] at hb
  have hsn : 1 ≤ s ^ n := one_le_pow₀ hs1
  have hq : 0 ≤ 1 / ‖ρ‖ ^ 2 := le_of_lt (one_div_pos.mpr hn2)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (n : ℝ) * |ρ⁻¹.re| ≤ n * (1 / ‖ρ‖ ^ 2) := mul_le_mul_of_nonneg_left hure hn0
  have hkey : (n : ℝ) + n ^ 2 * s ^ n ≤ 2 * ((n : ℝ) + 1) ^ 2 * s ^ n := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hsn), mul_nonneg (mul_nonneg hn0 hn0) (le_trans zero_le_one hsn),
      mul_nonneg hn0 (le_trans zero_le_one hsn)]
  have h4 := mul_le_mul_of_nonneg_right hkey hq
  unfold LiWeil.liTerm
  nlinarith

/-- **(V5):** for `1 < s`, the points with `‖1 - ρ⁻¹‖ < s` contribute at most `C (n + 1) ^ 2 s ^ n` to the real part of the
Li sum, under the local count and the open strip. -/
theorem remainder_le (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (hs : B321.HStrip Z) {s : ℝ} (hs1 : 1 < s) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re| ≤
        C * ((n : ℝ) + 1) ^ 2 * s ^ n := by
  let e : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s} → Z.carrier := fun ρ => ⟨ρ.1, ρ.2.1⟩
  have he : Function.Injective e := fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hg : Summable (fun ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s} =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
    (WeilEF.zero_sum_inv_sq_gen Z hc.1 hc.2).comp_injective he
  refine ⟨2 * (2 + 2 * (1 + s) ^ 2) * ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s},
    (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))), fun n => ?_⟩
  have hbound : ∀ ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, ‖(Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ ≤
      (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
        ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    intro ρ
    have hmem : (ρ : ℂ) ∈ Z.carrier := ρ.2.1
    have hlt : ‖1 - (ρ : ℂ)⁻¹‖ < s := ρ.2.2
    have hst : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := hs _ hmem
    have hb := liTerm_re_abs_le_pow hst.1 hst.2 hs1.le hlt.le n
    have hρ0 : (ρ : ℂ) ≠ 0 := by
      intro h
      have := hst.1
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
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
    have hstc := Z.strip _ hmem
    have hγ : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
      rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
      nlinarith [hstc.1, hstc.2]
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

end Schema
end SIDEExplicitFormula
