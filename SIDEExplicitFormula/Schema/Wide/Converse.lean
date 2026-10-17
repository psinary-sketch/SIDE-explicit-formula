/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/Converse.lean
THIS PROGRAMME'S WORK (act b679, ruling (R289)(4)-(6); the plan relay data/b679_strip_plan.txt == 1-== 3, == 6) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE COMPOSITION' AND S5' OVER THE WIDENED CLASS: Schema/LiConverseCfg.lean's (V2), (V3) and (S5) with the configuration a
`WideConfig` and `Wide.HExcl` in place of `B321.HStrip`, and the coefficient `Wide.liCoeff`, LiCfg.lean :28's definition over the
widened class. Three steps change. (V2): `ρ ≠ 0` from the exclusion's half at `0` (LiConverseCfg.lean :57). (V3): `Re ρ > -1/2` gives
`(r ^ 2 - 1) ‖ρ‖ ^ 2 < 2`, so the window's bound is `2 / (r ^ 2 - 1)` (:94). (S5), `w ≠ 1` on the dominant set (:213-:232): `w = 1`
puts `x⁻¹ = 1 - R`, a real number, so `Im x = 0`, and the exclusion gives `0 < Re x`, against `Re x⁻¹ = 1 - R < 0` -- the step :231
closes by `Wide.HExcl` where v0.32 closed it by `0 < Re x`. The summability `Wide.liCoeff_summable` bounds each term by the widened
per-point bound at `s = 2` (LiCfg.lean :53's constant `9/4` is `3` here). (V4) is Schema/PowerSum.lean's, and `wD`,
`one_lt_norm_one_sub_inv` are LiConverseCfg.lean's, used as they stand. THE CONTROLS ((R289)(5)(v), the author's word): `c2Config`,
a point at the excluded `1 / (1 - R)` for `R = 5`, fails the exclusion (`c2_not_excl`), so S5' does not apply to it; `c2bConfig`,
the points `0` and `1`, has every coefficient nonnegative with `1` off the line (`c2b_nonneg_offline`), so the converse is false
without the exclusion's half at `0`. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Wide.Remainder
import SIDEExplicitFormula.Schema.LiConverseCfg

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Wide

open Zeta23

/-- **The Li coefficient over the widened class:** `(1/2) Σ' ρ ∈ Z, m_ρ Re (pairTerm n ρ)` (LiCfg.lean :28's form). -/
def liCoeff (Z : WideConfig) (n : ℕ) : ℝ :=
  (1 / 2) * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re

/-- **The summability, from the local count:** each term with `|Im ρ| ≥ 1` is at most `12 (n + 1) ^ 2 2 ^ n · m_ρ / (1 + |γ| ^ 2)`,
by the widened per-point bound at `s = 2` (`‖1 - ρ⁻¹‖ ≤ 1 + ‖ρ⁻¹‖ ≤ 2` for `‖ρ‖ ≥ 1`) and `1 + |γ| ^ 2 ≤ 3 ‖ρ‖ ^ 2` there. -/
theorem liCoeff_summable (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (n : ℕ) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re) := by
  have hg : Summable (fun ρ : Z.carrier =>
      (12 * ((n : ℝ) + 1) ^ 2 * 2 ^ n) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    (zero_sum_inv_sq Z hc.1 hc.2).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : (window Z (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (window Z (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hst := Z.strip _ hρmem
  have hnorm1 : 1 ≤ ‖(ρ : ℂ)‖ := him.trans (Complex.abs_im_le_norm _)
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro e
    rw [e, norm_zero] at hnorm1
    linarith
  have hn2 : 0 < ‖(ρ : ℂ)‖ ^ 2 := by positivity
  have hz : ‖1 - (ρ : ℂ)⁻¹‖ ≤ 2 := by
    have hi : ‖(ρ : ℂ)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hnorm1
    calc ‖1 - (ρ : ℂ)⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖(ρ : ℂ)⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hb := Wide.liTerm_re_abs_le_pow hρ0 hst.1 hst.2 (by norm_num : (1 : ℝ) ≤ 2) hz n
  have him2 : 1 ≤ (ρ : ℂ).im ^ 2 := by
    have := one_le_pow₀ (n := 2) him
    rwa [sq_abs] at this
  have hρsq : (ρ : ℂ).im ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (ρ : ℂ)) 2
    rwa [sq_abs] at this
  have hγ : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 := by
    rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    nlinarith [hst.1, hst.2]
  have hq0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (gammaOf (ρ : ℂ))
    linarith
  have key : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 3 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    rw [div_le_div_iff₀ hn2 hq0]
    linarith
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 2 * 2 ^ n := by positivity
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm, LiWeil.pairTerm_re, abs_mul, abs_two]
  calc (Z.mult ρ : ℝ) * (2 * |(LiWeil.liTerm n ρ).re|)
      ≤ (Z.mult ρ : ℝ) * (2 * (2 * ((n : ℝ) + 1) ^ 2 * 2 ^ n * (1 / ‖(ρ : ℂ)‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by norm_num)) hm
    _ ≤ (Z.mult ρ : ℝ) * (2 * (2 * ((n : ℝ) + 1) ^ 2 * 2 ^ n * (3 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hc2) (by norm_num)) hm
    _ = (12 * ((n : ℝ) + 1) ^ 2 * 2 ^ n) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring

/-! ## (V2') the orbit member, over the widened class -/

/-- **(V2'):** over the widened class with the exclusion, an off-line point has an orbit member under `ρ ↦ 1 - conj ρ` with
`1 < ‖1 - ρ′⁻¹‖` (LiConverseCfg.lean :53's statement; `ρ ≠ 0` from the exclusion). -/
theorem exists_dominant_point (Z : WideConfig) (hx : HExcl Z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hoff : ρ.re ≠ 1 / 2) : ∃ ρ' ∈ Z.carrier, 1 < ‖1 - ρ'⁻¹‖ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact ⟨ρ, hρ, one_lt_norm_one_sub_inv (ne_zero_of_excl hx hρ) hlt⟩
  · have hmem : Zeta23.reflect ρ ∈ Z.carrier := Z.reflect_mem ρ hρ
    refine ⟨Zeta23.reflect ρ, hmem, one_lt_norm_one_sub_inv (ne_zero_of_excl hx hmem) ?_⟩
    unfold Zeta23.reflect
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-! ## (V3') the dominant set is finite -/

/-- **(V3'):** for `1 < r`, the points of the widened class with `r ≤ ‖1 - ρ⁻¹‖` are finitely many: `r ‖ρ‖ ≤ ‖ρ - 1‖` and
`Re ρ > -1/2` give `(r ^ 2 - 1) ‖ρ‖ ^ 2 ≤ 2`, a bounded ordinate (LiConverseCfg.lean :72, the window's bound `2 / (r ^ 2 - 1)`). -/
theorem dominant_finite (Z : WideConfig) {r : ℝ} (hr : 1 < r) :
    {ρ : ℂ | ρ ∈ Z.carrier ∧ r ≤ ‖1 - ρ⁻¹‖}.Finite := by
  have hr2 : 0 < r ^ 2 - 1 := by nlinarith
  set K : ℝ := 2 / (r ^ 2 - 1) with hK
  have hKpos : 0 < K := by rw [hK]; exact div_pos (by norm_num) hr2
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
  have hbd : (r ^ 2 - 1) * ‖ρ‖ ^ 2 ≤ 2 := by nlinarith [hst.1]
  have him : ρ.im ^ 2 ≤ ‖ρ‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm ρ) 2
    rwa [sq_abs] at this
  have hK2 : ρ.im ^ 2 ≤ K := by
    rw [hK, le_div_iff₀ hr2]
    nlinarith
  exact ⟨hρ, by nlinarith [sq_nonneg (ρ.im + 1)], by nlinarith [sq_nonneg (ρ.im - 1)]⟩

/-! ## (S5') the split of the coefficient at the dominant set -/

/-- The points of `Z` at modulus `‖1 - ρ⁻¹‖ = R`. -/
def domSet (Z : WideConfig) (R : ℝ) : Set ℂ := {x | x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ = R}

theorem mem_domSet {Z : WideConfig} {R : ℝ} {x : ℂ} : x ∈ Wide.domSet Z R ↔ x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ = R := Iff.rfl

/-- The points of `Z` at modulus `‖1 - ρ⁻¹‖ < s`: (V5')'s set. -/
def restSet (Z : WideConfig) (s : ℝ) : Set ℂ := {x | x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ < s}

theorem mem_restSet {Z : WideConfig} {s : ℝ} {x : ℂ} : x ∈ Wide.restSet Z s ↔ x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ < s := Iff.rfl

/-- The coefficient's term at a point of `ℂ`: `m_x Re (liTerm n x)`. -/
def gL (Z : WideConfig) (n : ℕ) (x : ℂ) : ℝ := (Z.mult x : ℝ) * (LiWeil.liTerm n x).re

/-- The coefficient as a sum over `ℂ`: `liCoeff Z n = Σ' x, 1_Z(x) m_x Re (liTerm n x)` (`pairTerm_re`). -/
theorem liCoeff_eq_indicator (Z : WideConfig) (n : ℕ) :
    Wide.liCoeff Z n = ∑' x : ℂ, Z.carrier.indicator (Wide.gL Z n) x := by
  have h : (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re) =
      fun ρ : Z.carrier => 2 * Wide.gL Z n ρ := by
    funext ρ
    rw [LiWeil.pairTerm_re, Wide.gL]
    ring
  rw [Wide.liCoeff, h, tsum_mul_left, ← tsum_subtype Z.carrier (Wide.gL Z n)]
  ring

/-- The summability of the coefficient's terms over `ℂ`, from `liCoeff_summable`. -/
theorem summable_indicator_gL (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (n : ℕ) :
    Summable (Z.carrier.indicator (Wide.gL Z n)) := by
  have hsub : Summable (fun ρ : Z.carrier => Wide.gL Z n ρ) :=
    ((Wide.liCoeff_summable Z hc n).mul_left (1 / 2)).congr fun ρ => by
      rw [LiWeil.pairTerm_re, Wide.gL]
      ring
  exact (summable_subtype_iff_indicator (f := Wide.gL Z n) (s := Z.carrier)).mp hsub

/-- The dominant part: `Σ_D m_x Re (liTerm n x) = Σ_D m_x - R ^ n Re (Σ_D m_x w_x ^ n)` for `R ≠ 0`. -/
theorem sum_gL_dom (Z : WideConfig) (D : Finset ℂ) {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    ∑ x ∈ D, Wide.gL Z n x = ∑ x ∈ D, (Z.mult x : ℝ) - R ^ n * (∑ x ∈ D, (Z.mult x : ℂ) * wD R x ^ n).re := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hz : 1 - x⁻¹ = wD R x * (R : ℂ) := (div_mul_cancel₀ (1 - x⁻¹) hRC).symm
  rw [Wide.gL, LiWeil.liTerm, hz, mul_pow, ← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero]
  ring

/-! ## (S5') the converse over the widened class -/

/-- **The converse over the widened class (S5'):** for a configuration in the open strip `(-1/2, 3/2)` with no real point in
`(-1/2, 0]`, under the local count, `0 ≤ liCoeff Z n` for every `n` puts every point of `Z` on the line. -/
theorem li_nonneg_cfg_imp_online (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (hex : HExcl Z) :
    (∀ n : ℕ, 0 ≤ liCoeff Z n) → ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  intro hnn
  by_contra hno
  push_neg at hno
  obtain ⟨ρ1, hρ1, hoff⟩ := hno
  -- (V2'): a point of modulus above `1`; (V3'): finitely many at or above `r`
  obtain ⟨ρ', hρ', hr0⟩ := Wide.exists_dominant_point Z hex hρ1 hoff
  obtain ⟨r, hr1, hrr0⟩ : ∃ r : ℝ, 1 < r ∧ r < ‖1 - ρ'⁻¹‖ :=
    ⟨(1 + ‖1 - ρ'⁻¹‖) / 2, by linarith, by linarith⟩
  have hF := Wide.dominant_finite Z hr1
  -- the dominant modulus `R`
  obtain ⟨ρm, hρm, hmax⟩ := Set.exists_max_image _ (fun x : ℂ => ‖1 - x⁻¹‖) hF ⟨ρ', hρ', hrr0.le⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖1 - ρm⁻¹‖ := ⟨_, rfl⟩
  have hR0le : ‖1 - ρ'⁻¹‖ ≤ R := by
    rw [hRdef]
    exact hmax ρ' ⟨hρ', hrr0.le⟩
  have hrR : r < R := lt_of_lt_of_le hrr0 hR0le
  have hR1 : 1 < R := by linarith
  have hR0 : 0 < R := by linarith
  have hRne : R ≠ 0 := hR0.ne'
  have hRmax : ∀ x ∈ Z.carrier, r ≤ ‖1 - x⁻¹‖ → ‖1 - x⁻¹‖ ≤ R := by
    intro x hx h
    rw [hRdef]
    exact hmax x ⟨hx, h⟩
  -- a modulus `s` strictly between the next modulus and `R`
  have hs1ex : ∃ s1 : ℝ, s1 < R ∧ r ≤ s1 ∧
      ∀ x ∈ Z.carrier, r ≤ ‖1 - x⁻¹‖ → ‖1 - x⁻¹‖ < R → ‖1 - x⁻¹‖ ≤ s1 := by
    by_cases hG : ({x : ℂ | x ∈ Z.carrier ∧ r ≤ ‖1 - x⁻¹‖ ∧ ‖1 - x⁻¹‖ < R}).Nonempty
    · obtain ⟨x2, hx2, hmax2⟩ := Set.exists_max_image _ (fun x : ℂ => ‖1 - x⁻¹‖)
        (hF.subset fun x hx => ⟨hx.1, hx.2.1⟩) hG
      exact ⟨max ‖1 - x2⁻¹‖ r, max_lt hx2.2.2 hrR, le_max_right _ _,
        fun x hx h1 h2 => (hmax2 x ⟨hx, h1, h2⟩).trans (le_max_left _ _)⟩
    · exact ⟨r, hrR, le_rfl, fun x hx h1 h2 => (hG ⟨x, hx, h1, h2⟩).elim⟩
  obtain ⟨s1, hs1R, hrs1, hs1max⟩ := hs1ex
  obtain ⟨s, hs1s, hsR⟩ : ∃ s : ℝ, s1 < s ∧ s < R := ⟨(s1 + R) / 2, by linarith, by linarith⟩
  have hs1 : 1 < s := by linarith
  have hlts : ∀ x ∈ Z.carrier, ‖1 - x⁻¹‖ ≠ R → ‖1 - x⁻¹‖ < s := by
    intro x hx hne
    by_cases hxr : r ≤ ‖1 - x⁻¹‖
    · have h1 := hRmax x hx hxr
      have h2 := hs1max x hx hxr (lt_of_le_of_ne h1 hne)
      linarith
    · push_neg at hxr
      linarith
  -- the dominant set `D`, finite and nonempty
  have hDfin : (Wide.domSet Z R).Finite :=
    hF.subset fun x hx => ⟨(Wide.mem_domSet.mp hx).1, by rw [(Wide.mem_domSet.mp hx).2]; exact hrR.le⟩
  obtain ⟨DF, hDF⟩ : ∃ DF : Finset ℂ, ∀ x, x ∈ DF ↔ x ∈ Wide.domSet Z R :=
    ⟨hDfin.toFinset, fun x => hDfin.mem_toFinset⟩
  have hDne : DF.Nonempty := ⟨ρm, (hDF ρm).mpr (Wide.mem_domSet.mpr ⟨hρm.1, hRdef.symm⟩)⟩
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRne
  have hwn : ∀ x ∈ DF, ‖wD R x‖ = 1 := by
    intro x hx
    have hxD := Wide.mem_domSet.mp ((hDF x).mp hx)
    rw [wD, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, hxD.2, div_self hRne]
  -- `w ≠ 1` on `D`: `w = 1` makes `x` real and negative, which the exclusion forbids (LiConverseCfg.lean :213-:232's step)
  have hw1 : ∀ x ∈ DF, wD R x ≠ 1 := by
    intro x hx h
    have hxD := Wide.mem_domSet.mp ((hDF x).mp hx)
    have hx0 : x ≠ 0 := ne_zero_of_excl hex hxD.1
    have h2 : 1 - x⁻¹ = (R : ℂ) := by
      rw [wD, div_eq_one_iff_eq hRC] at h
      exact h
    have h3 : x⁻¹.re = 1 - R := by
      have := congrArg Complex.re h2
      rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at this
      linarith
    have h5 : x⁻¹.im = 0 := by
      have := congrArg Complex.im h2
      rw [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at this
      linarith
    have h6 : x.im = 0 := by
      rw [Complex.inv_im, div_eq_zero_iff] at h5
      rcases h5 with h5 | h5
      · linarith
      · exact absurd h5 (Complex.normSq_pos.mpr hx0).ne'
    have h4 : 0 < x⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos (hex x hxD.1 h6) (Complex.normSq_pos.mpr hx0)
    linarith
  have hinj : Set.InjOn (wD R) DF := by
    intro a _ b _ h
    have h2 : 1 - a⁻¹ = 1 - b⁻¹ := by
      have ha : 1 - a⁻¹ = wD R a * (R : ℂ) := (div_mul_cancel₀ (1 - a⁻¹) hRC).symm
      have hb : 1 - b⁻¹ = wD R b * (R : ℂ) := (div_mul_cancel₀ (1 - b⁻¹) hRC).symm
      rw [ha, hb, h]
    exact inv_injective (sub_right_injective h2)
  have hm1 : ∀ x ∈ DF, 1 ≤ Z.mult x := fun x hx => Z.one_le_mult x (Wide.mem_domSet.mp ((hDF x).mp hx)).1
  obtain ⟨hB, hQ, _⟩ := powerSum_consts DF Z.mult hDne hm1
  have hc0 : 0 < (∑ x ∈ DF, (Z.mult x : ℝ) ^ 2) / (4 * ∑ x ∈ DF, (Z.mult x : ℝ)) := div_pos hQ (by linarith)
  -- (V5') on the rest
  obtain ⟨C, hC⟩ := Wide.remainder_le Z hc hex hs1
  -- the bound's ratio to `R ^ n` tends to `0`
  have hq1 : (0 : ℝ) ≤ 1 / R := (one_div_pos.mpr hR0).le
  have hq1' : 1 / R < 1 := (div_lt_one hR0).mpr hR1
  have hq2 : (0 : ℝ) ≤ s / R := (div_pos (by linarith) hR0).le
  have hq2' : s / R < 1 := (div_lt_one hR0).mpr hsR
  have hq2a : |s / R| < 1 := by rw [abs_of_nonneg hq2]; exact hq2'
  have hT1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq1 hq1').const_mul (∑ x ∈ DF, (Z.mult x : ℝ))
  have hT2 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hq2a).const_mul C
  have hT3 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq2a).const_mul (2 * C)
  have hT4 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq2 hq2').const_mul C
  have hT := ((hT1.add hT2).add hT3).add hT4
  simp only [mul_zero, add_zero] at hT
  obtain ⟨Nq, hNq⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hc0))
  -- (V4+) at some `n ≥ Nq`
  obtain ⟨n, hn, hX⟩ := powerSum_re_ge_infinitely DF (wD R) Z.mult hDne hwn hw1 hinj hm1 Nq
  have hlt : (∑ x ∈ DF, (Z.mult x : ℝ)) * (1 / R) ^ n + C * ((n : ℝ) ^ 2 * (s / R) ^ n) +
      2 * C * ((n : ℝ) ^ 1 * (s / R) ^ n) + C * (s / R) ^ n <
        (∑ x ∈ DF, (Z.mult x : ℝ) ^ 2) / (4 * ∑ x ∈ DF, (Z.mult x : ℝ)) := hNq n hn
  -- the split of the coefficient at `D`
  have hdec : ∀ x, Z.carrier.indicator (Wide.gL Z n) x =
      (Wide.domSet Z R).indicator (Wide.gL Z n) x + (Wide.restSet Z s).indicator (Wide.gL Z n) x := by
    intro x
    by_cases hx : x ∈ Z.carrier
    · by_cases hxD : ‖1 - x⁻¹‖ = R
      · have hxR : ¬ (‖1 - x⁻¹‖ < s) := by
          rw [hxD]
          exact not_lt.mpr hsR.le
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Wide.mem_domSet.mpr ⟨hx, hxD⟩),
          Set.indicator_of_notMem (fun h => hxR (Wide.mem_restSet.mp h).2), add_zero]
      · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (fun h => hxD (Wide.mem_domSet.mp h).2),
          Set.indicator_of_mem (Wide.mem_restSet.mpr ⟨hx, hlts x hx hxD⟩), zero_add]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (Wide.mem_domSet.mp h).1),
        Set.indicator_of_notMem (fun h => hx (Wide.mem_restSet.mp h).1), add_zero]
  have hsumC := Wide.summable_indicator_gL Z hc n
  have hD0 : ∀ x ∉ DF, (Wide.domSet Z R).indicator (Wide.gL Z n) x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx ((hDF x).mpr h)) _
  have hsumD : Summable ((Wide.domSet Z R).indicator (Wide.gL Z n)) := summable_of_ne_finset_zero hD0
  have hsubR : Wide.restSet Z s ⊆ Z.carrier := fun x hx => (Wide.mem_restSet.mp hx).1
  have hsumR : Summable ((Wide.restSet Z s).indicator (Wide.gL Z n)) := by
    have := hsumC.indicator (Wide.restSet Z s)
    rwa [Set.indicator_indicator, Set.inter_eq_left.mpr hsubR] at this
  have htD : ∑' x, (Wide.domSet Z R).indicator (Wide.gL Z n) x = ∑ x ∈ DF, Wide.gL Z n x := by
    rw [tsum_eq_sum hD0]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem ((hDF x).mp hx) _
  have htR : ∑' x, (Wide.restSet Z s).indicator (Wide.gL Z n) x =
      ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re :=
    (tsum_subtype (Wide.restSet Z s) (Wide.gL Z n)).symm
  have hsplit : Wide.liCoeff Z n = ∑ x ∈ DF, Wide.gL Z n x +
      ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re := by
    rw [Wide.liCoeff_eq_indicator, tsum_congr hdec, Summable.tsum_add hsumD hsumR, htD, htR]
  -- the composition: `0 ≤ λ_n ≤ Σ_D m - c R ^ n + C (n + 1) ^ 2 s ^ n < 0`
  have hRest := (abs_le.mp (hC n)).2
  have hRn : 0 < R ^ n := pow_pos hR0 n
  have hX' := mul_le_mul_of_nonneg_left hX hRn.le
  have e1 : R ^ n * (1 / R) ^ n = 1 := by rw [← mul_pow, mul_one_div_cancel hRne, one_pow]
  have e2 : R ^ n * (s / R) ^ n = s ^ n := by
    rw [← mul_pow, show R * (s / R) = s by field_simp]
  have hmul := mul_lt_mul_of_pos_left hlt hRn
  have hexp : R ^ n * ((∑ x ∈ DF, (Z.mult x : ℝ)) * (1 / R) ^ n + C * ((n : ℝ) ^ 2 * (s / R) ^ n) +
      2 * C * ((n : ℝ) ^ 1 * (s / R) ^ n) + C * (s / R) ^ n) =
      (∑ x ∈ DF, (Z.mult x : ℝ)) * (R ^ n * (1 / R) ^ n) + C * ((n : ℝ) + 1) ^ 2 * (R ^ n * (s / R) ^ n) := by
    ring
  rw [hexp, e1, e2] at hmul
  have h0 := hnn n
  rw [hsplit, Wide.sum_gL_dom Z DF hRne n] at h0
  linarith

/-! ## The controls ((R289)(5)(v) and the author's word): one on the hypothesis, one on the theorem -/

/-- `reflect` on a real point: `reflect a = 1 - a`. -/
theorem reflect_ofReal (a : ℝ) : Zeta23.reflect (a : ℂ) = ((1 - a : ℝ) : ℂ) :=
  Complex.ext (by simp [Zeta23.reflect]) (by simp [Zeta23.reflect])

/-- **C2, the control on the hypothesis:** the points `-1/4 = 1 / (1 - 5)` (the excluded point at `R = 5`) and its reflection
`5/4`, multiplicity `1`. -/
def c2Config : WideConfig where
  carrier := {((-1 / 4 : ℝ) : ℂ), ((5 / 4 : ℝ) : ℂ)}
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_refl 1
  strip := by
    intro ρ hρ
    rcases hρ with rfl | rfl <;> norm_num
  reflect_mem := by
    intro ρ hρ
    rcases hρ with rfl | rfl <;> rw [reflect_ofReal] <;> norm_num
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Set.finite_insert.mpr (Set.finite_singleton _)).subset Set.inter_subset_left

/-- **C2 fails the exclusion:** `-1/4` is a real point of the carrier with negative real part, so S5' does not apply to it. -/
theorem c2_not_excl : ¬ HExcl c2Config := by
  intro h
  have hmem : ((-1 / 4 : ℝ) : ℂ) ∈ c2Config.carrier := Set.mem_insert _ _
  have := h ((-1 / 4 : ℝ) : ℂ) hmem (Complex.ofReal_im _)
  rw [Complex.ofReal_re] at this
  norm_num at this

/-- **C2b, the control on the theorem:** the points `0` and `1 = reflect 0`, multiplicity `1`. -/
def c2bConfig : WideConfig where
  carrier := {((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)}
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_refl 1
  strip := by
    intro ρ hρ
    rcases hρ with rfl | rfl <;> norm_num
  reflect_mem := by
    intro ρ hρ
    rcases hρ with rfl | rfl <;> rw [reflect_ofReal] <;> norm_num
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Set.finite_insert.mpr (Set.finite_singleton _)).subset Set.inter_subset_left

/-- **C2b: every coefficient nonnegative, a point off the line** -- in Lean's convention `0⁻¹ = 0`, `liTerm n 0 = 0` and
`liTerm n 1 = 1 - 0 ^ n ≥ 0`, while `Re 1 ≠ 1/2`: the converse is false without the exclusion's half at `0`. -/
theorem c2b_nonneg_offline :
    (∀ n : ℕ, 0 ≤ liCoeff c2bConfig n) ∧ ∃ ρ ∈ c2bConfig.carrier, ρ.re ≠ 1 / 2 := by
  refine ⟨fun n => ?_, ((1 : ℝ) : ℂ), Set.mem_insert_of_mem _ (Set.mem_singleton _), by norm_num⟩
  unfold liCoeff
  refine mul_nonneg (by norm_num) (tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) ?_)
  rcases Set.mem_insert_iff.mp ρ.2 with h | h
  · rw [LiWeil.pairTerm_re, h]
    simp [LiWeil.liTerm]
  · rw [LiWeil.pairTerm_re, Set.mem_singleton_iff.mp h]
    cases n with
    | zero => simp [LiWeil.liTerm]
    | succ k => simp [LiWeil.liTerm]

end Wide
end Schema
end SIDEExplicitFormula
