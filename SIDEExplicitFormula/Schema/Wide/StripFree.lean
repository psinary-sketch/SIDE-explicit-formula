/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/StripFree.lean
THIS PROGRAMME'S WORK (act b689, ruling (R299)(3)-(4); the plan relay data/b689_plan.txt == 1-== 6) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE STRIP-FREE FORM OF THE LI CONVERSE OVER THE WIDENED CLASS (S5''): Schema/Wide/Converse.lean's S5' with the exclusion `Wide.HExcl`
replaced by `ρ ≠ 0` for every point (HExcl's half at `0`; its half on `(-1/2, 0)` dropped), and the dominant set split at `w = 1` in
place of the step that half closed (relay data/b679_strip_plan.txt section 11). By injectivity of `w` on the dominant set at most one
point has `w = 1`; there `Re Σ m wⁿ` gains that point's multiplicity at every `n`, and (V4) on the rest gives the bound past every `N`
(`powerSum_re_ge_split`). The remainder (V5'') and the orbit member (V2'') are v0.33's widened copies with `ρ ≠ 0` read from the
hypothesis; everything else is v0.33's, used as it stands. THE CONTROLS: `c2Config`, the configuration with a real point at `-1/4`
that v0.33 excluded, meets the hypothesis, sits at `w = 1` and has a negative first coefficient (`c3_real_segment`); `c2bConfig`, the
points `0` and `1`, fails the hypothesis at `0` while every coefficient is nonnegative with `1` off the line (`c2b_lesson`): the
exclusion of `0` is necessary, and it lives in this hypothesis. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Wide.Converse

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Wide

open Zeta23

/-! ## (V5'') the remainder with `ρ ≠ 0` for every point -/

/-- **(V5''), per point:** Remainder.lean's `rest_term_le` with `ρ ≠ 0` read from the hypothesis in place of the exclusion. -/
theorem rest_term_le_ne_zero (Z : WideConfig) (hnz : ∀ ρ ∈ Z.carrier, ρ ≠ 0) {s : ℝ} (hs1 : 1 < s) (n : ℕ) {ρ : ℂ}
    (hmem : ρ ∈ Z.carrier) (hlt : ‖1 - ρ⁻¹‖ < s) :
    ‖(Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ ≤
      (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
        ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have hst := Z.strip ρ hmem
    have hρ0 : (ρ : ℂ) ≠ 0 := hnz ρ hmem
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

/-- **(V5''):** Remainder.lean's `remainder_le` with `ρ ≠ 0` for every point in place of the exclusion; the same witness and constant. -/
theorem remainder_le_ne_zero (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (hnz : ∀ ρ ∈ Z.carrier, ρ ≠ 0) {s : ℝ} (hs1 : 1 < s) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re| ≤
        C * ((n : ℝ) + 1) ^ 2 * s ^ n := by
  have hg := Wide.summable_rest Z hc s
  refine ⟨2 * (2 + 2 * (1 + s) ^ 2) * ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s},
    (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))), fun n => ?_⟩
  have hbound : ∀ ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, ‖(Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re‖ ≤
      (2 * (2 + 2 * (1 + s) ^ 2) * ((n : ℝ) + 1) ^ 2 * s ^ n) *
        ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
    fun ρ => Wide.rest_term_le_ne_zero Z hnz hs1 n ρ.2.1 ρ.2.2
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

/-! ## (V2'') the orbit member with `ρ ≠ 0` for every point -/

/-- **(V2''):** Converse.lean's `exists_dominant_point` with `ρ ≠ 0` read from the hypothesis in place of the exclusion. -/
theorem exists_dominant_point_ne_zero (Z : WideConfig) (hnz : ∀ ρ ∈ Z.carrier, ρ ≠ 0) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hoff : ρ.re ≠ 1 / 2) : ∃ ρ' ∈ Z.carrier, 1 < ‖1 - ρ'⁻¹‖ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact ⟨ρ, hρ, one_lt_norm_one_sub_inv (hnz ρ hρ) hlt⟩
  · have hmem : Zeta23.reflect ρ ∈ Z.carrier := Z.reflect_mem ρ hρ
    refine ⟨Zeta23.reflect ρ, hmem, one_lt_norm_one_sub_inv (hnz _ hmem) ?_⟩
    unfold Zeta23.reflect
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-! ## (V4'') the power sum split at `w = 1` -/

/-- **(V4''), the split at `w = 1`:** for a nonempty finite set on which `w` is injective and unimodular and the multiplicities are at
least `1`, some `c > 0` is at most `Re Σ m wⁿ` for arbitrarily large `n` -- with no hypothesis `w ≠ 1`. At most one point `x₁` has
`w x₁ = 1` (injectivity); it adds `m x₁` at every `n`, and (V4) on the rest gives its bound past every `N` (`c = 1` if the rest is
empty). Where no point has `w = 1`, this is (V4) itself. -/
theorem powerSum_re_ge_split (s : Finset ℂ) (w : ℂ → ℂ) (m : ℂ → ℕ) (hs : s.Nonempty) (hw : ∀ x ∈ s, ‖w x‖ = 1)
    (hinj : Set.InjOn w s) (hm : ∀ x ∈ s, 1 ≤ m x) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, c ≤ (∑ x ∈ s, (m x : ℂ) * w x ^ n).re := by
  classical
  by_cases h1 : ∃ x₁ ∈ s, w x₁ = 1
  · obtain ⟨x₁, hx₁, hw₁⟩ := h1
    have hsplit : ∀ n : ℕ, (∑ x ∈ s, (m x : ℂ) * w x ^ n).re =
        (m x₁ : ℝ) + (∑ x ∈ s.erase x₁, (m x : ℂ) * w x ^ n).re := by
      intro n
      have he := Finset.add_sum_erase s (fun x => (m x : ℂ) * w x ^ n) hx₁
      rw [← he]
      simp only [Complex.add_re, hw₁, one_pow, mul_one, Complex.natCast_re]
    have hw1' : ∀ x ∈ s.erase x₁, w x ≠ 1 := by
      intro x hx h
      exact Finset.ne_of_mem_erase hx
        (hinj (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hx)) (Finset.mem_coe.mpr hx₁) (h.trans hw₁.symm))
    by_cases hE : (s.erase x₁).Nonempty
    · have hmE : ∀ x ∈ s.erase x₁, 1 ≤ m x := fun x hx => hm x (Finset.mem_of_mem_erase hx)
      obtain ⟨hP, hQ, _⟩ := powerSum_consts (s.erase x₁) m hE hmE
      refine ⟨(∑ x ∈ s.erase x₁, (m x : ℝ) ^ 2) / (4 * ∑ x ∈ s.erase x₁, (m x : ℝ)), div_pos hQ (by linarith), fun N => ?_⟩
      obtain ⟨n, hn, hX⟩ := powerSum_re_ge_infinitely (s.erase x₁) w m hE (fun x hx => hw x (Finset.mem_of_mem_erase hx)) hw1'
        (hinj.mono (Finset.coe_subset.mpr (Finset.erase_subset x₁ s))) hmE N
      refine ⟨n, hn, ?_⟩
      rw [hsplit n]
      have h0 : (0 : ℝ) ≤ m x₁ := Nat.cast_nonneg _
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      refine ⟨1, one_pos, fun N => ⟨N, le_rfl, ?_⟩⟩
      rw [hsplit N, hE, Finset.sum_empty, Complex.zero_re, add_zero]
      exact_mod_cast hm x₁ hx₁
  · push_neg at h1
    obtain ⟨hP, hQ, _⟩ := powerSum_consts s m hs hm
    exact ⟨(∑ x ∈ s, (m x : ℝ) ^ 2) / (4 * ∑ x ∈ s, (m x : ℝ)), div_pos hQ (by linarith),
      powerSum_re_ge_infinitely s w m hs hw h1 hinj hm⟩

/-! ## (S5'') the converse with `ρ ≠ 0` for every point -/

/-- **The strip-free converse over the widened class (S5''):** for a configuration in the open strip `(-1/2, 3/2)` with no point at `0`,
under the local count, `0 ≤ liCoeff Z n` for every `n` puts every point of `Z` on the line. Converse.lean's S5' with the exclusion's half on
`(-1/2, 0)` dropped and the dominant set split at `w = 1` (`powerSum_re_ge_split`). -/
theorem li_nonneg_cfg_imp_online_ne_zero (Z : WideConfig) {A₀ : ℝ} (hc : HCount Z A₀) (hnz : ∀ ρ ∈ Z.carrier, ρ ≠ 0) :
    (∀ n : ℕ, 0 ≤ liCoeff Z n) → ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  intro hnn
  by_contra hno
  push_neg at hno
  obtain ⟨ρ1, hρ1, hoff⟩ := hno
  -- (V2''): a point of modulus above `1`; (V3'): finitely many at or above `r`
  obtain ⟨ρ', hρ', hr0⟩ := Wide.exists_dominant_point_ne_zero Z hnz hρ1 hoff
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
  have hinj : Set.InjOn (wD R) DF := by
    intro a _ b _ h
    have h2 : 1 - a⁻¹ = 1 - b⁻¹ := by
      have ha : 1 - a⁻¹ = wD R a * (R : ℂ) := (div_mul_cancel₀ (1 - a⁻¹) hRC).symm
      have hb : 1 - b⁻¹ = wD R b * (R : ℂ) := (div_mul_cancel₀ (1 - b⁻¹) hRC).symm
      rw [ha, hb, h]
    exact inv_injective (sub_right_injective h2)
  have hm1 : ∀ x ∈ DF, 1 ≤ Z.mult x := fun x hx => Z.one_le_mult x (Wide.mem_domSet.mp ((hDF x).mp hx)).1
  -- (V4''): the split at `w = 1` in place of v0.33's `w ≠ 1` step
  obtain ⟨c, hc0, hXinf⟩ := Wide.powerSum_re_ge_split DF (wD R) Z.mult hDne hwn hinj hm1
  -- (V5'') on the rest
  obtain ⟨C, hC⟩ := Wide.remainder_le_ne_zero Z hc hnz hs1
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
  -- (V4'') at some `n ≥ Nq`
  obtain ⟨n, hn, hX⟩ := hXinf Nq
  have hlt : (∑ x ∈ DF, (Z.mult x : ℝ)) * (1 / R) ^ n + C * ((n : ℝ) ^ 2 * (s / R) ^ n) +
      2 * C * ((n : ℝ) ^ 1 * (s / R) ^ n) + C * (s / R) ^ n < c := hNq n hn
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

/-! ## The controls under the strip-free form ((R299)(3)-(4), the plan == 5): C2 and C3 on the real segment, C2b on the point `0` -/

/-- **C2 meets the hypothesis:** both points of `c2Config` are nonzero. -/
theorem c2_ne_zero : ∀ ρ ∈ c2Config.carrier, ρ ≠ 0 := by
  intro ρ hρ
  rcases Set.mem_insert_iff.mp hρ with h | h
  · rw [h]
    exact Complex.ofReal_ne_zero.mpr (by norm_num)
  · rw [Set.mem_singleton_iff.mp h]
    exact Complex.ofReal_ne_zero.mpr (by norm_num)

/-- **C2's dominant point is the `w = 1` point:** at `R = 5`, `wD 5 (-1/4) = (1 + 4) / 5 = 1`. -/
theorem c2_w_eq_one : wD 5 ((-1 / 4 : ℝ) : ℂ) = 1 := by
  have h5 : ((5 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by norm_num)
  rw [wD, div_eq_one_iff_eq h5]
  first
    | (rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_inj]; norm_num)
    | (push_cast; norm_num)
    | norm_num

/-- **C2's first coefficient is negative:** `λ₁ = (-1/4)⁻¹ + (5/4)⁻¹ = -16/5`. -/
theorem c2_liCoeff_one_neg : liCoeff c2Config 1 < 0 := by
  classical
  have h1 : ((-1 / 4 : ℝ) : ℂ) ∈ c2Config.carrier := Set.mem_insert _ _
  have h2 : ((5 / 4 : ℝ) : ℂ) ∈ c2Config.carrier := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hne : ((-1 / 4 : ℝ) : ℂ) ≠ ((5 / 4 : ℝ) : ℂ) := fun h => absurd (Complex.ofReal_injective h) (by norm_num)
  have hsupp : ∀ x ∉ ({((-1 / 4 : ℝ) : ℂ), ((5 / 4 : ℝ) : ℂ)} : Finset ℂ),
      c2Config.carrier.indicator (gL c2Config 1) x = 0 := by
    intro x hx
    refine Set.indicator_of_notMem (fun hmem => hx ?_) _
    rcases Set.mem_insert_iff.mp hmem with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · rw [Set.mem_singleton_iff.mp h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hm : ∀ x, c2Config.mult x = 1 := fun _ => rfl
  have e : ∀ r : ℝ, (LiWeil.liTerm 1 (r : ℂ)).re = r⁻¹ := by
    intro r
    rw [LiWeil.liTerm, pow_one, sub_sub_cancel, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [liCoeff_eq_indicator, tsum_eq_sum hsupp, Finset.sum_pair hne, Set.indicator_of_mem h1, Set.indicator_of_mem h2, gL, gL,
    hm, hm, e, e]
  norm_num

/-- **C3, the real segment admitted:** the configuration with a real point at `-1/4 ∈ (-1/2, 0)` meets the strip-free hypothesis, fails
v0.33's exclusion, has its dominant point at `w = 1`, and carries a negative coefficient. -/
theorem c3_real_segment : (∀ ρ ∈ c2Config.carrier, ρ ≠ 0) ∧ ¬ HExcl c2Config ∧ wD 5 ((-1 / 4 : ℝ) : ℂ) = 1 ∧
    liCoeff c2Config 1 < 0 :=
  ⟨c2_ne_zero, c2_not_excl, c2_w_eq_one, c2_liCoeff_one_neg⟩

/-- **C2b fails the hypothesis at `0`.** -/
theorem c2b_not_ne_zero : ¬ ∀ ρ ∈ c2bConfig.carrier, ρ ≠ 0 :=
  fun h => h ((0 : ℝ) : ℂ) (Set.mem_insert _ _) Complex.ofReal_zero

/-- **C2b's lesson under the strip-free form:** the configuration `{0, 1}` fails `ρ ≠ 0` at `0`, while every coefficient is nonnegative
and `1` is off the line -- the exclusion of `0` is necessary, and it lives in the hypothesis `ρ ≠ 0`. -/
theorem c2b_lesson : (¬ ∀ ρ ∈ c2bConfig.carrier, ρ ≠ 0) ∧ (∀ n : ℕ, 0 ≤ liCoeff c2bConfig n) ∧
    ∃ ρ ∈ c2bConfig.carrier, ρ.re ≠ 1 / 2 :=
  ⟨c2b_not_ne_zero, c2b_nonneg_offline⟩

end Wide
end Schema
end SIDEExplicitFormula
