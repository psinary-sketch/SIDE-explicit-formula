/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/LiConverseCfg.lean
THIS PROGRAMME'S WORK (act b669, ruling (R279)(3)-(4) and the author's word on the route: (P); act b673, ruling (R283)(5))
-- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CONVERSE OVER A CONFIGURATION, ON THE BOMBIERI-LAGARIAS ROUTE (OPEN_TRAILS :11609, (V1)-(V4); at χ :11732, :11796).
(V1) is the configuration's own fields `reflect_mem`, `mult_reflect`. (V2) an off-line point of a configuration in the open
strip has an orbit member `ρ′` with `1 < ‖1 - ρ′⁻¹‖` (`exists_dominant_point`). (V3) for `1 < r` the points with
`r ≤ ‖1 - ρ⁻¹‖` are finitely many (`dominant_finite`; the kernel's finite dominant set for the power-window score,
PowerWindow.lean :398-:403, is another set). (V4) the power-sum lemma, generic, in both signs, is Schema/PowerSum.lean's
(moved there at b673 with its two partial-sum lemmas); (V5) the remainder off the dominant set is Schema/LiRemainder.lean's.
(S5) `li_nonneg_cfg_imp_online`, composed at b673: an off-line point gives a dominant modulus `R = r_max > 1` (V2, V3), the
finite set `D` of points at that modulus, and a modulus `s < R` above every other point; the coefficient splits at `D` as
`Σ_D m - R ^ n Re (Σ_D m w ^ n) + (the rest)`, `w = (1 - ρ⁻¹) / R` unimodular and never `1` in the open strip; (V4+) puts
`Re (Σ_D m w ^ n) ≥ c > 0` at arbitrarily large `n`, (V5) bounds the rest by `C (n + 1) ^ 2 s ^ n`, and
`Σ_D m (1 / R) ^ n + C (n + 1) ^ 2 (s / R) ^ n → 0` makes the coefficient negative there -- against the hypothesis. Its
instance at χ `li_nonneg_chi_imp_grh_chi` (S6) and the equivalence at χ `li_nonneg_chi_iff_grh_chi` (S7) follow.
Nothing here proves GRH or RH or locates any zero.
-/
import SIDEExplicitFormula.Schema.PowerSum
import SIDEExplicitFormula.Schema.LiRemainder
import SIDEExplicitFormula.Chi.LocalCount
import SIDEExplicitFormula.Chi.LiForward

open Complex Filter Topology

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

/-! ## (S5) the split of the coefficient at the dominant set -/

/-- The points of `Z` at modulus `‖1 - ρ⁻¹‖ = R`. -/
def domSet (Z : ZeroConfig) (R : ℝ) : Set ℂ := {x | x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ = R}

theorem mem_domSet {Z : ZeroConfig} {R : ℝ} {x : ℂ} : x ∈ domSet Z R ↔ x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ = R := Iff.rfl

/-- The points of `Z` at modulus `‖1 - ρ⁻¹‖ < s`: (V5)'s set. -/
def restSet (Z : ZeroConfig) (s : ℝ) : Set ℂ := {x | x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ < s}

theorem mem_restSet {Z : ZeroConfig} {s : ℝ} {x : ℂ} : x ∈ restSet Z s ↔ x ∈ Z.carrier ∧ ‖1 - x⁻¹‖ < s := Iff.rfl

/-- The coefficient's term at a point of `ℂ`: `m_x Re (liTerm n x)`. -/
def gL (Z : ZeroConfig) (n : ℕ) (x : ℂ) : ℝ := (Z.mult x : ℝ) * (LiWeil.liTerm n x).re

/-- The unimodular direction at modulus `R`: `w = (1 - x⁻¹) / R`. -/
def wD (R : ℝ) (x : ℂ) : ℂ := (1 - x⁻¹) / (R : ℂ)

/-- The coefficient as a sum over `ℂ`: `liCoeffCfg Z n = Σ' x, 1_Z(x) m_x Re (liTerm n x)` (`pairTerm_re`). -/
theorem liCoeffCfg_eq_indicator (Z : ZeroConfig) (n : ℕ) :
    liCoeffCfg Z n = ∑' x : ℂ, Z.carrier.indicator (gL Z n) x := by
  have h : (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re) = fun ρ => 2 * gL Z n ρ := by
    funext ρ
    rw [LiWeil.pairTerm_re, gL]
    ring
  rw [liCoeffCfg, h, tsum_mul_left, ← tsum_subtype Z.carrier (gL Z n)]
  ring

/-- The summability of the coefficient's terms over `ℂ`, from `liCoeffCfg_summable`. -/
theorem summable_indicator_gL (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (n : ℕ) :
    Summable (Z.carrier.indicator (gL Z n)) := by
  have hsub : Summable (fun ρ : Z.carrier => gL Z n ρ) :=
    ((liCoeffCfg_summable Z hc n).mul_left (1 / 2)).congr fun ρ => by
      rw [LiWeil.pairTerm_re, gL]
      ring
  exact (summable_subtype_iff_indicator (f := gL Z n) (s := Z.carrier)).mp hsub

/-- The dominant part: `Σ_D m_x Re (liTerm n x) = Σ_D m_x - R ^ n Re (Σ_D m_x w_x ^ n)` for `R ≠ 0`. -/
theorem sum_gL_dom (Z : ZeroConfig) (D : Finset ℂ) {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    ∑ x ∈ D, gL Z n x = ∑ x ∈ D, (Z.mult x : ℝ) - R ^ n * (∑ x ∈ D, (Z.mult x : ℂ) * wD R x ^ n).re := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hz : 1 - x⁻¹ = wD R x * (R : ℂ) := (div_mul_cancel₀ (1 - x⁻¹) hRC).symm
  rw [gL, LiWeil.liTerm, hz, mul_pow, ← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero]
  ring

/-! ## (S5) the converse over a configuration -/

/-- **The converse over a configuration (S5):** under the local count and the open strip, `0 ≤ liCoeffCfg Z n` for every `n`
puts every point of `Z` on the line. -/
theorem li_nonneg_cfg_imp_online (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (hs : B321.HStrip Z) :
    (∀ n : ℕ, 0 ≤ liCoeffCfg Z n) → ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  intro hnn
  by_contra hno
  push_neg at hno
  obtain ⟨ρ1, hρ1, hoff⟩ := hno
  -- (V2): a point of modulus above `1`; (V3): finitely many at or above `r`
  obtain ⟨ρ', hρ', hr0⟩ := exists_dominant_point Z hs hρ1 hoff
  obtain ⟨r, hr1, hrr0⟩ : ∃ r : ℝ, 1 < r ∧ r < ‖1 - ρ'⁻¹‖ :=
    ⟨(1 + ‖1 - ρ'⁻¹‖) / 2, by linarith, by linarith⟩
  have hF := dominant_finite Z hr1
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
  have hDfin : (domSet Z R).Finite :=
    hF.subset fun x hx => ⟨(mem_domSet.mp hx).1, by rw [(mem_domSet.mp hx).2]; exact hrR.le⟩
  obtain ⟨DF, hDF⟩ : ∃ DF : Finset ℂ, ∀ x, x ∈ DF ↔ x ∈ domSet Z R :=
    ⟨hDfin.toFinset, fun x => hDfin.mem_toFinset⟩
  have hDne : DF.Nonempty := ⟨ρm, (hDF ρm).mpr (mem_domSet.mpr ⟨hρm.1, hRdef.symm⟩)⟩
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRne
  have hwn : ∀ x ∈ DF, ‖wD R x‖ = 1 := by
    intro x hx
    have hxD := mem_domSet.mp ((hDF x).mp hx)
    rw [wD, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, hxD.2, div_self hRne]
  have hw1 : ∀ x ∈ DF, wD R x ≠ 1 := by
    intro x hx h
    have hxD := mem_domSet.mp ((hDF x).mp hx)
    have hst := hs x hxD.1
    have hx0 : x ≠ 0 := by
      intro e
      have := hst.1
      rw [e, Complex.zero_re] at this
      exact lt_irrefl _ this
    have h2 : 1 - x⁻¹ = (R : ℂ) := by
      rw [wD, div_eq_one_iff_eq hRC] at h
      exact h
    have h3 : x⁻¹.re = 1 - R := by
      have := congrArg Complex.re h2
      rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at this
      linarith
    have h4 : 0 < x⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos hst.1 (Complex.normSq_pos.mpr hx0)
    linarith
  have hinj : Set.InjOn (wD R) DF := by
    intro a _ b _ h
    have h2 : 1 - a⁻¹ = 1 - b⁻¹ := by
      have ha : 1 - a⁻¹ = wD R a * (R : ℂ) := (div_mul_cancel₀ (1 - a⁻¹) hRC).symm
      have hb : 1 - b⁻¹ = wD R b * (R : ℂ) := (div_mul_cancel₀ (1 - b⁻¹) hRC).symm
      rw [ha, hb, h]
    exact inv_injective (sub_right_injective h2)
  have hm1 : ∀ x ∈ DF, 1 ≤ Z.mult x := fun x hx => Z.one_le_mult x (mem_domSet.mp ((hDF x).mp hx)).1
  obtain ⟨hB, hQ, _⟩ := powerSum_consts DF Z.mult hDne hm1
  have hc0 : 0 < (∑ x ∈ DF, (Z.mult x : ℝ) ^ 2) / (4 * ∑ x ∈ DF, (Z.mult x : ℝ)) := div_pos hQ (by linarith)
  -- (V5) on the rest
  obtain ⟨C, hC⟩ := remainder_le Z hc hs hs1
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
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hc0))
  -- (V4+) at some `n ≥ N0`
  obtain ⟨n, hn, hX⟩ := powerSum_re_ge_infinitely DF (wD R) Z.mult hDne hwn hw1 hinj hm1 N0
  have hlt : (∑ x ∈ DF, (Z.mult x : ℝ)) * (1 / R) ^ n + C * ((n : ℝ) ^ 2 * (s / R) ^ n) +
      2 * C * ((n : ℝ) ^ 1 * (s / R) ^ n) + C * (s / R) ^ n <
        (∑ x ∈ DF, (Z.mult x : ℝ) ^ 2) / (4 * ∑ x ∈ DF, (Z.mult x : ℝ)) := hN0 n hn
  -- the split of the coefficient at `D`
  have hdec : ∀ x, Z.carrier.indicator (gL Z n) x =
      (domSet Z R).indicator (gL Z n) x + (restSet Z s).indicator (gL Z n) x := by
    intro x
    by_cases hx : x ∈ Z.carrier
    · by_cases hxD : ‖1 - x⁻¹‖ = R
      · have hxR : ¬ (‖1 - x⁻¹‖ < s) := by
          rw [hxD]
          exact not_lt.mpr hsR.le
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_domSet.mpr ⟨hx, hxD⟩),
          Set.indicator_of_notMem (fun h => hxR (mem_restSet.mp h).2), add_zero]
      · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (fun h => hxD (mem_domSet.mp h).2),
          Set.indicator_of_mem (mem_restSet.mpr ⟨hx, hlts x hx hxD⟩), zero_add]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (mem_domSet.mp h).1),
        Set.indicator_of_notMem (fun h => hx (mem_restSet.mp h).1), add_zero]
  have hsumC := summable_indicator_gL Z hc n
  have hD0 : ∀ x ∉ DF, (domSet Z R).indicator (gL Z n) x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx ((hDF x).mpr h)) _
  have hsumD : Summable ((domSet Z R).indicator (gL Z n)) := summable_of_ne_finset_zero hD0
  have hsubR : restSet Z s ⊆ Z.carrier := fun x hx => (mem_restSet.mp hx).1
  have hsumR : Summable ((restSet Z s).indicator (gL Z n)) := by
    have := hsumC.indicator (restSet Z s)
    rwa [Set.indicator_indicator, Set.inter_eq_left.mpr hsubR] at this
  have htD : ∑' x, (domSet Z R).indicator (gL Z n) x = ∑ x ∈ DF, gL Z n x := by
    rw [tsum_eq_sum hD0]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem ((hDF x).mp hx) _
  have htR : ∑' x, (restSet Z s).indicator (gL Z n) x =
      ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re :=
    (tsum_subtype (restSet Z s) (gL Z n)).symm
  have hsplit : liCoeffCfg Z n = ∑ x ∈ DF, gL Z n x +
      ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ‖1 - ρ⁻¹‖ < s}, (Z.mult ρ : ℝ) * (LiWeil.liTerm n ρ).re := by
    rw [liCoeffCfg_eq_indicator, tsum_congr hdec, Summable.tsum_add hsumD hsumR, htD, htR]
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
  rw [hsplit, sum_gL_dom Z DF hRne n] at h0
  linarith

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

/-- **Li's criterion at χ (S7):** for a primitive `χ ≠ 1`, `(∀ n, 0 ≤ liCoeffCfg (chiZeroConfig χ hχ h1) n) ↔ GRH_chi χ` --
the converse (S6) and the forward half `grh_chi_imp_li_nonneg_chi` (Chi/LiForward.lean). -/
theorem li_nonneg_chi_iff_grh_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    (∀ n : ℕ, 0 ≤ Schema.liCoeffCfg (chiZeroConfig χ hχ h1) n) ↔ GRH_chi χ :=
  ⟨li_nonneg_chi_imp_grh_chi χ hχ h1, grh_chi_imp_li_nonneg_chi χ hχ h1⟩

end GRHWeil
end SIDEExplicitFormula
