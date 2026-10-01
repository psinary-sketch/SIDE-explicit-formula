/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Converse.lean
THIS PROGRAMME'S WORK (act b573, ruling (R183)(4)(b)-(c); W-ORD-GRH-WEIL, act eight) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE GENERIC SCHEMA, ITS CONVERSE AND THE EQUIVALENCE. PowerLimit.lean's L7e (`dominant_summable` through `zeroSide_eventually_neg`,
:947-:1157 at v0.14), stated over `Zeta23.zetaZeroConfig` with ζ's local count, carried to any `WeilConfig` with its `count` field
and its zero side by named, asserted replacements (relay data/b573_gen_schema.py.txt, b572's method); every generic lemma of
PowerLimit, PowerWindow and RestBound consumed as it stands. Then L8 over the structure: `h2_sign_cfg C → online C` through the
`ef` field, and `h2_sign_cfg C ↔ online C ↔ C.target`. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Config

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

variable {C : WeilConfig} {g0 : ℝ → ℝ} {L M : ℝ}

/-- **L7e, `dominant_summable_cfg`:** with `j_0 = D`, the dominant is summable over the configuration, by its
local count. -/
theorem dominant_summable_cfg (H : PWSetup C.toZeroConfig g0 L M) (B : ℝ) (D : ℕ) :
    Summable (fun ρ : C.toZeroConfig.carrier => (C.toZeroConfig.mult ρ : ℝ) *
      (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))) := by
  obtain ⟨A₀, hcnt⟩ := C.count
  have hM := H.hM
  have hA := Aw_nonneg H
  exact weighted_summable C.toZeroConfig hcnt
    (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
    (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
    (fun ρ _ => mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
    (fun ρ hρ => zero_weight H B D ρ hρ)

open Classical in
/-- The rest of the zero side: the zeros off `T`. -/
def fR_cfg (H : PWSetup C.toZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (j : ℕ)
    (x : C.toZeroConfig.carrier) : ℂ :=
  if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then 0 else
    (C.toZeroConfig.mult x : ℂ) * Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x)

theorem fR_norm_le_cfg (H : PWSetup C.toZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ)
    (x : C.toZeroConfig.carrier) (hT : (x : ℂ) ∉ tieSet C.toZeroConfig g0 M) :
    ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) := by
  have hterm := rest_term_small H (Q j) B D (hB j) j x
  have hMN : 0 < M ^ (2 ^ (j + 1)) := pow_pos H.hM _
  unfold fR_cfg
  rw [if_neg hT, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg H.hM.le,
    div_pow]
  have e : (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) *
      (offScore g0 x ^ (2 ^ (j + 1)) / M ^ (2 ^ (j + 1)))) =
      ((C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * offScore g0 x ^ (2 ^ (j + 1)))) /
        M ^ (2 ^ (j + 1)) := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)) hMN.le

theorem fR_bound_cfg (H : PWSetup C.toZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ) (hj : D ≤ j)
    (x : C.toZeroConfig.carrier) :
    ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) := by
  have hM := H.hM
  have hr0 : 0 ≤ offScore g0 x / M := div_nonneg (norm_nonneg _) hM.le
  have hbnd0 : 0 ≤ (C.toZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity)) (pow_nonneg hr0 _))
  by_cases hT : (x : ℂ) ∈ tieSet C.toZeroConfig g0 M
  · have h0 : fR_cfg H Q j x = 0 := by
      unfold fR_cfg
      rw [if_pos hT]
    rw [h0, zero_div, norm_zero]
    exact hbnd0
  by_cases hK : (x : ℂ) ∈ killSet C.toZeroConfig g0 M
  · have h0 : fR_cfg H Q j x = 0 := by
      unfold fR_cfg
      rw [if_neg hT, kill_term_zero H (Q j) j hK, mul_zero]
    rw [h0, zero_div, norm_zero]
    exact hbnd0
  have hlt : offScore g0 x < M := by
    by_cases hon : (x : ℂ).re = 1 / 2
    · by_contra hge
      push_neg at hge
      exact hK ⟨x.2, hon, hge⟩
    · exact lt_of_le_of_ne (H.hdom x x.2 hon) (fun heq => hT ⟨x.2, hon, heq⟩)
  have hr1 : offScore g0 x / M ≤ 1 := (div_le_one hM).mpr hlt.le
  have hN : 2 ^ (D + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
      ≤ (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) :=
        fR_norm_le_cfg H Q B D hB j x hT
    _ ≤ (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hN) (by positivity))
          (Nat.cast_nonneg _)

/-- **L7e, `rest_tendsto_zero_cfg`:** the rest over `M^(2^(j+1))` tends to 0 (Tannery's theorem, the dominant of
`dominant_summable_cfg`, valid for `j >= D`). -/
theorem rest_tendsto_zero_cfg (H : PWSetup C.toZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) :
    Tendsto (fun j => ∑' x, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
  have hM := H.hM
  have hN : Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.lt_two_pow_self (n := j + 1)).le) (tendsto_add_atTop_nat 1)
  have hpt : ∀ x : C.toZeroConfig.carrier,
      Tendsto (fun j => fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
    intro x
    by_cases hT : (x : ℂ) ∈ tieSet C.toZeroConfig g0 M
    · have h0 : ∀ j, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR_cfg
        rw [if_pos hT, zero_div]
      simp only [h0]
      exact tendsto_const_nhds
    by_cases hK : (x : ℂ) ∈ killSet C.toZeroConfig g0 M
    · have h0 : ∀ j, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR_cfg
        rw [if_neg hT, kill_term_zero H (Q j) j hK, mul_zero, zero_div]
      simp only [h0]
      exact tendsto_const_nhds
    have hlt : offScore g0 x < M := by
      by_cases hon : (x : ℂ).re = 1 / 2
      · by_contra hge
        push_neg at hge
        exact hK ⟨x.2, hon, hge⟩
      · exact lt_of_le_of_ne (H.hdom x x.2 hon) (fun heq => hT ⟨x.2, hon, heq⟩)
    have hr0 : 0 ≤ offScore g0 x / M := div_nonneg (norm_nonneg _) hM.le
    have hr1 : offScore g0 x / M < 1 := (div_lt_one hM).mpr hlt
    have hr : Tendsto (fun j : ℕ => (offScore g0 x / M) ^ (2 ^ (j + 1))) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hN
    have hc := hr.const_mul ((C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D)))
    rw [mul_zero] at hc
    refine squeeze_zero_norm (fun j => fR_norm_le_cfg H Q B D hB j x hT) (hc.congr (fun j => ?_))
    ring
  have hbd : ∀ᶠ j in atTop, ∀ x : C.toZeroConfig.carrier,
      ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
        (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    Filter.eventually_atTop.mpr ⟨D, fun j hj x => fR_bound_cfg H Q B D hB j hj x⟩
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun j x => fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1)))
    (g := fun _ => (0 : ℂ)) (dominant_summable_cfg H B D) hpt hbd
  simpa using hlim

open Classical in
/-- `T` as a Finset of the carrier. -/
def sT_cfg (H : PWSetup C.toZeroConfig g0 L M) : Finset C.toZeroConfig.carrier :=
  (TF H).subtype (· ∈ C.toZeroConfig.carrier)

theorem mem_sT_cfg (H : PWSetup C.toZeroConfig g0 L M) (x : C.toZeroConfig.carrier) :
    x ∈ sT_cfg H ↔ (x : ℂ) ∈ tieSet C.toZeroConfig g0 M := by
  classical
  unfold sT_cfg
  exact Finset.mem_subtype.trans (mem_TF H)

/-- **L7e, `zeroSide_eventually_neg_cfg`:** for some `j`, the zero side of the power window has negative real part. -/
theorem zeroSide_eventually_neg_cfg (H : PWSetup C.toZeroConfig g0 L M) (ρs : ℂ)
    (hρs : ρs ∈ tieSet C.toZeroConfig g0 M) :
    ∃ (a : List ℝ) (j : ℕ), (zeroSide_cfg C (kWindow a g0 j)).re < 0 := by
  classical
  obtain ⟨B, D, hB0, hcoef⟩ := coeffs_exist H ⟨ρs, hρs⟩
  choose Q hQtie hQb using hcoef
  have hc0 : 0 < ∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x := by
    refine Finset.sum_pos (fun x hx => mul_pos ?_ (Nf_pos H ((mem_sT_cfg H x).mp hx)))
      ⟨⟨ρs, hρs.1⟩, (mem_sT_cfg H _).mpr hρs⟩
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (C.toZeroConfig.one_le_mult x x.2))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (rest_tendsto_zero_cfg H Q B D hQb) _ hc0
  have hj := hJ (max J D) (le_max_left _ _)
  rw [dist_zero_right] at hj
  refine ⟨coeffList (Pof H (Q (max J D))), max J D, ?_⟩
  have hDj : D ≤ max J D := le_max_right _ _
  have hM := H.hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMN : (M : ℂ) ^ (2 ^ (max J D + 1)) ≠ 0 := pow_ne_zero _ hM0
  have hsplit : ∀ x : C.toZeroConfig.carrier,
      (C.toZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) =
        (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) +
          fR_cfg H Q (max J D) x := by
    intro x
    unfold fR_cfg
    split_ifs <;> simp
  have hzeroT : ∀ x ∉ sT_cfg H, (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) = 0 :=
    fun x hx => if_neg (fun h => hx ((mem_sT_cfg H x).mpr h))
  have hsumT : Summable (fun x : C.toZeroConfig.carrier =>
      if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) :=
    summable_of_ne_finset_zero hzeroT
  have hsumR : Summable (fR_cfg H Q (max J D)) := by
    refine Summable.of_norm_bounded ((dominant_summable_cfg H B D).mul_left (M ^ (2 ^ (max J D + 1)))) (fun x => ?_)
    have hb := fR_bound_cfg H Q B D hQb (max J D) hDj x
    calc ‖fR_cfg H Q (max J D) x‖
        = ‖fR_cfg H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))‖ * ‖(M : ℂ) ^ (2 ^ (max J D + 1))‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hMN]
      _ ≤ (C.toZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) * M ^ (2 ^ (max J D + 1)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact mul_le_mul_of_nonneg_right hb (pow_nonneg hM.le _)
      _ = M ^ (2 ^ (max J D + 1)) * ((C.toZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := mul_comm _ _
  have hT : ∀ x ∈ sT_cfg H, ((C.toZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x)).re =
        -((C.toZeroConfig.mult x : ℝ) * Nf H x * M ^ (2 ^ (max J D + 1))) := by
    intro x hx
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      tie_term_neg H (Q (max J D)) (max J D) (hQtie (max J D)) ((mem_sT_cfg H x).mp hx)]
    ring
  have hR : (∑' x, fR_cfg H Q (max J D) x).re <
      (∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
    have h1 : (∑' x, fR_cfg H Q (max J D) x) =
        (∑' x, fR_cfg H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))) * (M : ℂ) ^ (2 ^ (max J D + 1)) := by
      rw [tsum_div_const, div_mul_cancel₀ _ hMN]
    have h2 : ‖∑' x, fR_cfg H Q (max J D) x‖ <
        (∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
      rw [h1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact mul_lt_mul_of_pos_right hj (pow_pos hM _)
    exact lt_of_le_of_lt (Complex.re_le_norm _) h2
  have hTsum : (∑ x ∈ sT_cfg H, (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then
      (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0)) =
      ∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) :=
    Finset.sum_congr rfl (fun x hx => if_pos ((mem_sT_cfg H x).mp hx))
  unfold zeroSide_cfg
  rw [tsum_congr hsplit, Summable.tsum_add hsumT hsumR, tsum_eq_sum hzeroT, hTsum, Complex.add_re, Complex.re_sum,
    Finset.sum_congr rfl hT, Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

/-- **L8 over the structure, the converse at the strip**: an off-line point of the configuration, the plateau's dominant point,
and a window in classK whose zero side has negative real part contradict `h2_sign_cfg C` through the `ef` field. -/
theorem h2_sign_cfg_imp_online (C : WeilConfig) : h2_sign_cfg C → online C := by
  intro h2
  by_contra hno
  unfold online at hno
  push_neg at hno
  obtain ⟨ρ1, hρ1, hoff⟩ := hno
  have hF0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hF1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨L, hL, ρs, hρs, hoffs, hpos, hdom⟩ :=
    plateau_dominant C.toZeroConfig (1 / 2) hF0 hF1 ρ1 hρ1 hoff
  have H : PWSetup C.toZeroConfig (plateau (1 / 2) L hF0 hF1 hL) L
      (offScore (plateau (1 / 2) L hF0 hF1 hL) ρs) :=
    ⟨plateau_even _ _ hF0 hF1 hL, plateau_contDiff _ _ hF0 hF1 hL ⊤, plateau_support_Icc _ _ hF0 hF1 hL, hL.le,
      hpos, hdom⟩
  obtain ⟨a, j, hneg'⟩ := zeroSide_eventually_neg_cfg H ρs ⟨hρs, hoffs, rfl⟩
  have hk := kWindow_classK a H.hsm H.hs j
  have hsign := h2 _ hk
  obtain ⟨he, hc, hs, -⟩ := hk
  rw [← zeroSide_cfg_eq C hc hs he] at hsign
  have h0 := (Complex.nonneg_iff.mp hsign).1
  linarith

/-- **THE CRITERION OVER THE STRUCTURE, AT THE STRIP**: Weil positivity on classK is the strip form, both directions. -/
theorem h2_sign_cfg_iff_online (C : WeilConfig) : h2_sign_cfg C ↔ online C :=
  ⟨h2_sign_cfg_imp_online C, online_imp_h2_sign_cfg C⟩

/-- **THE CRITERION OVER THE STRUCTURE**: Weil positivity on classK is the instance's own target, both directions. An
equivalence between open statements; it proves neither. -/
theorem h2_sign_cfg_iff_target (C : WeilConfig) : h2_sign_cfg C ↔ C.target :=
  (h2_sign_cfg_iff_online C).trans C.target_iff.symm

end Schema
end SIDEExplicitFormula
