/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/CriterionConverse.lean
THIS PROGRAMME'S WORK (act b572, ruling (R182)(4)(c)-(d); W-ORD-GRH-WEIL, act seven) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CRITERION AT THE χ-INSTANCE, ITS CONVERSE, AND THE EQUIVALENCE. PowerLimit.lean's L7e (`dominant_summable` through
`zeroSide_eventually_neg`, :947-:1157 at v0.13) is stated over `Zeta23.zetaZeroConfig` and consumes ζ's local count; its proofs
consume of ζ nothing else. Carried here to `chiZeroConfig` with `chiZeroConfig_local_count` (Chi/LocalCount.lean) and the zero side
for χ, by named replacements (relay data/b572_gen_converse.py.txt); every generic lemma of PowerLimit, PowerWindow and RestBound
(the window, the tie and kill sets, the polynomial operator, `weighted_summable`, `plateau_dominant`) is consumed as it stands.
Then L8 at χ: `h2_sign_chi → rh_strip_chi` through b321's identity for χ, and `h2_sign_chi χ ↔ GRH_chi χ`.
Nothing here proves GRH or locates any zero of any `L(s, χ)`: an equivalence between open statements.
-/
import SIDEExplicitFormula.Chi.CriterionForward

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter B321

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {hχ : χ.IsPrimitive} {h1 : χ ≠ 1}
  {g0 : ℝ → ℝ} {L M : ℝ}

/-- **L7e, `dominant_summable_chi`:** with `j_0 = D`, the dominant is summable over the χ-configuration, by its
local count. -/
theorem dominant_summable_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (B : ℝ) (D : ℕ) :
    Summable (fun ρ : (chiZeroConfig χ hχ h1).carrier => ((chiZeroConfig χ hχ h1).mult ρ : ℝ) *
      (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))) := by
  obtain ⟨A₀, hA1, hA2⟩ := chiZeroConfig_local_count hχ h1
  have hM := H.hM
  have hA := Aw_nonneg H
  exact weighted_summable (chiZeroConfig χ hχ h1) ⟨hA1, hA2⟩
    (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
    (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
    (fun ρ _ => mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
    (fun ρ hρ => zero_weight H B D ρ hρ)

open Classical in
/-- The rest of the zero side: the zeros off `T`. -/
def fR_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (Q : ℕ → Polynomial ℝ) (j : ℕ)
    (x : (chiZeroConfig χ hχ h1).carrier) : ℂ :=
  if (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M then 0 else
    ((chiZeroConfig χ hχ h1).mult x : ℂ) * Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x)

theorem fR_norm_le_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ)
    (x : (chiZeroConfig χ hχ h1).carrier) (hT : (x : ℂ) ∉ tieSet (chiZeroConfig χ hχ h1) g0 M) :
    ‖fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) := by
  have hterm := rest_term_small H (Q j) B D (hB j) j x
  have hMN : 0 < M ^ (2 ^ (j + 1)) := pow_pos H.hM _
  unfold fR_chi
  rw [if_neg hT, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg H.hM.le,
    div_pow]
  have e : ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) *
      (offScore g0 x ^ (2 ^ (j + 1)) / M ^ (2 ^ (j + 1)))) =
      (((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * offScore g0 x ^ (2 ^ (j + 1)))) /
        M ^ (2 ^ (j + 1)) := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)) hMN.le

theorem fR_bound_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ) (hj : D ≤ j)
    (x : (chiZeroConfig χ hχ h1).carrier) :
    ‖fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) := by
  have hM := H.hM
  have hr0 : 0 ≤ offScore g0 x / M := div_nonneg (norm_nonneg _) hM.le
  have hbnd0 : 0 ≤ ((chiZeroConfig χ hχ h1).mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity)) (pow_nonneg hr0 _))
  by_cases hT : (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M
  · have h0 : fR_chi H Q j x = 0 := by
      unfold fR_chi
      rw [if_pos hT]
    rw [h0, zero_div, norm_zero]
    exact hbnd0
  by_cases hK : (x : ℂ) ∈ killSet (chiZeroConfig χ hχ h1) g0 M
  · have h0 : fR_chi H Q j x = 0 := by
      unfold fR_chi
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
  calc ‖fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
      ≤ ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) :=
        fR_norm_le_chi H Q B D hB j x hT
    _ ≤ ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hN) (by positivity))
          (Nat.cast_nonneg _)

/-- **L7e, `rest_tendsto_zero_chi`:** the rest over `M^(2^(j+1))` tends to 0 (Tannery's theorem, the dominant of
`dominant_summable_chi`, valid for `j >= D`). -/
theorem rest_tendsto_zero_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) :
    Tendsto (fun j => ∑' x, fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
  have hM := H.hM
  have hN : Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.lt_two_pow_self (n := j + 1)).le) (tendsto_add_atTop_nat 1)
  have hpt : ∀ x : (chiZeroConfig χ hχ h1).carrier,
      Tendsto (fun j => fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
    intro x
    by_cases hT : (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M
    · have h0 : ∀ j, fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR_chi
        rw [if_pos hT, zero_div]
      simp only [h0]
      exact tendsto_const_nhds
    by_cases hK : (x : ℂ) ∈ killSet (chiZeroConfig χ hχ h1) g0 M
    · have h0 : ∀ j, fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR_chi
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
    have hc := hr.const_mul (((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D)))
    rw [mul_zero] at hc
    refine squeeze_zero_norm (fun j => fR_norm_le_chi H Q B D hB j x hT) (hc.congr (fun j => ?_))
    ring
  have hbd : ∀ᶠ j in atTop, ∀ x : (chiZeroConfig χ hχ h1).carrier,
      ‖fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
        ((chiZeroConfig χ hχ h1).mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    Filter.eventually_atTop.mpr ⟨D, fun j hj x => fR_bound_chi H Q B D hB j hj x⟩
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun j x => fR_chi H Q j x / (M : ℂ) ^ (2 ^ (j + 1)))
    (g := fun _ => (0 : ℂ)) (dominant_summable_chi H B D) hpt hbd
  simpa using hlim

open Classical in
/-- `T` as a Finset of the carrier. -/
def sT_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) : Finset (chiZeroConfig χ hχ h1).carrier :=
  (TF H).subtype (· ∈ (chiZeroConfig χ hχ h1).carrier)

theorem mem_sT_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (x : (chiZeroConfig χ hχ h1).carrier) :
    x ∈ sT_chi H ↔ (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M := by
  classical
  unfold sT_chi
  exact Finset.mem_subtype.trans (mem_TF H)

/-- **L7e, `zeroSide_eventually_neg_chi`:** for some `j`, the zero side of the power window has negative real part. -/
theorem zeroSide_eventually_neg_chi (H : PWSetup (chiZeroConfig χ hχ h1) g0 L M) (ρs : ℂ)
    (hρs : ρs ∈ tieSet (chiZeroConfig χ hχ h1) g0 M) :
    ∃ (a : List ℝ) (j : ℕ), (zeroSide_chi χ hχ h1 (kWindow a g0 j)).re < 0 := by
  classical
  obtain ⟨B, D, hB0, hcoef⟩ := coeffs_exist H ⟨ρs, hρs⟩
  choose Q hQtie hQb using hcoef
  have hc0 : 0 < ∑ x ∈ sT_chi H, ((chiZeroConfig χ hχ h1).mult x : ℝ) * Nf H x := by
    refine Finset.sum_pos (fun x hx => mul_pos ?_ (Nf_pos H ((mem_sT_chi H x).mp hx)))
      ⟨⟨ρs, hρs.1⟩, (mem_sT_chi H _).mpr hρs⟩
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one ((chiZeroConfig χ hχ h1).one_le_mult x x.2))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (rest_tendsto_zero_chi H Q B D hQb) _ hc0
  have hj := hJ (max J D) (le_max_left _ _)
  rw [dist_zero_right] at hj
  refine ⟨coeffList (Pof H (Q (max J D))), max J D, ?_⟩
  have hDj : D ≤ max J D := le_max_right _ _
  have hM := H.hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMN : (M : ℂ) ^ (2 ^ (max J D + 1)) ≠ 0 := pow_ne_zero _ hM0
  have hsplit : ∀ x : (chiZeroConfig χ hχ h1).carrier,
      ((chiZeroConfig χ hχ h1).mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) =
        (if (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M then ((chiZeroConfig χ hχ h1).mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) +
          fR_chi H Q (max J D) x := by
    intro x
    unfold fR_chi
    split_ifs <;> simp
  have hzeroT : ∀ x ∉ sT_chi H, (if (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M then ((chiZeroConfig χ hχ h1).mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) = 0 :=
    fun x hx => if_neg (fun h => hx ((mem_sT_chi H x).mpr h))
  have hsumT : Summable (fun x : (chiZeroConfig χ hχ h1).carrier =>
      if (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M then ((chiZeroConfig χ hχ h1).mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) :=
    summable_of_ne_finset_zero hzeroT
  have hsumR : Summable (fR_chi H Q (max J D)) := by
    refine Summable.of_norm_bounded ((dominant_summable_chi H B D).mul_left (M ^ (2 ^ (max J D + 1)))) (fun x => ?_)
    have hb := fR_bound_chi H Q B D hQb (max J D) hDj x
    calc ‖fR_chi H Q (max J D) x‖
        = ‖fR_chi H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))‖ * ‖(M : ℂ) ^ (2 ^ (max J D + 1))‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hMN]
      _ ≤ ((chiZeroConfig χ hχ h1).mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) * M ^ (2 ^ (max J D + 1)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact mul_le_mul_of_nonneg_right hb (pow_nonneg hM.le _)
      _ = M ^ (2 ^ (max J D + 1)) * (((chiZeroConfig χ hχ h1).mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := mul_comm _ _
  have hT : ∀ x ∈ sT_chi H, (((chiZeroConfig χ hχ h1).mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x)).re =
        -(((chiZeroConfig χ hχ h1).mult x : ℝ) * Nf H x * M ^ (2 ^ (max J D + 1))) := by
    intro x hx
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      tie_term_neg H (Q (max J D)) (max J D) (hQtie (max J D)) ((mem_sT_chi H x).mp hx)]
    ring
  have hR : (∑' x, fR_chi H Q (max J D) x).re <
      (∑ x ∈ sT_chi H, ((chiZeroConfig χ hχ h1).mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
    have hR1 : (∑' x, fR_chi H Q (max J D) x) =
        (∑' x, fR_chi H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))) * (M : ℂ) ^ (2 ^ (max J D + 1)) := by
      rw [tsum_div_const, div_mul_cancel₀ _ hMN]
    have hR2 : ‖∑' x, fR_chi H Q (max J D) x‖ <
        (∑ x ∈ sT_chi H, ((chiZeroConfig χ hχ h1).mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
      rw [hR1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact mul_lt_mul_of_pos_right hj (pow_pos hM _)
    exact lt_of_le_of_lt (Complex.re_le_norm _) hR2
  have hTsum : (∑ x ∈ sT_chi H, (if (x : ℂ) ∈ tieSet (chiZeroConfig χ hχ h1) g0 M then
      ((chiZeroConfig χ hχ h1).mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0)) =
      ∑ x ∈ sT_chi H, ((chiZeroConfig χ hχ h1).mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) :=
    Finset.sum_congr rfl (fun x hx => if_pos ((mem_sT_chi H x).mp hx))
  unfold zeroSide_chi
  rw [tsum_congr hsplit, Summable.tsum_add hsumT hsumR, tsum_eq_sum hzeroT, hTsum, Complex.add_re, Complex.re_sum,
    Finset.sum_congr rfl hT, Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

/-- **L8 at χ, the converse at the strip**: an off-line point of the χ-configuration, the plateau's dominant point, and a
window in classK whose zero side for χ has negative real part contradict `h2_sign_chi` through b321's identity for χ. -/
theorem h2_sign_chi_imp_rh_strip_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    h2_sign_chi χ → rh_strip_chi χ hχ h1 := by
  intro h2
  by_contra hno
  unfold rh_strip_chi at hno
  push_neg at hno
  obtain ⟨ρ1, hρ1, hoff⟩ := hno
  have hF0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hF1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨L, hL, ρs, hρs, hoffs, hpos, hdom⟩ :=
    plateau_dominant (chiZeroConfig χ hχ h1) (1 / 2) hF0 hF1 ρ1 hρ1 hoff
  have H : PWSetup (chiZeroConfig χ hχ h1) (plateau (1 / 2) L hF0 hF1 hL) L
      (offScore (plateau (1 / 2) L hF0 hF1 hL) ρs) :=
    ⟨plateau_even _ _ hF0 hF1 hL, plateau_contDiff _ _ hF0 hF1 hL ⊤, plateau_support_Icc _ _ hF0 hF1 hL, hL.le,
      hpos, hdom⟩
  obtain ⟨a, j, hneg'⟩ := zeroSide_eventually_neg_chi H ρs ⟨hρs, hoffs, rfl⟩
  have hk := kWindow_classK a H.hsm H.hs j
  have hsign := h2 _ hk
  obtain ⟨_he, hc, hs, -⟩ := hk
  rw [← zeroSide_chi_eq hχ h1 hc hs] at hsign
  have h0 := (Complex.nonneg_iff.mp hsign).1
  linarith

/-- **THE CONVERSE OF THE CRITERION FOR χ**: `h2_sign_chi χ → GRH_chi χ`, for primitive `χ ≠ 1`. -/
theorem h2_sign_chi_imp_grh_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    h2_sign_chi χ → GRH_chi χ :=
  fun h => (rh_strip_chi_iff_grh_chi hχ h1).mp (h2_sign_chi_imp_rh_strip_chi χ hχ h1 h)

/-- **THE CRITERION AT THE χ-INSTANCE**: Weil positivity on classK for χ is GRH for χ, both directions, for every primitive
`χ ≠ 1`. An equivalence between open statements; it proves neither. -/
theorem h2_sign_chi_iff_grh_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    h2_sign_chi χ ↔ GRH_chi χ :=
  ⟨h2_sign_chi_imp_grh_chi χ hχ h1, grh_chi_imp_h2_sign_chi hχ h1⟩

end GRHWeil
end SIDEExplicitFormula
