/-
SIDE-explicit-formula -- SIDEExplicitFormula/LiWeilSym.lean
THIS PROGRAMME'S WORK (act b563, ruling (R173)(4); W-ORD-LI-WEIL-BRIDGE, item (X2)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LI-WEIL BRIDGE AT THE SYMMETRIC FAMILY. The Bombieri-Lagarias test function `k_n(u) = 1_{u<0} e^{u/2} P_n(u)` has a jump
at `0`. b561 found (relay `data/b561_decay_read.txt`) that a truncation family mollifying the jump ONE-SIDEDLY moves its
midpoint into `u < 0`, and `LiLimitExchange` (LiWeil.lean) is false as stated for `n ≥ 1`. Here the jump is mollified EVENLY
about `0`: the cut `symCut δ u = st(1/2 - u/δ) · st(δ u + 2)` (`st` Mathlib's `Real.smoothTransition`) is `1` on
`[-1/δ, -δ/2]`, `0` right of `δ/2` and left of `-2/δ`, and `symCut δ u + symCut δ (-u) = 1` near `0`.

(a) The family and (D1'): each member `symMember n δ = symCut δ · e^{u/2} P_n(u)` is in EF_lit's class for `δ > 0`.
(b) (D2'): at each `ρ` with `Re ρ > 0` the member's transform tends to `liTerm n ρ` as `δ → 0⁺`.
(c) `LiLimitExchangeSym n` stated; the zero sum at each member is real.
(d) (D3') `symPair_bound`: `|Re H_δ(ρ)| ≤ C(n)/‖ρ‖²` for every `δ ∈ (0, 1]` -- the odd jump cut cancels the jump's `n/ρ` in the
    real part (`jump_cos_bound`, two integrations by parts), and the left edge decays uniformly as `Re ρ → 0` (`left_edge_bound`,
    the scaling `u = v/δ` and iterated integration by parts on fixed profiles).
(e) (D4') `exchange_of_bound` (Tannery over the zeros, the dominant by `zero_sum_inv_sq`); `liLimitExchangeSym_holds`; and
    `li_identity_sym`: `LiCoeff n` is the `δ → 0⁺` limit of EF_lit's literature right-hand side at the symmetric members --
    the Bombieri-Lagarias arithmetic formula in limit form, over the genuine zeros of Mathlib's `riemannZeta`.

Nothing here proves RH or any positivity of the Li coefficients.
-/
import SIDEExplicitFormula.LiWeilExchange

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

noncomputable section

namespace SIDEExplicitFormula
namespace LiWeil

open Zeta23

/-! ## (a) The symmetric family and (D1') -/

/-- **The parity of the smooth transition:** `st (1 - x) = 1 - st x`. -/
theorem smoothTransition_one_sub (x : ℝ) : Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have h1 := Real.smoothTransition.pos_denom x
  have h2 := Real.smoothTransition.pos_denom (1 - x)
  unfold Real.smoothTransition at *
  rw [sub_sub_cancel] at h2 ⊢
  rw [eq_sub_iff_add_eq, div_add_div _ _ h2.ne' h1.ne', div_eq_one_iff_eq (mul_ne_zero h2.ne' h1.ne')]
  ring

/-- **The symmetric cut:** `st (1/2 - u/δ) · st (δ u + 2)`. -/
def symCut (δ u : ℝ) : ℝ := Real.smoothTransition (1 / 2 - u / δ) * Real.smoothTransition (δ * u + 2)

/-- **The symmetric truncation family:** the cut times the smooth profile `e^{u/2} P_n(u)`. -/
def symMember (n : ℕ) (δ : ℝ) (u : ℝ) : ℂ := ((symCut δ u : ℝ) : ℂ) * blSmooth n u

theorem symCut_contDiff (δ : ℝ) : ContDiff ℝ 2 (symCut δ) := by
  unfold symCut
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.div_const δ))).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const))

theorem symCut_nonneg (δ u : ℝ) : 0 ≤ symCut δ u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem symCut_le_one (δ u : ℝ) : symCut δ u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem symCut_eq_zero_right {δ u : ℝ} (hδ : 0 < δ) (hu : δ / 2 ≤ u) : symCut δ u = 0 := by
  unfold symCut
  have : 1 / 2 - u / δ ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hδ]
    linarith
  rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]

theorem symCut_eq_zero_left {δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ -2 / δ) : symCut δ u = 0 := by
  unfold symCut
  have : δ * u + 2 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hu hδ.le
    rw [mul_div_assoc', mul_neg, neg_div, mul_div_cancel_left₀ _ hδ.ne'] at h
    linarith
  rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

theorem symCut_eq_one {δ u : ℝ} (hδ : 0 < δ) (h1 : -1 / δ ≤ u) (h2 : u ≤ -(δ / 2)) : symCut δ u = 1 := by
  unfold symCut
  have ha : 1 ≤ 1 / 2 - u / δ := by
    have : u / δ ≤ -(1 / 2) := by
      rw [div_le_iff₀ hδ]
      linarith
    linarith
  have hb : 1 ≤ δ * u + 2 := by
    have h := mul_le_mul_of_nonneg_left h1 hδ.le
    rw [mul_div_assoc', mul_neg, mul_one, neg_div, div_self hδ.ne'] at h
    linarith
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb, one_mul]

/-- **(D1'):** for `δ > 0` every member of the symmetric family is in EF_lit's class -- `ContDiff ℝ 2` with compact
support (in `[-2/δ, δ/2]`). -/
theorem symMember_classEF (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 2 (symMember n δ) ∧ HasCompactSupport (symMember n δ) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp (symCut_contDiff δ)).mul (blSmooth_contDiff n), ?_⟩
  refine HasCompactSupport.intro (isCompact_Icc (a := -2 / δ) (b := δ / 2)) (fun u hu => ?_)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  unfold symMember
  rcases hu with hu | hu
  · rw [symCut_eq_zero_left hδ hu.le, Complex.ofReal_zero, zero_mul]
  · rw [symCut_eq_zero_right hδ hu.le, Complex.ofReal_zero, zero_mul]

/-- **EF_lit at each member of the symmetric family** (Zeta23's EF_lit for the genuine instance, WeilEF/Main.lean:286). -/
theorem symMember_EF (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ)) ∧
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ)
      = EF.literatureRHS (symMember n δ) :=
  WeilEF.EF_lit_zetaZeroConfig _ (symMember_classEF n hδ).1 (symMember_classEF n hδ).2

/-! ## (b) (D2') -- the member transforms tend to the jump's at each fixed zero -/

/-- The integrand of the member's transform: the cut times the profile's integrand. -/
theorem symMember_integrand (n : ℕ) (δ : ℝ) (ρ : ℂ) (u : ℝ) :
    symMember n δ u * cexp (Complex.I * gammaOf ρ * u)
      = ((symCut δ u : ℝ) : ℂ) * (blSmooth n u * cexp (Complex.I * gammaOf ρ * u)) := by
  unfold symMember
  ring

/-- Left of `0` the jump's integrand is the profile's. -/
theorem blTest_integrand_neg (n : ℕ) (ρ : ℂ) {u : ℝ} (hu : u < 0) :
    blTest n u * cexp (Complex.I * gammaOf ρ * u) = blSmooth n u * cexp (Complex.I * gammaOf ρ * u) := by
  unfold blTest
  rw [if_pos hu]

/-- **(D2'):** for `Re ρ > 0`, the transform of the symmetric member at `gammaOf ρ` tends to `liTerm n ρ` as `δ → 0⁺` --
dominated convergence in `u` (the dominant: the jump's integrand plus the profile's on `[0, 1]`) and `blTransform_holds`.
It is per zero; it says nothing uniform over the zeros. -/
theorem symMember_transform_tendsto (n : ℕ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    Tendsto (fun δ => paperFT (symMember n δ) (gammaOf ρ)) (𝓝[>] 0) (𝓝 (liTerm n ρ)) := by
  rw [← blTransform_holds n ρ hρ]
  unfold paperFT
  have hint : Integrable (fun u : ℝ => blTest n u * cexp (Complex.I * gammaOf ρ * u)) := integrable_blTest_integrand n hρ
  have hcont : Continuous (fun u : ℝ => blSmooth n u * cexp (Complex.I * gammaOf ρ * u)) :=
    (blSmooth_contDiff n).continuous.mul (by fun_prop)
  have hbi : Integrable (fun u : ℝ => ‖blTest n u * cexp (Complex.I * gammaOf ρ * u)‖
      + (Icc (0 : ℝ) 1).indicator (fun u => ‖blSmooth n u * cexp (Complex.I * gammaOf ρ * u)‖) u) := by
    refine hint.norm.add ?_
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hcont.norm.integrableOn_Icc
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbi ?_
  · exact Filter.Eventually.of_forall fun δ =>
      (((Complex.ofRealCLM.contDiff.comp (symCut_contDiff δ)).mul (blSmooth_contDiff n)).continuous.mul
        (by fun_prop : Continuous (fun u : ℝ => cexp (Complex.I * gammaOf ρ * u)))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    refine Filter.Eventually.of_forall fun u => ?_
    rw [symMember_integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (symCut_nonneg δ u)]
    have hb0 : 0 ≤ ‖blTest n u * cexp (Complex.I * gammaOf ρ * u)‖ := norm_nonneg _
    have hi0 : 0 ≤ (Icc (0 : ℝ) 1).indicator (fun u => ‖blSmooth n u * cexp (Complex.I * gammaOf ρ * u)‖) u :=
      Set.indicator_nonneg (fun _ _ => norm_nonneg _) u
    have hh0 := norm_nonneg (blSmooth n u * cexp (Complex.I * gammaOf ρ * u))
    have hc1 := symCut_le_one δ u
    have hc0 := symCut_nonneg δ u
    by_cases hu : u < 0
    · rw [blTest_integrand_neg n ρ hu]
      nlinarith
    · by_cases hu1 : u ≤ 1
      · rw [Set.indicator_of_mem (show u ∈ Icc (0 : ℝ) 1 from ⟨not_lt.mp hu, hu1⟩)]
        nlinarith
      · have h1u := not_le.mp hu1
        rw [symCut_eq_zero_right hδ.1 (by linarith [hδ.2]), zero_mul]
        linarith
  · have h0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with u hu0
    simp_rw [symMember_integrand]
    rcases lt_or_gt_of_ne hu0 with hu | hu
    · rw [blTest_integrand_neg n ρ hu]
      refine tendsto_const_nhds.congr' ?_
      have hpos : 0 < min (-2 * u) (-1 / u) := lt_min (by linarith) (div_pos_of_neg_of_neg (by norm_num) hu)
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      have hd1 : δ ≤ -2 * u := (hδ.2.trans_le (min_le_left _ _)).le
      have hd2 : δ ≤ -1 / u := (hδ.2.trans_le (min_le_right _ _)).le
      have h1 : -1 / δ ≤ u := by
        rw [div_le_iff₀ hδ.1]
        have hm := mul_le_mul_of_nonpos_left hd2 hu.le
        have he : u * (-1 / u) = -1 := by field_simp
        linarith [mul_comm u δ]
      rw [symCut_eq_one hδ.1 h1 (by linarith), Complex.ofReal_one, one_mul]
    · have hT : blTest n u * cexp (Complex.I * gammaOf ρ * u) = 0 := by
        unfold blTest
        rw [if_neg (not_lt.mpr hu.le), zero_mul]
      rw [hT]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * u by linarith)] with δ hδ
      rw [symCut_eq_zero_right hδ.1 (by linarith [hδ.2]), Complex.ofReal_zero, zero_mul]

/-! ## (c) The exchange at the symmetric family, stated; the zero sum is real -/

/-- **The limit exchange at the symmetric family (a `Prop`):** the zero side of EF_lit at the symmetric members tends
to `LiCoeff n` as `δ → 0⁺`. This is `LiLimitExchange` restated for (X2)'s family (ruling (R173)(4)); it is proved below
(`liLimitExchangeSym_holds`, part (e)). -/
def LiLimitExchangeSym (n : ℕ) : Prop :=
  Tendsto (fun δ => ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ))
    (𝓝[>] 0) (𝓝 (LiCoeff n : ℂ))

theorem I_gammaOf_mul (ρ : ℂ) (u : ℝ) : Complex.I * gammaOf ρ * u = (ρ - 1 / 2) * u := by
  unfold gammaOf
  field_simp

/-- The member is real, so its transform at the conjugate zero is the conjugate transform. -/
theorem symMember_transform_conj (n : ℕ) (δ : ℝ) (ρ : ℂ) :
    paperFT (symMember n δ) (gammaOf ((starRingEnd ℂ) ρ)) = (starRingEnd ℂ) (paperFT (symMember n δ) (gammaOf ρ)) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext u
  rw [I_gammaOf_mul, I_gammaOf_mul]
  unfold symMember blSmooth
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_sub, map_mul, Complex.conj_ofReal, map_ofNat]

/-- Conjugation on the genuine configuration, as an equivalence (`conj_mem`). -/
def conjEquiv : zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun ρ := ⟨(starRingEnd ℂ) ρ, conj_mem ρ.2⟩
  invFun ρ := ⟨(starRingEnd ℂ) ρ, conj_mem ρ.2⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

/-- **The zero sum at a member is its own conjugate** (the member real, the configuration conjugation-stable with its
multiplicities, `mult_conj`). -/
theorem symZeroSum_conj (n : ℕ) (δ : ℝ) :
    (starRingEnd ℂ) (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ))
      = ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ) := by
  rw [Complex.conj_tsum]
  conv_rhs => rw [← conjEquiv.tsum_eq]
  congr 1
  funext ρ
  show (starRingEnd ℂ) ((zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ)) =
    (zetaZeroConfig.mult ((starRingEnd ℂ) (ρ : ℂ)) : ℂ) * paperFT (symMember n δ) (gammaOf ((starRingEnd ℂ) (ρ : ℂ)))
  rw [mult_conj ρ.2, symMember_transform_conj, map_mul, Complex.conj_natCast]

/-- **The zero sum at a member is real.** -/
theorem symZeroSum_im (n : ℕ) (δ : ℝ) :
    (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (symMember n δ) (gammaOf ρ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (symZeroSum_conj n δ)

/-! ## (d) (D3') -- the bound, in the decay read's order (relay `data/b563_decay_read.txt` (4), (5), (7)) -/

/-- **(D3') STATED (a `Prop`):** the real part of the symmetric member's transform is bounded by `C / ‖ρ‖²` for every
`δ ∈ (0, 1]` and every `ρ` with `1 ≤ |Im ρ|` and `0 < Re ρ < 1`, the constant depending on `n` alone. -/
def SymPairBound (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ρ : ℂ, 1 ≤ |ρ.im| → 0 < ρ.re → ρ.re < 1 →
    |(paperFT (symMember n δ) (gammaOf ρ)).re| ≤ C / ‖ρ‖ ^ 2

/-- (d1) The member's integrand at `gammaOf ρ` is `symCut δ u · P_n(u) · e^{ρ u}`. -/
theorem symMember_integrand_exp (n : ℕ) (δ : ℝ) (ρ : ℂ) (u : ℝ) :
    symMember n δ u * cexp (Complex.I * gammaOf ρ * u) = ((symCut δ u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) := by
  rw [I_gammaOf_mul]
  unfold symMember blSmooth
  calc ((symCut δ u : ℝ) : ℂ) * ((Real.exp (u / 2) * blPoly n u : ℝ) : ℂ) * cexp ((ρ - 1 / 2) * u)
      = ((symCut δ u * blPoly n u : ℝ) : ℂ) * (cexp ((u / 2 : ℝ) : ℂ) * cexp ((ρ - 1 / 2) * u)) := by
        push_cast
        ring
    _ = ((symCut δ u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring

/-- (d1) **The cosine form:** the real part of the member's transform is
`∫ symCut δ u · P_n(u) · e^{β u} cos(γ u) du`, `β = Re ρ`, `γ = Im ρ` -- the member is real. -/
theorem symMember_transform_re (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (ρ : ℂ) :
    (paperFT (symMember n δ) (gammaOf ρ)).re
      = ∫ u : ℝ, symCut δ u * blPoly n u * (Real.exp (ρ.re * u) * Real.cos (ρ.im * u)) := by
  unfold paperFT
  have hi : Integrable (fun u : ℝ => symMember n δ u * cexp (Complex.I * gammaOf ρ * u)) :=
    ((symMember_classEF n hδ).1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (symMember_classEF n hδ).2.mul_right
  have h := integral_re hi
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1
  funext u
  rw [symMember_integrand_exp, Complex.re_ofReal_mul, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, mul_assoc]

/-! ### (d2) the jump side: the 1/γ² bound, uniform in δ, by two integrations by parts on (0, δ/2] -/

/-- **Two integrations by parts against `cos (γ u)`** on `[0, a]`. -/
theorem integral_mul_cos_ibp {k k' k'' : ℝ → ℝ} (a γ : ℝ) (hγ : γ ≠ 0)
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : ∀ x, HasDerivAt k' (k'' x) x) (hc : Continuous k'') :
    ∫ u in (0 : ℝ)..a, k u * Real.cos (γ * u)
      = k a * (Real.sin (γ * a) / γ) + (k' a * Real.cos (γ * a) - k' 0) / γ ^ 2
        - (∫ u in (0 : ℝ)..a, k'' u * Real.cos (γ * u)) / γ ^ 2 := by
  have hk'c : Continuous k' := continuous_iff_continuousAt.2 fun x => (hk' x).continuousAt
  have hs : ∀ x, HasDerivAt (fun u => Real.sin (γ * u) / γ) (Real.cos (γ * x)) x := by
    intro x
    have h := ((Real.hasDerivAt_sin (γ * x)).comp x ((hasDerivAt_id' x).const_mul γ)).div_const γ
    exact h.congr_deriv (by field_simp)
  have hc2 : ∀ x, HasDerivAt (fun u => -Real.cos (γ * u) / γ ^ 2) (Real.sin (γ * x) / γ) x := by
    intro x
    have h := (((Real.hasDerivAt_cos (γ * x)).comp x ((hasDerivAt_id' x).const_mul γ)).neg).div_const (γ ^ 2)
    exact h.congr_deriv (by field_simp <;> ring)
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := a) (fun x _ => hk x) (fun x _ => hs x)
    (hk'c.intervalIntegrable _ _) ((by fun_prop : Continuous fun x => Real.cos (γ * x)).intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := a) (fun x _ => hk' x) (fun x _ => hc2 x)
    (hc.intervalIntegrable _ _) ((by fun_prop : Continuous fun x => Real.sin (γ * x) / γ).intervalIntegrable _ _)
  have h3 : ∫ x in (0 : ℝ)..a, k'' x * (-Real.cos (γ * x) / γ ^ 2)
      = -(∫ x in (0 : ℝ)..a, k'' x * Real.cos (γ * x)) / γ ^ 2 := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_div]
    congr 1
    funext x
    ring
  rw [h1, h2, h3]
  simp only [mul_zero, Real.sin_zero, zero_div, Real.cos_zero]
  ring

theorem blPoly_contDiff_infty (n : ℕ) : ContDiff ℝ ∞ (blPoly n) := by
  unfold blPoly
  exact ContDiff.sum fun j _ => (contDiff_const.mul (contDiff_id.pow j)).div_const _

/-- `q_β(u) = P_n(u) e^{β u}` and its first two derivatives. -/
def qf (n : ℕ) (β u : ℝ) : ℝ := blPoly n u * Real.exp (β * u)

def qf1 (n : ℕ) (β u : ℝ) : ℝ := (deriv (blPoly n) u + β * blPoly n u) * Real.exp (β * u)

def qf2 (n : ℕ) (β u : ℝ) : ℝ :=
  (deriv (deriv (blPoly n)) u + 2 * β * deriv (blPoly n) u + β ^ 2 * blPoly n u) * Real.exp (β * u)

theorem exp_mul_hasDerivAt (β x : ℝ) : HasDerivAt (fun u => Real.exp (β * u)) (β * Real.exp (β * x)) x := by
  have h := (Real.hasDerivAt_exp (β * x)).comp x ((hasDerivAt_id' x).const_mul β)
  exact h.congr_deriv (by ring)

theorem qf_hasDerivAt (n : ℕ) (β x : ℝ) : HasDerivAt (qf n β) (qf1 n β x) x := by
  have hPd := (contDiff_infty_iff_deriv.mp (blPoly_contDiff_infty n)).1
  have h := (hPd x).hasDerivAt.mul (exp_mul_hasDerivAt β x)
  unfold qf qf1
  exact h.congr_deriv (by ring)

theorem qf1_hasDerivAt (n : ℕ) (β x : ℝ) : HasDerivAt (qf1 n β) (qf2 n β x) x := by
  obtain ⟨hPd, hP1⟩ := contDiff_infty_iff_deriv.mp (blPoly_contDiff_infty n)
  have hPd1 := (contDiff_infty_iff_deriv.mp hP1).1
  have h := (((hPd1 x).hasDerivAt.add ((hPd x).hasDerivAt.const_mul β))).mul (exp_mul_hasDerivAt β x)
  unfold qf1 qf2
  exact h.congr_deriv (by simp only [Pi.add_apply, Pi.mul_apply]; ring)

theorem qf_bounds (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ x ∈ Icc (-1 : ℝ) 1,
    |qf1 n β x| ≤ K ∧ |qf2 n β x| ≤ K := by
  obtain ⟨hPd, hP1⟩ := contDiff_infty_iff_deriv.mp (blPoly_contDiff_infty n)
  have hP2 := (contDiff_infty_iff_deriv.mp hP1).2
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn (blPoly_contDiff_infty n).continuous.continuousOn
    (s := Icc (-1 : ℝ) 1)
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hP1.continuous.continuousOn (s := Icc (-1 : ℝ) 1)
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hP2.continuous.continuousOn (s := Icc (-1 : ℝ) 1)
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hM0p : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 h0)
  have hM1p : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 h0)
  have hM2p : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 h0)
  refine ⟨(M2 + 2 * M1 + M0) * Real.exp 1, by positivity, fun β hβ0 hβ1 x hx => ?_⟩
  have e0 : |blPoly n x| ≤ M0 := by simpa [Real.norm_eq_abs] using hM0 x hx
  have e1 : |deriv (blPoly n) x| ≤ M1 := by simpa [Real.norm_eq_abs] using hM1 x hx
  have e2 : |deriv (deriv (blPoly n)) x| ≤ M2 := by simpa [Real.norm_eq_abs] using hM2 x hx
  have hE : Real.exp (β * x) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have := abs_le.mp (show |x| ≤ 1 from abs_le.mpr ⟨hx.1, hx.2⟩)
    nlinarith
  have hE0 : 0 ≤ Real.exp (β * x) := (Real.exp_pos _).le
  have hβ2 : β ^ 2 ≤ 1 := by nlinarith
  constructor
  · unfold qf1
    rw [abs_mul, abs_of_nonneg hE0]
    have ha : |deriv (blPoly n) x + β * blPoly n x| ≤ M2 + 2 * M1 + M0 := by
      calc |deriv (blPoly n) x + β * blPoly n x| ≤ |deriv (blPoly n) x| + |β| * |blPoly n x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ M1 + 1 * M0 := by
            gcongr
            rw [abs_of_nonneg hβ0]; exact hβ1
        _ ≤ M2 + 2 * M1 + M0 := by linarith
    exact mul_le_mul ha hE hE0 (by positivity)
  · unfold qf2
    rw [abs_mul, abs_of_nonneg hE0]
    have ha : |deriv (deriv (blPoly n)) x + 2 * β * deriv (blPoly n) x + β ^ 2 * blPoly n x| ≤ M2 + 2 * M1 + M0 := by
      calc |deriv (deriv (blPoly n)) x + 2 * β * deriv (blPoly n) x + β ^ 2 * blPoly n x|
          ≤ |deriv (deriv (blPoly n)) x| + |2 * β| * |deriv (blPoly n) x| + |β ^ 2| * |blPoly n x| := by
            rw [← abs_mul, ← abs_mul]
            exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ M2 + 2 * M1 + 1 * M0 := by
            gcongr
            · rw [abs_of_nonneg (by positivity)]; linarith
            · rw [abs_of_nonneg (by positivity)]; exact hβ2
        _ = M2 + 2 * M1 + M0 := by ring
    exact mul_le_mul ha hE hE0 (by positivity)

/-- The jump cut on `(0, δ/2]`: `w(u) = st(1/2 - u/δ)` and its derivatives. -/
def wf (δ u : ℝ) : ℝ := Real.smoothTransition (1 / 2 - u / δ)

def wf1 (δ u : ℝ) : ℝ := deriv Real.smoothTransition (1 / 2 - u / δ) * (-(1 / δ))

def wf2 (δ u : ℝ) : ℝ := deriv (deriv Real.smoothTransition) (1 / 2 - u / δ) * (-(1 / δ)) * (-(1 / δ))

theorem wf_hasDerivAt (δ x : ℝ) : HasDerivAt (wf δ) (wf1 δ x) x := by
  have hstd := (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).1
  exact (hstd _).hasDerivAt.comp x (((hasDerivAt_id' x).div_const δ).const_sub (1 / 2))

theorem wf1_hasDerivAt (δ x : ℝ) : HasDerivAt (wf1 δ) (wf2 δ x) x := by
  have hst1 := (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2
  have hstd1 := (contDiff_infty_iff_deriv.mp hst1).1
  exact ((hstd1 _).hasDerivAt.comp x (((hasDerivAt_id' x).div_const δ).const_sub (1 / 2))).mul_const _

/-- (d2) **The jump side, uniform in δ:** for `0 < δ ≤ 1`, `0 ≤ β ≤ 1`, `γ ≠ 0`,
`|∫_0^{δ/2} st(1/2 - u/δ) (q_β(u) - q_β(-u)) cos(γ u) du| ≤ C / γ²`, `C` depending on `n` alone -- the real part of the
jump side of the excess, the jump's value `q(0) = n` cancelled by the cut's oddness (relay `data/b563_decay_read.txt` (2), (4)). -/
theorem jump_cos_bound (n : ℕ) : ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ γ : ℝ, γ ≠ 0 →
    |∫ u in (0 : ℝ)..(δ / 2), wf δ u * (qf n β u - qf n β (-u)) * Real.cos (γ * u)| ≤ C / γ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := qf_bounds n
  have hst1 := (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2
  have hst2 := (contDiff_infty_iff_deriv.mp hst1).2
  obtain ⟨S1, hS1⟩ := isCompact_Icc.exists_bound_of_continuousOn hst1.continuous.continuousOn (s := Icc (0 : ℝ) 1)
  obtain ⟨S2, hS2⟩ := isCompact_Icc.exists_bound_of_continuousOn hst2.continuous.continuousOn (s := Icc (0 : ℝ) 1)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hS1p : 0 ≤ S1 := (norm_nonneg _).trans (hS1 0 h0)
  have hS2p : 0 ≤ S2 := (norm_nonneg _).trans (hS2 0 h0)
  refine ⟨S1 * K + 2 * K + (S2 * K + 4 * S1 * K) / 2 + 2 * K, fun δ hδ hδ1 β hβ0 hβ1 γ hγ => ?_⟩
  -- the pieces on [0, 1]
  have hD : ∀ u ∈ Icc (0 : ℝ) 1, |qf n β u - qf n β (-u)| ≤ 2 * K * u := by
    intro u hu
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := qf n β) (f' := qf1 n β) (s := Icc (-1 : ℝ) 1)
      (fun x _ => (qf_hasDerivAt n β x).hasDerivWithinAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact (hK β hβ0 hβ1 x hx).1) (convex_Icc _ _)
      (show -u ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (show u ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hu.1], hu.2⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show u - -u = 2 * u by ring, abs_of_nonneg (show (0 : ℝ) ≤ 2 * u by linarith [hu.1])] at hm
    linarith
  have hD1 : ∀ u ∈ Icc (0 : ℝ) 1, |qf1 n β u + qf1 n β (-u)| ≤ 2 * K := by
    intro u hu
    have a1 := (hK β hβ0 hβ1 u ⟨by linarith [hu.1], hu.2⟩).1
    have a2 := (hK β hβ0 hβ1 (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).1
    exact (abs_add_le _ _).trans (by linarith)
  have hD2 : ∀ u ∈ Icc (0 : ℝ) 1, |qf2 n β u - qf2 n β (-u)| ≤ 2 * K := by
    intro u hu
    have a1 := (hK β hβ0 hβ1 u ⟨by linarith [hu.1], hu.2⟩).2
    have a2 := (hK β hβ0 hβ1 (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).2
    exact (abs_sub _ _).trans (by linarith)
  have harg : ∀ u ∈ Icc (0 : ℝ) (δ / 2), 1 / 2 - u / δ ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    have h1 : u / δ ≤ 1 / 2 := by rw [div_le_iff₀ hδ]; linarith [hu.2]
    have h2 : 0 ≤ u / δ := div_nonneg hu.1 hδ.le
    exact ⟨by linarith, by linarith⟩
  have hw0 : ∀ u, |wf δ u| ≤ 1 := fun u => by
    unfold wf; rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have hw1 : ∀ u ∈ Icc (0 : ℝ) (δ / 2), |wf1 δ u| ≤ S1 / δ := by
    intro u hu
    unfold wf1
    rw [abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hδ), mul_one_div]
    exact div_le_div_of_nonneg_right (by simpa [Real.norm_eq_abs] using hS1 _ (harg u hu)) hδ.le
  have hw2 : ∀ u ∈ Icc (0 : ℝ) (δ / 2), |wf2 δ u| ≤ S2 / δ ^ 2 := by
    intro u hu
    unfold wf2
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hδ), mul_assoc, one_div_mul_one_div, ← sq, mul_one_div]
    exact div_le_div_of_nonneg_right (by simpa [Real.norm_eq_abs] using hS2 _ (harg u hu)) (by positivity)
  have hsub : ∀ u ∈ Icc (0 : ℝ) (δ / 2), u ∈ Icc (0 : ℝ) 1 := fun u hu => ⟨hu.1, by linarith [hu.2]⟩
  -- the integration by parts
  set k : ℝ → ℝ := fun u => wf δ u * (qf n β u - qf n β (-u)) with hkdef
  set k1 : ℝ → ℝ := fun u => wf1 δ u * (qf n β u - qf n β (-u)) + wf δ u * (qf1 n β u + qf1 n β (-u)) with hk1def
  set k2 : ℝ → ℝ := fun u => wf2 δ u * (qf n β u - qf n β (-u)) + 2 * (wf1 δ u * (qf1 n β u + qf1 n β (-u)))
    + wf δ u * (qf2 n β u - qf2 n β (-u)) with hk2def
  have hqn : ∀ x, HasDerivAt (fun u => qf n β (-u)) (-qf1 n β (-x)) x := fun x => by
    have h := (qf_hasDerivAt n β (-x)).comp x (hasDerivAt_neg x)
    exact h.congr_deriv (by ring)
  have hq1n : ∀ x, HasDerivAt (fun u => qf1 n β (-u)) (-qf2 n β (-x)) x := fun x => by
    have h := (qf1_hasDerivAt n β (-x)).comp x (hasDerivAt_neg x)
    exact h.congr_deriv (by ring)
  have hk : ∀ x, HasDerivAt k (k1 x) x := fun x => by
    have h := (wf_hasDerivAt δ x).mul ((qf_hasDerivAt n β x).sub (hqn x))
    exact h.congr_deriv (by simp only [hk1def, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring)
  have hk1 : ∀ x, HasDerivAt k1 (k2 x) x := fun x => by
    have h := ((wf1_hasDerivAt δ x).mul ((qf_hasDerivAt n β x).sub (hqn x))).add
      ((wf_hasDerivAt δ x).mul ((qf1_hasDerivAt n β x).add (hq1n x)))
    exact h.congr_deriv (by simp only [hk2def, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring)
  have hk2c : Continuous k2 := by
    have hst1c := hst1.continuous
    have hst2c := hst2.continuous
    obtain ⟨_, hP1⟩ := contDiff_infty_iff_deriv.mp (blPoly_contDiff_infty n)
    have hP2c := (contDiff_infty_iff_deriv.mp hP1).2.continuous
    have hP1c := hP1.continuous
    have hPc := (blPoly_contDiff_infty n).continuous
    simp only [hk2def, wf, wf1, wf2, qf, qf1, qf2]
    fun_prop
  have hibp := integral_mul_cos_ibp (δ / 2) γ hγ hk hk1 hk2c
  have hka : k (δ / 2) = 0 := by
    simp only [hkdef, wf, show 1 / 2 - δ / 2 / δ = 0 by field_simp <;> ring, Real.smoothTransition.zero, zero_mul]
  have hk1a : |k1 (δ / 2)| ≤ S1 * K := by
    have hwa : wf δ (δ / 2) = 0 := by simp only [wf, show 1 / 2 - δ / 2 / δ = 0 by field_simp <;> ring, Real.smoothTransition.zero]
    have hmem : δ / 2 ∈ Icc (0 : ℝ) (δ / 2) := ⟨by linarith, le_rfl⟩
    simp only [hk1def, hwa, zero_mul, add_zero]
    rw [abs_mul]
    calc |wf1 δ (δ / 2)| * |qf n β (δ / 2) - qf n β (-(δ / 2))| ≤ (S1 / δ) * (2 * K * (δ / 2)) :=
          mul_le_mul (hw1 _ hmem) (hD _ (hsub _ hmem)) (abs_nonneg _) (by positivity)
      _ = S1 * K := by field_simp <;> ring
  have hk10 : |k1 0| ≤ 2 * K := by
    have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) (δ / 2) := ⟨le_rfl, by linarith⟩
    simp only [hk1def, neg_zero, sub_self, mul_zero, zero_add]
    rw [abs_mul]
    calc |wf δ 0| * |qf1 n β 0 + qf1 n β 0| ≤ 1 * (2 * K) :=
          mul_le_mul (hw0 0) (by simpa using hD1 0 (hsub 0 hmem)) (abs_nonneg _) zero_le_one
      _ = 2 * K := one_mul _
  have hI : |∫ u in (0 : ℝ)..(δ / 2), k2 u * Real.cos (γ * u)| ≤ (S2 * K + 4 * S1 * K) / 2 + 2 * K := by
    have hb : ∀ x ∈ Ι (0 : ℝ) (δ / 2), ‖k2 x * Real.cos (γ * x)‖ ≤ (S2 * K + 4 * S1 * K) / δ + 4 * K := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      have hmem : x ∈ Icc (0 : ℝ) (δ / 2) := ⟨hx.1.le, hx.2⟩
      have hx1 := hsub x hmem
      rw [Real.norm_eq_abs, abs_mul]
      have hc : |Real.cos (γ * x)| ≤ 1 := Real.abs_cos_le_one _
      have t1 : |wf2 δ x * (qf n β x - qf n β (-x))| ≤ S2 * K / δ := by
        rw [abs_mul]
        calc |wf2 δ x| * |qf n β x - qf n β (-x)| ≤ (S2 / δ ^ 2) * (2 * K * (δ / 2)) :=
              mul_le_mul (hw2 x hmem) ((hD x hx1).trans (by nlinarith [hmem.2])) (abs_nonneg _) (by positivity)
          _ = S2 * K / δ := by field_simp <;> ring
      have t2 : |2 * (wf1 δ x * (qf1 n β x + qf1 n β (-x)))| ≤ 4 * S1 * K / δ := by
        rw [abs_mul, abs_mul, abs_two]
        calc 2 * (|wf1 δ x| * |qf1 n β x + qf1 n β (-x)|) ≤ 2 * ((S1 / δ) * (2 * K)) := by
              gcongr
              · exact hw1 x hmem
              · exact hD1 x hx1
          _ = 4 * S1 * K / δ := by field_simp <;> ring
      have t3 : |wf δ x * (qf2 n β x - qf2 n β (-x))| ≤ 2 * K := by
        rw [abs_mul]
        calc |wf δ x| * |qf2 n β x - qf2 n β (-x)| ≤ 1 * (2 * K) :=
              mul_le_mul (hw0 x) (hD2 x hx1) (abs_nonneg _) zero_le_one
          _ = 2 * K := one_mul _
      have tk : |k2 x| ≤ (S2 * K + 4 * S1 * K) / δ + 4 * K := by
        have e : (S2 * K + 4 * S1 * K) / δ = S2 * K / δ + 4 * S1 * K / δ := by ring
        simp only [hk2def]
        calc _ ≤ |wf2 δ x * (qf n β x - qf n β (-x))| + |2 * (wf1 δ x * (qf1 n β x + qf1 n β (-x)))|
              + |wf δ x * (qf2 n β x - qf2 n β (-x))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ S2 * K / δ + 4 * S1 * K / δ + 2 * K := by linarith
          _ ≤ (S2 * K + 4 * S1 * K) / δ + 4 * K := by rw [e]; linarith
      calc |k2 x| * |Real.cos (γ * x)| ≤ ((S2 * K + 4 * S1 * K) / δ + 4 * K) * 1 :=
            mul_le_mul tk hc (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < δ / 2)] at h
    calc _ ≤ ((S2 * K + 4 * S1 * K) / δ + 4 * K) * (δ / 2) := h
      _ = (S2 * K + 4 * S1 * K) / 2 + 2 * K * δ := by field_simp <;> ring
      _ ≤ (S2 * K + 4 * S1 * K) / 2 + 2 * K := by nlinarith
  -- assembling
  have hg2 : 0 < γ ^ 2 := by positivity
  show |∫ u in (0 : ℝ)..(δ / 2), k u * Real.cos (γ * u)| ≤ _
  rw [hibp, hka, zero_mul, zero_add]
  have hc : |Real.cos (γ * (δ / 2))| ≤ 1 := Real.abs_cos_le_one _
  have hnum : |k1 (δ / 2) * Real.cos (γ * (δ / 2)) - k1 0| ≤ S1 * K + 2 * K := by
    calc _ ≤ |k1 (δ / 2) * Real.cos (γ * (δ / 2))| + |k1 0| := abs_sub _ _
      _ ≤ S1 * K * 1 + 2 * K := by
          rw [abs_mul]
          gcongr
      _ = S1 * K + 2 * K := by ring
  rw [← sub_div, abs_div, abs_of_pos hg2]
  apply div_le_div_of_nonneg_right _ hg2.le
  calc _ ≤ |k1 (δ / 2) * Real.cos (γ * (δ / 2)) - k1 0| + |∫ u in (0 : ℝ)..(δ / 2), k2 u * Real.cos (γ * u)| := abs_sub _ _
    _ ≤ (S1 * K + 2 * K) + ((S2 * K + 4 * S1 * K) / 2 + 2 * K) := add_le_add hnum hI
    _ = _ := by ring

/-! ### (d3) the left edge, uniform as `Re ρ → 0`: iterated integration by parts on fixed compactly supported profiles -/

/-- **One integration by parts against `e^{τ v}`** for a smooth compactly supported `g`. -/
theorem integral_mul_cexp_ibp {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) {τ : ℂ} (hτ : τ ≠ 0) :
    ∫ v : ℝ, g v * cexp (τ * v) = (-1 / τ) * ∫ v : ℝ, deriv g v * cexp (τ * v) := by
  obtain ⟨hgd, hg1⟩ := contDiff_infty_iff_deriv.mp hg
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (τ * y) / τ) (cexp (τ * x)) x := by
    intro x
    have h := (((hasDerivAt_id' (x : ℂ)).const_mul τ).cexp.comp_ofReal).div_const τ
    exact h.congr_deriv (by field_simp)
  have hint1 : Integrable (g * fun x : ℝ => cexp (τ * x)) :=
    (hgd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  have hint2 : Integrable (deriv g * fun x : ℝ => cexp (τ * x) / τ) :=
    (hg1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hs.deriv.mul_right
  have hlim : Tendsto (g * fun x : ℝ => cexp (τ * x) / τ) (Filter.cocompact ℝ) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hs.isCompact.compl_mem_cocompact] with x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have h := integral_mul_deriv_eq_deriv_mul (u := g) (u' := deriv g) (fun x _ => (hgd x).hasDerivAt)
    (fun x _ => hv x) hint1 hint2 (hlim.mono_left atBot_le_cocompact) (hlim.mono_left atTop_le_cocompact)
  rw [h, sub_zero, zero_sub, ← integral_neg, ← integral_const_mul]
  congr 1
  funext x
  field_simp

/-- **Iterated:** `∫ g e^{τ v} = (-1/τ)^m ∫ g^{(m)} e^{τ v}` for a smooth compactly supported `g`. -/
theorem integral_mul_cexp_ibp_iter {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) {τ : ℂ} (hτ : τ ≠ 0) :
    ∀ m : ℕ, ∫ v : ℝ, g v * cexp (τ * v) = (-1 / τ) ^ m * ∫ v : ℝ, iteratedDeriv m g v * cexp (τ * v) := by
  have hreg : ∀ m : ℕ, ContDiff ℝ ∞ (iteratedDeriv m g) ∧ HasCompactSupport (iteratedDeriv m g) := by
    intro m
    induction m with
    | zero => simpa using ⟨hg, hs⟩
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ⟨(contDiff_infty_iff_deriv.mp ih.1).2, ih.2.deriv⟩
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, integral_mul_cexp_ibp (hreg m).1 (hreg m).2 hτ, ← iteratedDeriv_succ, pow_succ, mul_assoc]

/-- The left-edge profile `st'(v + 2) · v^j`: smooth, supported in `[-2, -1]`. -/
def edgeProfile (j : ℕ) (v : ℝ) : ℂ := ((deriv Real.smoothTransition (v + 2) * v ^ j : ℝ) : ℂ)

theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) : deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]

theorem edgeProfile_contDiff (j : ℕ) : ContDiff ℝ ∞ (edgeProfile j) := by
  have hst1 := (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2
  unfold edgeProfile
  exact Complex.ofRealCLM.contDiff.comp ((hst1.comp (contDiff_id.add contDiff_const)).mul (contDiff_id.pow j))

theorem edgeProfile_eq_zero (j : ℕ) {v : ℝ} (hv : v < -2 ∨ -1 < v) : edgeProfile j v = 0 := by
  unfold edgeProfile
  rw [deriv_smoothTransition_eq_zero (by rcases hv with h | h; exact Or.inl (by linarith); exact Or.inr (by linarith)),
    zero_mul, Complex.ofReal_zero]

theorem edgeProfile_hasCompactSupport (j : ℕ) : HasCompactSupport (edgeProfile j) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := -1)) (fun v hv => ?_)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  exact edgeProfile_eq_zero j hv

/-- **The profile's transform decays:** `‖∫ st'(v+2) v^j e^{τ v} dv‖ ≤ A / ‖τ‖^m` for `Re τ ≥ 0`, `τ ≠ 0`, every `m`. -/
theorem edgeProfile_bound (j m : ℕ) : ∃ A : ℝ, ∀ τ : ℂ, 0 ≤ τ.re → τ ≠ 0 →
    ‖∫ v : ℝ, edgeProfile j v * cexp (τ * v)‖ ≤ A / ‖τ‖ ^ m := by
  have hg := edgeProfile_contDiff j
  have hs := edgeProfile_hasCompactSupport j
  have hreg : ContDiff ℝ ∞ (iteratedDeriv m (edgeProfile j)) ∧ HasCompactSupport (iteratedDeriv m (edgeProfile j)) := by
    induction m with
    | zero => simpa using ⟨hg, hs⟩
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ⟨(contDiff_infty_iff_deriv.mp ih.1).2, ih.2.deriv⟩
  have hzero : ∀ v : ℝ, -1 < v → iteratedDeriv m (edgeProfile j) v = 0 := by
    intro v hv
    have hE : Set.EqOn (edgeProfile j) (fun _ => (0 : ℂ)) (Ioi (-1)) := fun y hy => edgeProfile_eq_zero j (Or.inr hy)
    rw [hE.iteratedDeriv_of_isOpen isOpen_Ioi m hv]
    simp
  refine ⟨∫ v : ℝ, ‖iteratedDeriv m (edgeProfile j) v‖, fun τ hτ hτ0 => ?_⟩
  rw [integral_mul_cexp_ibp_iter hg hs hτ0 m, norm_mul, norm_pow, norm_div, norm_neg, norm_one]
  have hb : ‖∫ v : ℝ, iteratedDeriv m (edgeProfile j) v * cexp (τ * v)‖ ≤ ∫ v : ℝ, ‖iteratedDeriv m (edgeProfile j) v‖ := by
    refine norm_integral_le_of_norm_le (hreg.1.continuous.norm.integrable_of_hasCompactSupport hreg.2.norm)
      (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : -1 < v
    · rw [hzero v hv, zero_mul, norm_zero]
    · rw [norm_mul, Complex.norm_exp]
      have hre : (τ * (v : ℂ)).re ≤ 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        nlinarith [not_lt.mp hv]
      calc ‖iteratedDeriv m (edgeProfile j) v‖ * Real.exp (τ * (v : ℂ)).re
          ≤ ‖iteratedDeriv m (edgeProfile j) v‖ * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hre) (norm_nonneg _)
        _ = _ := mul_one _
  have hτp : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  calc (1 / ‖τ‖) ^ m * ‖∫ v : ℝ, iteratedDeriv m (edgeProfile j) v * cexp (τ * v)‖
      ≤ (1 / ‖τ‖) ^ m * ∫ v : ℝ, ‖iteratedDeriv m (edgeProfile j) v‖ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [one_div_pow, one_div_mul_eq_div]

/-- A cut `h` (`|h| ≤ 1`, `h = 0` on `[0, ∞)`) times `u^j e^{τ u}` is integrable for `Re τ > 0` -- b561's
`integrableOn_pow_mul_cexp` reflected. -/
theorem integrable_cut_pow_cexp {h : ℝ → ℝ} (hc : Continuous h) (h1 : ∀ u, |h u| ≤ 1) (h0 : ∀ u, 0 ≤ u → h u = 0)
    (j : ℕ) {τ : ℂ} (hτ : 0 < τ.re) : Integrable (fun u : ℝ => ((h u * u ^ j : ℝ) : ℂ) * cexp (τ * u)) := by
  have hI := (integrableOn_pow_mul_cexp hτ j).comp_neg
  rw [Set.neg_Ioi, neg_zero] at hI
  have heq : (fun u : ℝ => ((h u * u ^ j : ℝ) : ℂ) * cexp (τ * u))
      = (Iio (0 : ℝ)).indicator (fun u : ℝ => ((h u * u ^ j : ℝ) : ℂ) * cexp (τ * u)) := by
    funext u
    by_cases hu : u < 0
    · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
    · rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu), h0 u (not_lt.mp hu), zero_mul, Complex.ofReal_zero, zero_mul]
  rw [heq, integrable_indicator_iff measurableSet_Iio]
  refine hI.norm.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Iio).mpr (Filter.Eventually.of_forall fun u _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_pow, Complex.norm_exp, Complex.norm_exp]
  have e : (τ * (u : ℂ)).re = (-(τ * ((-u : ℝ) : ℂ))).re := by push_cast; ring_nf
  rw [e]
  have hp : 0 ≤ |u| ^ j * Real.exp (-(τ * ((-u : ℝ) : ℂ))).re := by positivity
  nlinarith [h1 u, abs_nonneg (h u)]

/-- The left-edge tail `ψ_j(v) = (st(v + 2) - 1) v^j`: zero for `v ≥ -1`. -/
def edgeTail (j : ℕ) (v : ℝ) : ℂ := (((Real.smoothTransition (v + 2) - 1) * v ^ j : ℝ) : ℂ)

theorem edgeCut_abs (v : ℝ) : |Real.smoothTransition (v + 2) - 1| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [Real.smoothTransition.nonneg (v + 2), Real.smoothTransition.le_one (v + 2)]

theorem edgeTail_integrable (j : ℕ) {τ : ℂ} (hτ : 0 < τ.re) : Integrable (fun v : ℝ => edgeTail j v * cexp (τ * v)) :=
  integrable_cut_pow_cexp (h := fun v => Real.smoothTransition (v + 2) - 1) (by fun_prop) edgeCut_abs
    (fun v hv => by rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]) j hτ

theorem edgeTail_hasDerivAt (j : ℕ) (v : ℝ) :
    HasDerivAt (edgeTail j) (edgeProfile j v + (j : ℂ) * (((Real.smoothTransition (v + 2) - 1) * v ^ (j - 1) : ℝ) : ℂ)) v := by
  have hstd := (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).1
  have h1 := ((hstd (v + 2)).hasDerivAt.comp v ((hasDerivAt_id' v).add_const 2)).sub_const 1
  have h := (h1.mul (hasDerivAt_pow j v)).ofReal_comp
  unfold edgeTail edgeProfile
  exact h.congr_deriv (by
    simp only [Function.comp_apply, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_natCast, mul_one]
    ring)

/-- **One integration by parts for the tail**, on the whole line (the tail decays like `v^j e^{Re τ v}` at `-∞`). -/
theorem edgeTail_ibp (j : ℕ) {τ : ℂ} (hτ : 0 < τ.re) :
    ∫ v : ℝ, edgeTail j v * cexp (τ * v)
      = (-1 / τ) * ∫ v : ℝ, (edgeProfile j v + (j : ℂ) * (((Real.smoothTransition (v + 2) - 1) * v ^ (j - 1) : ℝ) : ℂ))
          * cexp (τ * v) := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hτ; exact lt_irrefl _ hτ
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (τ * y) / τ) (cexp (τ * x)) x := by
    intro x
    have h := (((hasDerivAt_id' (x : ℂ)).const_mul τ).cexp.comp_ofReal).div_const τ
    exact h.congr_deriv (by field_simp)
  have hint1 : Integrable (edgeTail j * fun x : ℝ => cexp (τ * x)) := edgeTail_integrable j hτ
  have hIt : Integrable (fun v : ℝ => (((Real.smoothTransition (v + 2) - 1) * v ^ (j - 1) : ℝ) : ℂ) * cexp (τ * v)) :=
    integrable_cut_pow_cexp (h := fun v => Real.smoothTransition (v + 2) - 1) (by fun_prop) edgeCut_abs
      (fun v hv => by rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]) (j - 1) hτ
  have hIp : Integrable (fun v : ℝ => edgeProfile j v * cexp (τ * v)) :=
    ((edgeProfile_contDiff j).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (edgeProfile_hasCompactSupport j).mul_right
  have hint2 : Integrable ((fun v : ℝ => edgeProfile j v + (j : ℂ) * (((Real.smoothTransition (v + 2) - 1) * v ^ (j - 1) : ℝ) : ℂ))
      * fun x : ℝ => cexp (τ * x) / τ) := by
    have h := (hIp.add (hIt.const_mul (j : ℂ))).div_const τ
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  have htop : Tendsto (edgeTail j * fun x : ℝ => cexp (τ * x) / τ) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Pi.mul_apply, edgeTail]
    rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self, zero_mul, Complex.ofReal_zero, zero_mul]
  have hbot : Tendsto (edgeTail j * fun x : ℝ => cexp (τ * x) / τ) atBot (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => (τ.re * x) ^ j * Real.exp (-(τ.re * x))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp (tendsto_id.const_mul_atTop hτ)
    have hb' := ((hb.const_mul ((1 / τ.re) ^ j / ‖τ‖)).comp tendsto_neg_atBot_atTop)
    rw [mul_zero] at hb'
    refine squeeze_zero_norm' ?_ hb'
    filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
    simp only [Pi.mul_apply, edgeTail, Function.comp_apply]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_exp]
    have hre : (τ * (x : ℂ)).re = -(τ.re * -x) := by simp [Complex.mul_re]
    rw [hre, abs_pow, abs_of_nonpos hx]
    have e : (-x) ^ j = (1 / τ.re) ^ j * (τ.re * -x) ^ j := by rw [← mul_pow]; congr 1; field_simp
    have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
    have hc := edgeCut_abs x
    calc |Real.smoothTransition (x + 2) - 1| * (-x) ^ j * (Real.exp (-(τ.re * -x)) / ‖τ‖)
        ≤ 1 * (-x) ^ j * (Real.exp (-(τ.re * -x)) / ‖τ‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) j)) (by positivity)
      _ = (1 / τ.re) ^ j / ‖τ‖ * ((τ.re * -x) ^ j * Real.exp (-(τ.re * -x))) := by rw [e]; field_simp
  have h := integral_mul_deriv_eq_deriv_mul (u := edgeTail j) (fun x _ => edgeTail_hasDerivAt j x) (fun x _ => hv x)
    hint1 hint2 hbot htop
  rw [h, sub_zero, zero_sub, ← integral_neg, ← integral_const_mul]
  congr 1
  funext x
  field_simp

/-- **The tail's transform decays:** `‖∫ ψ_j(v) e^{τ v} dv‖ ≤ B / ‖τ‖^{j+2}` for `Re τ > 0`. -/
theorem edgeTail_bound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℂ, 0 < τ.re → ‖∫ v : ℝ, edgeTail j v * cexp (τ * v)‖ ≤ B / ‖τ‖ ^ (j + 2) := by
  induction j with
  | zero =>
    obtain ⟨A, hA⟩ := edgeProfile_bound 0 1
    have hA0 : 0 ≤ A := by
      have h := hA 1 (by norm_num) one_ne_zero
      rw [norm_one, one_pow, div_one] at h
      exact (norm_nonneg _).trans h
    refine ⟨A, hA0, fun τ hτ => ?_⟩
    have hτ0 : τ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hτ; exact lt_irrefl _ hτ
    have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
    rw [edgeTail_ibp 0 hτ]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [norm_mul, norm_div, norm_neg, norm_one]
    calc 1 / ‖τ‖ * ‖∫ v : ℝ, edgeProfile 0 v * cexp (τ * v)‖ ≤ 1 / ‖τ‖ * (A / ‖τ‖ ^ 1) :=
          mul_le_mul_of_nonneg_left (hA τ hτ.le hτ0) (by positivity)
      _ = A / ‖τ‖ ^ (0 + 2) := by rw [pow_one, show (0 : ℕ) + 2 = 2 from rfl, sq]; field_simp
  | succ j ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    obtain ⟨A, hA⟩ := edgeProfile_bound (j + 1) (j + 2)
    have hA0 : 0 ≤ A := by
      have h := hA 1 (by norm_num) one_ne_zero
      rw [norm_one, one_pow, div_one] at h
      exact (norm_nonneg _).trans h
    refine ⟨A + (j + 1) * B, by positivity, fun τ hτ => ?_⟩
    have hτ0 : τ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hτ; exact lt_irrefl _ hτ
    have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
    rw [edgeTail_ibp (j + 1) hτ, Nat.add_sub_cancel]
    have hIp : Integrable (fun v : ℝ => edgeProfile (j + 1) v * cexp (τ * v)) :=
      ((edgeProfile_contDiff (j + 1)).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (edgeProfile_hasCompactSupport (j + 1)).mul_right
    have hIt := edgeTail_integrable j hτ
    have hsplit : ∫ v : ℝ, (edgeProfile (j + 1) v + ((j + 1 : ℕ) : ℂ) * (((Real.smoothTransition (v + 2) - 1) * v ^ j : ℝ) : ℂ))
        * cexp (τ * v) = (∫ v : ℝ, edgeProfile (j + 1) v * cexp (τ * v))
          + ((j + 1 : ℕ) : ℂ) * ∫ v : ℝ, edgeTail j v * cexp (τ * v) := by
      rw [← integral_const_mul, ← integral_add hIp (hIt.const_mul _)]
      congr 1
      funext v
      unfold edgeTail
      ring
    rw [hsplit, norm_mul, norm_div, norm_neg, norm_one]
    have h1 := hA τ hτ.le hτ0
    have h2 := hB τ hτ
    have hn : ‖((j + 1 : ℕ) : ℂ)‖ = j + 1 := by rw [Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    calc 1 / ‖τ‖ * ‖(∫ v : ℝ, edgeProfile (j + 1) v * cexp (τ * v)) + ((j + 1 : ℕ) : ℂ) * ∫ v : ℝ, edgeTail j v * cexp (τ * v)‖
        ≤ 1 / ‖τ‖ * (A / ‖τ‖ ^ (j + 2) + (j + 1) * (B / ‖τ‖ ^ (j + 2))) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add h1 ?_)
          rw [norm_mul, hn]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (A + (j + 1) * B) / ‖τ‖ ^ (j + 1 + 2) := by field_simp; ring

/-- (d3) **The left edge, uniform as `Re ρ → 0`:** for `0 < δ ≤ 1`, `Re ρ > 0` and `‖ρ‖ ≥ 1`,
`‖∫ (st(δ u + 2) - 1) P_n(u) e^{ρ u} du‖ ≤ C / ‖ρ‖²`, `C` depending on `n` alone (relay `data/b563_decay_read.txt` (5)): by the
scaling `u = v/δ` each monomial becomes the tail `ψ_j` at `τ = ρ/δ`. -/
theorem left_edge_bound (n : ℕ) : ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ρ : ℂ, 0 < ρ.re → 1 ≤ ‖ρ‖ →
    ‖∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)‖ ≤ C / ‖ρ‖ ^ 2 := by
  choose B hB0 hB using edgeTail_bound
  refine ⟨∑ j ∈ Finset.range n, ((n.choose (j + 1) : ℝ) / (j.factorial : ℝ)) * B j, fun δ hδ hδ1 ρ hρ hρ1 => ?_⟩
  set R : ℝ := 1 / δ with hR
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hδ]; linarith
  have hRp : 0 < R := by linarith
  have hτ : 0 < (ρ * (R : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; positivity
  have hρn : 0 < ‖ρ‖ := by linarith
  -- each monomial, scaled
  have hmono : ∀ j : ℕ, ∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)
      = ((R ^ (j + 1) : ℝ) : ℂ) * ∫ v : ℝ, edgeTail j v * cexp ((ρ * (R : ℂ)) * v) := by
    intro j
    have hs := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => (((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)) R
    have hc : ∀ v : ℝ, (((Real.smoothTransition (δ * (R * v) + 2) - 1) * (R * v) ^ j : ℝ) : ℂ) * cexp (ρ * ((R * v : ℝ) : ℂ))
        = ((R ^ j : ℝ) : ℂ) * (edgeTail j v * cexp ((ρ * (R : ℂ)) * v)) := by
      intro v
      have hdR : δ * (R * v) = v := by rw [hR]; field_simp
      unfold edgeTail
      rw [hdR]
      push_cast
      ring_nf
    simp_rw [hc] at hs
    rw [integral_const_mul, abs_inv, abs_of_pos hRp, Complex.real_smul] at hs
    have e2 : ∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)
        = ((R : ℝ) : ℂ) * (((R ^ j : ℝ) : ℂ) * ∫ v : ℝ, edgeTail j v * cexp ((ρ * (R : ℂ)) * v)) := by
      rw [hs, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hRp.ne', Complex.ofReal_one, one_mul]
    rw [e2]
    push_cast
    ring
  -- the polynomial, monomial by monomial
  have hint : ∀ j : ℕ, Integrable (fun u : ℝ => (((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)) :=
    fun j => integrable_cut_pow_cexp (h := fun u => Real.smoothTransition (δ * u + 2) - 1) (by fun_prop)
      (fun u => edgeCut_abs (δ * u))
      (fun u hu => by rw [Real.smoothTransition.one_of_one_le (by have := mul_nonneg hδ.le hu; linarith), sub_self]) j hρ
  have hexp : ∀ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
      = ∑ j ∈ Finset.range n, (((n.choose (j + 1) : ℝ) / (j.factorial : ℝ) : ℝ) : ℂ)
          * ((((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)) := by
    intro u
    unfold blPoly
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun j _ => (hint j).const_mul _)]
  simp_rw [integral_const_mul, hmono]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hcj : 0 ≤ (n.choose (j + 1) : ℝ) / (j.factorial : ℝ) := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcj,
    abs_of_pos (by positivity : (0 : ℝ) < R ^ (j + 1))]
  have hbj := hB j (ρ * (R : ℂ)) hτ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp] at hbj
  have hpow : ‖ρ‖ ^ 2 ≤ ‖ρ‖ ^ (j + 2) := pow_le_pow_right₀ hρ1 (by omega)
  calc (n.choose (j + 1) : ℝ) / (j.factorial : ℝ) * (R ^ (j + 1) * ‖∫ v : ℝ, edgeTail j v * cexp (ρ * (R : ℂ) * v)‖)
      ≤ (n.choose (j + 1) : ℝ) / (j.factorial : ℝ) * (R ^ (j + 1) * (B j / (‖ρ‖ * R) ^ (j + 2))) := by gcongr
    _ = (n.choose (j + 1) : ℝ) / (j.factorial : ℝ) * B j / (R * ‖ρ‖ ^ (j + 2)) := by
        have hRne : R ≠ 0 := hRp.ne'
        have hρne : ‖ρ‖ ≠ 0 := hρn.ne'
        field_simp
        ring
    _ ≤ (n.choose (j + 1) : ℝ) / (j.factorial : ℝ) * B j / ‖ρ‖ ^ 2 := by
        apply div_le_div_of_nonneg_left (by have := hB0 j; positivity) (pow_pos hρn 2)
        calc ‖ρ‖ ^ 2 ≤ 1 * ‖ρ‖ ^ (j + 2) := by rw [one_mul]; exact hpow
          _ ≤ R * ‖ρ‖ ^ (j + 2) := by gcongr

/-! ### (D3') assembled: the member's transform is the jump's plus the jump side plus the left edge -/

/-- The jump's indicator `1_{u < 0}`, real. -/
def jumpInd (u : ℝ) : ℝ := if u < 0 then 1 else 0

/-- **The cut splits:** for `0 < δ ≤ 1`, `symCut = 1_{u<0} + (w - 1_{u<0}) + (st(δ u + 2) - 1)` -- the left factor differs
from `1` only where the jump cut is `1`. -/
theorem symCut_split {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u : ℝ) :
    symCut δ u = jumpInd u + (wf δ u - jumpInd u) + (Real.smoothTransition (δ * u + 2) - 1) := by
  unfold symCut wf
  by_cases h : 1 ≤ δ * u + 2
  · rw [Real.smoothTransition.one_of_one_le h]
    ring
  · have hu : u ≤ -(δ / 2) := by nlinarith
    have h' : 1 ≤ 1 / 2 - u / δ := by
      have : u / δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; linarith
      linarith
    rw [Real.smoothTransition.one_of_one_le h']
    ring

/-- The parity of the jump cut: `w(-u) = 1 - w(u)`. -/
theorem wf_neg (δ u : ℝ) : wf δ (-u) = 1 - wf δ u := by
  unfold wf
  rw [← smoothTransition_one_sub]
  congr 1
  ring

theorem wf_eq_zero {δ u : ℝ} (hδ : 0 < δ) (hu : δ / 2 ≤ u) : wf δ u = 0 := by
  unfold wf
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, le_div_iff₀ hδ]
  linarith

theorem re_ofReal_mul_cexp (r : ℝ) (ρ : ℂ) (u : ℝ) :
    ((r : ℂ) * cexp (ρ * u)).re = r * (Real.exp (ρ.re * u) * Real.cos (ρ.im * u)) := by
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

/-- The left-edge integrand is integrable (the polynomial monomial by monomial). -/
theorem leftEdge_integrable (n : ℕ) {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    Integrable (fun u : ℝ => (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)) := by
  have hint : ∀ j : ℕ, Integrable (fun u : ℝ => (((Real.smoothTransition (δ * u + 2) - 1) * u ^ j : ℝ) : ℂ) * cexp (ρ * u)) :=
    fun j => integrable_cut_pow_cexp (h := fun u => Real.smoothTransition (δ * u + 2) - 1) (by fun_prop)
      (fun u => edgeCut_abs (δ * u))
      (fun u hu => by rw [Real.smoothTransition.one_of_one_le (by have := mul_nonneg hδ.le hu; linarith), sub_self]) j hρ
  have h := integrable_finset_sum (Finset.range n) (fun j _ => (hint j).const_mul (((n.choose (j + 1) : ℝ) / (j.factorial : ℝ) : ℝ) : ℂ))
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Finset.sum_apply]
  unfold blPoly
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **(D3'): `SymPairBound n` HOLDS** -- `|Re H_δ(ρ)| ≤ C / ‖ρ‖²` for every `δ ∈ (0, 1]` and every `ρ` with `1 ≤ |Im ρ|`,
`0 < Re ρ < 1`, `C` depending on `n` alone: the jump's own part by `liTerm_re_abs_le`, the jump side by `jump_cos_bound`
after the odd cut's symmetrisation, the left edge by `left_edge_bound`. -/
theorem symPair_bound (n : ℕ) : SymPairBound n := by
  obtain ⟨CJ, hCJ⟩ := jump_cos_bound n
  obtain ⟨CL, hCL⟩ := left_edge_bound n
  have hCJ0 : 0 ≤ CJ := by
    have h := hCJ 1 one_pos le_rfl 0 le_rfl zero_le_one 1 one_ne_zero
    rw [one_pow, div_one] at h
    exact (abs_nonneg _).trans h
  refine ⟨(n + n * 2 ^ n) + 2 * CJ + CL, fun δ hδ hδ1 ρ hγ hβ0 hβ1 => ?_⟩
  set β := ρ.re with hβ
  set γ := ρ.im with hγdef
  have hγ0 : γ ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hρ1 : 1 ≤ ‖ρ‖ := hγ.trans (Complex.abs_im_le_norm ρ)
  have hρn : 0 < ‖ρ‖ := by linarith
  -- the three integrands
  set e : ℝ → ℂ := fun u => cexp (ρ * u) with he
  have hH : Integrable (fun u : ℝ => ((symCut δ u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)) := by
    have hi : Integrable (fun u : ℝ => symMember n δ u * cexp (Complex.I * gammaOf ρ * u)) :=
      ((symMember_classEF n hδ).1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (symMember_classEF n hδ).2.mul_right
    exact hi.congr (Filter.Eventually.of_forall fun u => symMember_integrand_exp n δ ρ u)
  have hT1 : Integrable (fun u : ℝ => ((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)) := by
    refine (integrable_blTest_integrand n hβ0).congr (Filter.Eventually.of_forall fun u => ?_)
    show blTest n u * cexp (Complex.I * gammaOf ρ * u) = ((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
    rw [blTest_integrand]
    unfold jumpInd
    by_cases hu : u < 0
    · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), if_pos hu, one_mul]
    · rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu), if_neg hu, zero_mul, Complex.ofReal_zero, zero_mul]
  have hT3 := leftEdge_integrable n hδ hβ0
  have hsplit : ∀ u : ℝ, ((symCut δ u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
      = ((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) + (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
        + (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) := by
    intro u
    rw [symCut_split hδ hδ1 u]
    push_cast
    ring
  have hT2 : Integrable (fun u : ℝ => (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)) := by
    refine ((hH.sub hT1).sub hT3).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit u]
    ring
  -- the transform, split
  have hHeq : paperFT (symMember n δ) (gammaOf ρ)
      = liTerm n ρ + (∫ u : ℝ, (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u))
        + ∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) := by
    have hL : liTerm n ρ = ∫ u : ℝ, ((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) := by
      rw [← blTransform_holds n ρ hβ0]
      unfold paperFT
      congr 1
      funext u
      rw [blTest_integrand]
      unfold jumpInd
      by_cases hu : u < 0
      · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), if_pos hu, one_mul]
      · rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu), if_neg hu, zero_mul, Complex.ofReal_zero, zero_mul]
    have e1 : ∫ u : ℝ, (((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) + (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
        + (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u))
        = (∫ u : ℝ, (((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) + (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)))
          + ∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) :=
      integral_add (hT1.add hT2) hT3
    have e2 : ∫ u : ℝ, (((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) + (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u))
        = (∫ u : ℝ, ((jumpInd u * blPoly n u : ℝ) : ℂ) * cexp (ρ * u))
          + ∫ u : ℝ, (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u) :=
      integral_add hT1 hT2
    unfold paperFT
    simp_rw [symMember_integrand_exp, hsplit]
    rw [e1, e2, hL]
  -- the jump side's real part, symmetrised
  set a : ℝ := δ / 2 with ha
  set g : ℝ → ℝ := fun u => (wf δ u - jumpInd u) * blPoly n u * (Real.exp (β * u) * Real.cos (γ * u)) with hg
  set k0 : ℝ → ℝ := fun u => wf δ u * (qf n β u - qf n β (-u)) * Real.cos (γ * u) with hk0
  set F : ℝ → ℝ := (Ioc 0 a).indicator k0 with hF
  have hreJ : (∫ u : ℝ, (((wf δ u - jumpInd u) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)).re = ∫ u : ℝ, g u := by
    have h := integral_re hT2
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    congr 1
    funext u
    rw [re_ofReal_mul_cexp]
  have hgInt : Integrable g := by
    refine hT2.re.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg]
    exact re_ofReal_mul_cexp _ ρ u
  have hk0c : Continuous k0 := by
    have hst := Real.smoothTransition.continuous
    have hPc := (blPoly_contDiff_infty n).continuous
    simp only [hk0, wf, qf]
    fun_prop
  have hFInt : Integrable F := by
    rw [hF, integrable_indicator_iff measurableSet_Ioc]
    exact (hk0c.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpos : ∀ u : ℝ, 0 < u → g u + g (-u) = F u := by
    intro u hu
    have hi1 : jumpInd u = 0 := by unfold jumpInd; rw [if_neg (not_lt.mpr hu.le)]
    have hi2 : jumpInd (-u) = 1 := by unfold jumpInd; rw [if_pos (by linarith)]
    have hgs : g u + g (-u) = k0 u := by
      simp only [hg, hk0, qf]
      rw [hi1, hi2, wf_neg, show γ * -u = -(γ * u) by ring, Real.cos_neg]
      ring
    rw [hgs, hF]
    by_cases hua : u ≤ a
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 a from ⟨hu, hua⟩)]
    · rw [Set.indicator_of_notMem (fun h => hua h.2)]
      simp only [hk0]
      rw [wf_eq_zero hδ (by linarith [not_le.mp hua]), zero_mul, zero_mul]
  have hFneg : ∀ u : ℝ, 0 < u → F (-u) = 0 := fun u hu => by
    rw [hF, Set.indicator_of_notMem (fun h => by linarith [h.1])]
  have hsym : ∀ᵐ u : ℝ ∂volume, g u + g (-u) = F u + F (-u) := by
    have h0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with u hu0
    rcases lt_or_gt_of_ne hu0 with hu | hu
    · have h1 := hpos (-u) (by linarith)
      have h2 := hFneg (-u) (by linarith)
      rw [neg_neg] at h1 h2
      rw [h2, zero_add, ← h1, add_comm]
    · rw [hpos u hu, hFneg u hu, add_zero]
  have hgF : ∫ u : ℝ, g u = ∫ u in (0 : ℝ)..a, k0 u := by
    have h1 : ∫ u : ℝ, (g u + g (-u)) = ∫ u : ℝ, (F u + F (-u)) := integral_congr_ae hsym
    rw [integral_add hgInt hgInt.comp_neg, integral_add hFInt hFInt.comp_neg, integral_neg_eq_self g, integral_neg_eq_self F] at h1
    have h2 : ∫ u : ℝ, g u = ∫ u : ℝ, F u := by linarith
    rw [h2, hF, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le (by positivity)]
  -- the bound
  have hJ : |∫ u in (0 : ℝ)..a, k0 u| ≤ CJ / γ ^ 2 := hCJ δ hδ hδ1 β hβ0.le hβ1.le γ hγ0
  have hLi := liTerm_re_abs_le n hρ1 hβ0.le hβ1.le
  have hEL := hCL δ hδ hδ1 ρ hβ0 hρ1
  have hnorm : ‖ρ‖ ^ 2 ≤ 2 * γ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : 1 ≤ γ ^ 2 := by nlinarith [abs_nonneg γ, sq_abs γ]
    nlinarith [hβ0, hβ1]
  have hρ2 : 0 < ‖ρ‖ ^ 2 := by positivity
  have hJ2 : CJ / γ ^ 2 ≤ 2 * CJ / ‖ρ‖ ^ 2 := by
    have hγ2 : 0 < γ ^ 2 := by positivity
    rw [div_le_div_iff₀ hγ2 hρ2]
    nlinarith
  rw [hHeq, Complex.add_re, Complex.add_re, hreJ, hgF]
  have hre := Complex.abs_re_le_norm (∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u))
  calc |(liTerm n ρ).re + (∫ u in (0 : ℝ)..a, k0 u)
        + (∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)).re|
      ≤ |(liTerm n ρ).re| + |∫ u in (0 : ℝ)..a, k0 u|
        + |(∫ u : ℝ, (((Real.smoothTransition (δ * u + 2) - 1) * blPoly n u : ℝ) : ℂ) * cexp (ρ * u)).re| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (n + n * 2 ^ n) / ‖ρ‖ ^ 2 + 2 * CJ / ‖ρ‖ ^ 2 + CL / ‖ρ‖ ^ 2 := by
        gcongr
        · exact hJ.trans hJ2
        · exact hre.trans hEL
    _ = _ := by ring

/-! ## (e) (D4') -- dominated convergence over the configuration; the discharge; the identity in limit form -/

/-- At a fixed zero the member transforms are bounded uniformly in `δ ∈ (0, 1]` (the dominant of (D2')). -/
theorem symMember_transform_norm_le (n : ℕ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    ∃ B : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖paperFT (symMember n δ) (gammaOf ρ)‖ ≤ B := by
  have hint : Integrable (fun u : ℝ => blTest n u * cexp (Complex.I * gammaOf ρ * u)) := integrable_blTest_integrand n hρ
  have hcont : Continuous (fun u : ℝ => blSmooth n u * cexp (Complex.I * gammaOf ρ * u)) :=
    (blSmooth_contDiff n).continuous.mul (by fun_prop)
  have hbi : Integrable (fun u : ℝ => ‖blTest n u * cexp (Complex.I * gammaOf ρ * u)‖
      + (Icc (0 : ℝ) 1).indicator (fun u => ‖blSmooth n u * cexp (Complex.I * gammaOf ρ * u)‖) u) := by
    refine hint.norm.add ?_
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hcont.norm.integrableOn_Icc
  refine ⟨∫ u : ℝ, (‖blTest n u * cexp (Complex.I * gammaOf ρ * u)‖
      + (Icc (0 : ℝ) 1).indicator (fun u => ‖blSmooth n u * cexp (Complex.I * gammaOf ρ * u)‖) u), fun δ hδ hδ1 => ?_⟩
  unfold paperFT
  refine norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall fun u => ?_)
  rw [symMember_integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (symCut_nonneg δ u)]
  have hb0 : 0 ≤ ‖blTest n u * cexp (Complex.I * gammaOf ρ * u)‖ := norm_nonneg _
  have hi0 : 0 ≤ (Icc (0 : ℝ) 1).indicator (fun u => ‖blSmooth n u * cexp (Complex.I * gammaOf ρ * u)‖) u :=
    Set.indicator_nonneg (fun _ _ => norm_nonneg _) u
  have hh0 := norm_nonneg (blSmooth n u * cexp (Complex.I * gammaOf ρ * u))
  have hc1 := symCut_le_one δ u
  have hc0 := symCut_nonneg δ u
  by_cases hu : u < 0
  · rw [blTest_integrand_neg n ρ hu]
    nlinarith
  · by_cases hu1 : u ≤ 1
    · rw [Set.indicator_of_mem (show u ∈ Icc (0 : ℝ) 1 from ⟨not_lt.mp hu, hu1⟩)]
      nlinarith
    · have h1u := not_le.mp hu1
      rw [symCut_eq_zero_right hδ (by linarith), zero_mul]
      linarith

/-- **(D4'): dominated convergence over the configuration** -- given (D3')'s bound, the zero side of EF_lit at the symmetric
members tends to `LiCoeff n` (Tannery over the zeros, the dominant `C m_ρ / ‖ρ‖²` summable by `zero_sum_inv_sq` as
`pair_summable` uses it, the finitely many zeros with `|Im ρ| ≤ 1` dominated one by one; the zero sum is real, so its real
part carries it). -/
theorem exchange_of_bound (n : ℕ) (hB : SymPairBound n) : LiLimitExchangeSym n := by
  obtain ⟨C, hC⟩ := hB
  have hre : ∀ ρ : zetaZeroConfig.carrier, 0 < (ρ : ℂ).re := fun ρ => (ρ.2 : IsNontrivialZero (ρ : ℂ)).2.1
  have hre1 : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re < 1 := fun ρ => (ρ.2 : IsNontrivialZero (ρ : ℂ)).2.2
  choose Bz hBz using fun ρ : zetaZeroConfig.carrier => symMember_transform_norm_le n (hre ρ)
  have hfin : (zetaZeroConfig.window (-1) 1).Finite := zetaZeroConfig.finite_window _ _
  have hSfin : ((fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) ⁻¹' (zetaZeroConfig.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  have hg : Summable (fun ρ : zetaZeroConfig.carrier =>
      (9 / 4 * |C|) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    (WeilEF.zero_sum_inv_sq zetaSeam).mul_left _
  have hE : Summable (fun ρ : zetaZeroConfig.carrier =>
      if ρ ∈ hSfin.toFinset then (zetaZeroConfig.mult ρ : ℝ) * Bz ρ else 0) :=
    summable_of_ne_finset_zero (s := hSfin.toFinset) (fun ρ hρ => by simp only [if_neg hρ])
  have hpt : ∀ ρ : zetaZeroConfig.carrier, Tendsto (fun δ => (zetaZeroConfig.mult ρ : ℝ) * (paperFT (symMember n δ) (gammaOf ρ)).re)
      (𝓝[>] 0) (𝓝 ((zetaZeroConfig.mult ρ : ℝ) * (liTerm n ρ).re)) :=
    fun ρ => ((Complex.continuous_re.tendsto _).comp (symMember_transform_tendsto n (hre ρ))).const_mul _
  have hdom : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ ρ : zetaZeroConfig.carrier,
      ‖(zetaZeroConfig.mult ρ : ℝ) * (paperFT (symMember n δ) (gammaOf ρ)).re‖
        ≤ (9 / 4 * |C|) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))
          + (if ρ ∈ hSfin.toFinset then (zetaZeroConfig.mult ρ : ℝ) * Bz ρ else 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    intro ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hA : 0 ≤ (9 / 4 * |C|) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
      mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
    by_cases hw : ρ ∈ hSfin.toFinset
    · rw [if_pos hw]
      have hr : |(paperFT (symMember n δ) (gammaOf ρ)).re| ≤ Bz ρ :=
        (Complex.abs_re_le_norm _).trans (hBz ρ δ hδ.1 hδ.2.le)
      nlinarith [mul_le_mul_of_nonneg_left hr hm]
    · rw [if_neg hw, add_zero]
      have hρmem : (ρ : ℂ) ∈ zetaZeroConfig.carrier := ρ.2
      have hnw : (ρ : ℂ) ∉ zetaZeroConfig.window (-1) 1 := fun h => hw ((Set.Finite.mem_toFinset hSfin).mpr h)
      have him : 1 ≤ |(ρ : ℂ).im| := by
        simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le] at hnw
        by_contra h
        rw [not_le, abs_lt] at h
        exact absurd (hnw hρmem h.1) (not_lt.mpr h.2.le)
      have hb := hC δ hδ.1 hδ.2.le ρ him (hre ρ) (hre1 ρ)
      have hstrip := zetaZeroConfig.strip _ hρmem
      have hnorm1 : 1 ≤ ‖(ρ : ℂ)‖ := him.trans (Complex.abs_im_le_norm _)
      have him2 : 1 ≤ (ρ : ℂ).im ^ 2 := by
        have := one_le_pow₀ (n := 2) him
        rwa [sq_abs] at this
      have hρsq : (ρ : ℂ).im ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (ρ : ℂ)) 2
        rwa [sq_abs] at this
      have hγ : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
        rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
        nlinarith [hstrip.1, hstrip.2]
      have hq0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        have := Complex.normSq_nonneg (gammaOf (ρ : ℂ))
        linarith
      have hn2 : 0 < ‖(ρ : ℂ)‖ ^ 2 := by positivity
      have key : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ (9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
        rw [div_le_div_iff₀ hn2 hq0]
        linarith
      have hC' : C / ‖(ρ : ℂ)‖ ^ 2 ≤ |C| * ((9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        calc C / ‖(ρ : ℂ)‖ ^ 2 ≤ |C| / ‖(ρ : ℂ)‖ ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) hn2.le
          _ = |C| * (1 / ‖(ρ : ℂ)‖ ^ 2) := by ring
          _ ≤ |C| * ((9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := mul_le_mul_of_nonneg_left key (abs_nonneg C)
      have hmult : (zetaZeroConfig.mult ρ : ℝ) = (zeroMult (ρ : ℂ) : ℝ) := by rw [zetaZeroConfig_mult]
      calc (zetaZeroConfig.mult ρ : ℝ) * |(paperFT (symMember n δ) (gammaOf ρ)).re|
          ≤ (zetaZeroConfig.mult ρ : ℝ) * (|C| * ((9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
            mul_le_mul_of_nonneg_left (hb.trans hC') hm
        _ = (9 / 4 * |C|) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by rw [hmult]; ring
  have hT := tendsto_tsum_of_dominated_convergence (hg.add hE) hpt hdom
  rw [← LiCoeff_eq] at hT
  unfold LiLimitExchangeSym
  refine ((Complex.continuous_ofReal.tendsto _).comp hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  apply Complex.ext
  · simp only [Function.comp_apply, Complex.ofReal_re]
    rw [Complex.re_tsum (symMember_EF n hδ).1]
    congr 1
    funext ρ
    simp [Complex.mul_re]
  · simp only [Function.comp_apply, Complex.ofReal_im]
    rw [symZeroSum_im]

/-- **THE DISCHARGE: `LiLimitExchangeSym n` HOLDS** for every `n` -- (D3') and (D4'). -/
theorem liLimitExchangeSym_holds (n : ℕ) : LiLimitExchangeSym n := exchange_of_bound n (symPair_bound n)

/-- **`li_identity_sym` -- the Bombieri-Lagarias arithmetic formula in limit form:** `LiCoeff n` is the `δ → 0⁺` limit of the
literature right-hand side of EF_lit (the pole terms, the prime sum and the Γ-integral) at the symmetric members. -/
theorem li_identity_sym (n : ℕ) :
    Tendsto (fun δ => EF.literatureRHS (symMember n δ)) (𝓝[>] 0) (𝓝 (LiCoeff n : ℂ)) := by
  refine (liLimitExchangeSym_holds n).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (symMember_EF n hδ).2

end LiWeil
end SIDEExplicitFormula
