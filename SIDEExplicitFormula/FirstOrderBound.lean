/-
SIDE-explicit-formula -- SIDEExplicitFormula/FirstOrderBound.lean
THIS PROGRAMME'S WORK (act b665, ruling (R275)(3); W-ORD-FT-FIRST-ORDER, b663's B1) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FIRST-ORDER TRANSFORM BOUND FOR THE KERNEL'S PLATEAU (relay data/b665_keiper_statement.txt, section (II)), at every ramp
fraction `F` and half-width `L` (the detector's base `detectorBase ρ = plateau (1/2) (baseWidth ρ)` among them):

* `plateau_deriv_abs_integral` -- `∫ |plateau'| = 2`: the plateau rises from 0 to 1 and falls back.
* `paperFT_plateau_first_order` -- `‖paperFT (phiC plateau) z‖ ‖z‖ ≤ 2 e^{L |Im z|}`, from `paperFT_decay` at `p = 1`
  (DecayBound.lean) and the integral above.
* `offScore_plateau_first_order` -- at a point `ρ` with `0 ≤ Re ρ ≤ 1`: `offScore plateau ρ · |Im ρ| ≤ 2 e^{L/2}`, the bound
  relay data/b663_epstein_plan.txt :155-:163 names B1.

The hypotheses are the plateau's parameter ranges and, for the last, the strip. Nothing here is a statement about the zeros of
ζ or about RH.
-/
import SIDEExplicitFormula.PowerWindow

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **The plateau's total variation**: `∫ |deriv (plateau F L)| = 2`. -/
theorem plateau_deriv_abs_integral (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) :
    ∫ u, |deriv (plateau F L hF0 hF1 hL) u| = 2 := by
  have hFL : 0 < F * L := mul_pos hF0 hL
  have hFL' : F * L ≤ L := by
    first
    | nlinarith
    | sorry
  -- on `u ≥ 0` the plateau is its falling transition, on `u ≤ 0` its rising one
  have hright : ∀ u : ℝ, 0 ≤ u → plateau F L hF0 hF1 hL u = Real.smoothTransition ((L - u) / (F * L)) := by
    intro u hu
    first
    | have h1 : 1 ≤ (L + u) / (F * L) := by
        rw [le_div_iff₀ hFL]
        linarith
      show Real.smoothTransition ((L - u) / (F * L)) * Real.smoothTransition ((L + u) / (F * L)) = _
      rw [Real.smoothTransition.one_of_one_le h1, mul_one]
    | sorry
  have hleft : ∀ u : ℝ, u ≤ 0 → plateau F L hF0 hF1 hL u = Real.smoothTransition ((L + u) / (F * L)) := by
    intro u hu
    first
    | have h1 : 1 ≤ (L - u) / (F * L) := by
        rw [le_div_iff₀ hFL]
        linarith
      show Real.smoothTransition ((L - u) / (F * L)) * Real.smoothTransition ((L + u) / (F * L)) = _
      rw [Real.smoothTransition.one_of_one_le h1, one_mul]
    | sorry
  have hanti : Antitone (fun u : ℝ => Real.smoothTransition ((L - u) / (F * L))) := by
    first
    | intro a b hab
      show Real.smoothTransition ((L - b) / (F * L)) ≤ Real.smoothTransition ((L - a) / (F * L))
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hFL.le)
    | sorry
  have hmono : Monotone (fun u : ℝ => Real.smoothTransition ((L + u) / (F * L))) := by
    first
    | intro a b hab
      show Real.smoothTransition ((L + a) / (F * L)) ≤ Real.smoothTransition ((L + b) / (F * L))
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hFL.le)
    | sorry
  -- regularity, from the kernel's `plateau_contDiff`
  have h1 : ContDiff ℝ 1 (plateau F L hF0 hF1 hL) := by
    have := plateau_contDiff F L hF0 hF1 hL 1
    exact_mod_cast this
  have hdiff : Differentiable ℝ (plateau F L hF0 hF1 hL) := by
    first
    | exact h1.differentiable one_ne_zero
    | sorry
  have hcd : Continuous (deriv (plateau F L hF0 hF1 hL)) := by
    first
    | exact h1.continuous_deriv_one
    | sorry
  -- the values at 0 and at ±L
  have hval0 : plateau F L hF0 hF1 hL 0 = 1 := by
    first
    | exact plateau_eq_one F L hF0 hF1 hL 0 (by rw [abs_zero]; exact mul_nonneg (by linarith) hL.le)
    | sorry
  have hvalL : plateau F L hF0 hF1 hL L = 0 := by
    first
    | rw [hright L hL.le, sub_self, zero_div, Real.smoothTransition.zero]
    | sorry
  have hvalmL : plateau F L hF0 hF1 hL (-L) = 0 := by
    first
    | rw [hleft (-L) (by linarith), show L + -L = 0 by ring, zero_div, Real.smoothTransition.zero]
    | sorry
  -- the derivative's sign on each side; at 0 the plateau is at its maximum
  have hd0 : deriv (plateau F L hF0 hF1 hL) 0 = 0 := by
    first
    | apply IsLocalMax.deriv_eq_zero
      refine Filter.Eventually.of_forall fun y => ?_
      show plateau F L hF0 hF1 hL y ≤ plateau F L hF0 hF1 hL 0
      rw [hval0]
      show Real.smoothTransition ((L - y) / (F * L)) * Real.smoothTransition ((L + y) / (F * L)) ≤ 1
      nlinarith [Real.smoothTransition.nonneg ((L - y) / (F * L)), Real.smoothTransition.le_one ((L - y) / (F * L)),
        Real.smoothTransition.nonneg ((L + y) / (F * L)), Real.smoothTransition.le_one ((L + y) / (F * L))]
    | sorry
  have hdr : ∀ u : ℝ, 0 ≤ u → deriv (plateau F L hF0 hF1 hL) u ≤ 0 := by
    intro u hu
    first
    | rcases hu.lt_or_eq with hpos | hzero
      · have heq : (plateau F L hF0 hF1 hL) =ᶠ[nhds u] (fun v : ℝ => Real.smoothTransition ((L - v) / (F * L))) := by
          filter_upwards [lt_mem_nhds hpos] with v hv
          exact hright v hv.le
        rw [heq.deriv_eq]
        exact hanti.deriv_nonpos
      · rw [← hzero]
        exact hd0.le
    | sorry
  have hdl : ∀ u : ℝ, u ≤ 0 → 0 ≤ deriv (plateau F L hF0 hF1 hL) u := by
    intro u hu
    first
    | rcases hu.lt_or_eq with hneg | hzero
      · have heq : (plateau F L hF0 hF1 hL) =ᶠ[nhds u] (fun v : ℝ => Real.smoothTransition ((L + v) / (F * L))) := by
          filter_upwards [gt_mem_nhds hneg] with v hv
          exact hleft v hv.le
        rw [heq.deriv_eq]
        exact hmono.deriv_nonneg
      · rw [hzero]
        exact hd0.ge
    | sorry
  -- the integral is over the derivative's support, split at 0
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (-L) L → |deriv (plateau F L hF0 hF1 hL) u| = 0 := by
    intro u hu
    first
    | have h0 : deriv (plateau F L hF0 hF1 hL) u = 0 := by
        by_contra h
        exact hu (support_deriv_Icc (plateau_support_Icc F L hF0 hF1 hL) h)
      rw [h0, abs_zero]
    | sorry
  have hci : Continuous (fun u : ℝ => |deriv (plateau F L hF0 hF1 hL) u|) := hcd.abs
  have hLL : -L ≤ L := by linarith
  have hwhole : ∫ u, |deriv (plateau F L hF0 hF1 hL) u| =
      (∫ u in (-L)..0, |deriv (plateau F L hF0 hF1 hL) u|) + ∫ u in (0 : ℝ)..L, |deriv (plateau F L hF0 hF1 hL) u| := by
    first
    | rw [← (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp), integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hLL,
        intervalIntegral.integral_add_adjacent_intervals (hci.intervalIntegrable (μ := volume) (-L) 0)
          (hci.intervalIntegrable (μ := volume) 0 L)]
    | sorry
  have hrightI : ∫ u in (0 : ℝ)..L, |deriv (plateau F L hF0 hF1 hL) u| = 1 := by
    first
    | have hc : ∫ u in (0 : ℝ)..L, |deriv (plateau F L hF0 hF1 hL) u| =
          ∫ u in (0 : ℝ)..L, -deriv (plateau F L hF0 hF1 hL) u := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hL.le] at hx
        exact abs_of_nonpos (hdr x hx.1)
      rw [hc, intervalIntegral.integral_neg,
        intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x) (hcd.intervalIntegrable (μ := volume) 0 L), hvalL, hval0]
      norm_num
    | sorry
  have hleftI : ∫ u in (-L)..0, |deriv (plateau F L hF0 hF1 hL) u| = 1 := by
    first
    | have hc : ∫ u in (-L)..0, |deriv (plateau F L hF0 hF1 hL) u| =
          ∫ u in (-L)..0, deriv (plateau F L hF0 hF1 hL) u := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith : -L ≤ 0)] at hx
        exact abs_of_nonneg (hdl x hx.2)
      rw [hc, intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x) (hcd.intervalIntegrable (μ := volume) (-L) 0), hval0,
        hvalmL]
      norm_num
    | sorry
  first
  | rw [hwhole, hleftI, hrightI]
    norm_num
  | sorry

/-- **The first-order bound**: `‖paperFT (phiC (plateau F L)) z‖ · ‖z‖ ≤ 2 e^{L |Im z|}`. -/
theorem paperFT_plateau_first_order (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (z : ℂ) :
    ‖Zeta23.paperFT (phiC (plateau F L hF0 hF1 hL)) z‖ * ‖z‖ ≤ 2 * Real.exp (L * |z.im|) := by
  have h1 : ContDiff ℝ (1 : ℕ) (plateau F L hF0 hF1 hL) := by
    have := plateau_contDiff F L hF0 hF1 hL 1
    exact_mod_cast this
  first
  | have h := paperFT_decay 1 h1 (plateau_support_Icc F L hF0 hF1 hL) z
    rw [pow_one, iteratedDeriv_one, plateau_deriv_abs_integral F L hF0 hF1 hL] at h
    exact h
  | sorry

/-- **B1 at a strip point**: for `0 ≤ Re ρ ≤ 1`, `offScore (plateau F L) ρ · |Im ρ| ≤ 2 e^{L/2}`. -/
theorem offScore_plateau_first_order (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (ρ : ℂ) (h0 : 0 ≤ ρ.re)
    (h1 : ρ.re ≤ 1) : offScore (plateau F L hF0 hF1 hL) ρ * |ρ.im| ≤ 2 * Real.exp (L / 2) := by
  first
  | have him : |(Zeta23.gammaOf ρ).im| ≤ 1 / 2 := by
      rw [gammaOf_im', abs_neg]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hexp : Real.exp (L * |(Zeta23.gammaOf ρ).im|) ≤ Real.exp (L / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (Zeta23.gammaOf ρ).im])
    have htx : |ρ.im| ≤ ‖Zeta23.gammaOf ρ‖ := by
      rw [← gammaOf_re' ρ]
      exact Complex.abs_re_le_norm _
    have hb := paperFT_plateau_first_order F L hF0 hF1 hL (Zeta23.gammaOf ρ)
    have hs0 : 0 ≤ offScore (plateau F L hF0 hF1 hL) ρ := norm_nonneg _
    unfold offScore at hs0 ⊢
    calc ‖Zeta23.paperFT (phiC (plateau F L hF0 hF1 hL)) (Zeta23.gammaOf ρ)‖ * |ρ.im|
        ≤ ‖Zeta23.paperFT (phiC (plateau F L hF0 hF1 hL)) (Zeta23.gammaOf ρ)‖ * ‖Zeta23.gammaOf ρ‖ :=
          mul_le_mul_of_nonneg_left htx hs0
      _ ≤ 2 * Real.exp (L * |(Zeta23.gammaOf ρ).im|) := hb
      _ ≤ 2 * Real.exp (L / 2) := by linarith
  | sorry

end B321
end SIDEExplicitFormula
