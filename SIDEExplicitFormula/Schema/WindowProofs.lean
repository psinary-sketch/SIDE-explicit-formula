/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/WindowProofs.lean
THIS PROGRAMME'S WORK (act b642, ruling (R252)(3)(b); W-ORD-DETECTION-REGION's (E3), the window's two obligations) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE WINDOW'S TWO OBLIGATIONS (`PlateauRamp.WindowObligations`), PROVED, AT EVERY `W` AND `h`:

* (O1) `convStep_holds W h : ConvStep W h`, at every `p` and every complex `z`, through Mathlib's convolution theorem for integrable
  functions (`Real.fourier_mul_convolution_eq`, Mathlib/Analysis/Fourier/Convolution.lean :119 at de5ce8a9): `paperFT` at `z` is the
  Fourier transform at the real frequency `-(Re z)/(2π)` of the function weighted by `e^(-(Im z) u)` (`paperFT_eq_fourier`), and the
  weight passes through a convolution (`conv_weighted`); the windows and the normalised box are integrable and compactly supported, so
  their weighted forms are integrable (`integrable_weighted`).
* (O2) `smooth4_holds W h : Smooth4 W h`, by the fundamental theorem of calculus: convolution with the normalised box is an interval
  average (`conv_nbox_eq`), which raises the order of smoothness by one (`contDiff_intAvg`), so the window is continuous at `p = 1` and
  `C^(p-1)` from there (`window_contDiff`); for `h ≤ 0` the normalised box is zero and the window is zero past `p = 0`.

Hence `plateauRampWindow_of` holds unconditionally (`windowObligations_holds`). Nothing here is a statement about the zeros of ζ, of any
L-function or of any Epstein zeta function.
-/
import SIDEExplicitFormula.Schema.PlateauRamp
import Mathlib.Analysis.Fourier.Convolution

open MeasureTheory FourierTransform

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace PlateauRamp

open B321

/-! ## Integrability -/

theorem box_integrable (a : ℝ) : Integrable (box a) := by
  unfold box
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))

theorem nbox_integrable (h : ℝ) : Integrable (nbox h) := (box_integrable (h / 2)).const_mul h⁻¹

theorem window_integrable (W h : ℝ) : ∀ p : ℕ, Integrable (window W h p)
  | 0 => box_integrable W
  | p + 1 => (window_integrable W h p).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (nbox_integrable h)

/-! ## (O2) The smoothness -/

/-- For `h ≤ 0` the normalised box is zero. -/
theorem nbox_of_nonpos {h : ℝ} (hh : h ≤ 0) : nbox h = 0 := by
  funext x
  unfold nbox box
  rcases hh.lt_or_eq with hlt | heq
  · have : x ∉ Set.Icc (-(h / 2)) (h / 2) := fun hx => by linarith [hx.1, hx.2]
    simp [Set.indicator_of_notMem this]
  · simp [heq]

/-- **Convolution with the normalised box is an interval average**: `conv f (nbox h) x = h⁻¹ ∫_{x-h/2}^{x+h/2} f`. -/
theorem conv_nbox_eq (f : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    conv f (nbox h) x = h⁻¹ * ∫ s in (x - h / 2)..(x + h / 2), f s := by
  simp only [conv, convolution_lsmul, smul_eq_mul]
  have e : (fun t => f t * nbox h (x - t)) = fun t => h⁻¹ * Set.indicator (Set.Icc (x - h / 2) (x + h / 2)) f t := by
    funext t
    unfold nbox box
    by_cases ht : t ∈ Set.Icc (x - h / 2) (x + h / 2)
    · have : x - t ∈ Set.Icc (-(h / 2)) (h / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [Set.indicator_of_mem this, Set.indicator_of_mem ht]; ring
    · have : x - t ∉ Set.Icc (-(h / 2)) (h / 2) := fun hm => ht ⟨by linarith [hm.2], by linarith [hm.1]⟩
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem ht]; ring
  rw [e, integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

/-- The interval average of an integrable function is continuous. -/
theorem continuous_intAvg {f : ℝ → ℝ} (hf : Integrable f) (c : ℝ) :
    Continuous fun x => ∫ s in (x - c)..(x + c), f s := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable
  have hG : Continuous fun y => ∫ s in (0 : ℝ)..y, f s := intervalIntegral.continuous_primitive hii 0
  have e : (fun x => ∫ s in (x - c)..(x + c), f s) = fun x => (∫ s in (0 : ℝ)..(x + c), f s) - ∫ s in (0 : ℝ)..(x - c), f s := by
    funext x
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [e]
  exact (hG.comp (continuous_id.add continuous_const)).sub (hG.comp (continuous_id.sub continuous_const))

/-- The primitive of a `C^n` function is `C^(n+1)`. -/
theorem contDiff_primitive {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ (n + 1 : ℕ) fun y => ∫ s in (0 : ℝ)..y, f s := by
  have hc : Continuous f := hf.continuous
  have hd : ∀ y, HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, f s) (f y) y := fun y =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hderiv : deriv (fun y => ∫ s in (0 : ℝ)..y, f s) = f := funext fun y => (hd y).deriv
  rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_deriv]
  refine ⟨fun y => (hd y).differentiableAt, by simp, ?_⟩
  rw [hderiv]; exact hf

/-- The interval average of a `C^n` function is `C^(n+1)`. -/
theorem contDiff_intAvg {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c : ℝ) :
    ContDiff ℝ (n + 1 : ℕ) fun x => ∫ s in (x - c)..(x + c), f s := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.continuous.intervalIntegrable a b
  have e : (fun x => ∫ s in (x - c)..(x + c), f s) = fun x => (∫ s in (0 : ℝ)..(x + c), f s) - ∫ s in (0 : ℝ)..(x - c), f s := by
    funext x
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [e]
  have hG := contDiff_primitive hf
  exact (hG.comp (contDiff_id.add contDiff_const)).sub (hG.comp (contDiff_id.sub contDiff_const))

/-- **The window is `C^(p-1)` from `p = 1`** (`h > 0`): each convolution with the normalised box raises the order by one. -/
theorem window_contDiff (W : ℝ) {h : ℝ} (hh : 0 < h) : ∀ p : ℕ, ContDiff ℝ (p : ℕ) (window W h (p + 1))
  | 0 => by
    have e : window W h (0 + 1) = fun x => h⁻¹ * ∫ s in (x - h / 2)..(x + h / 2), window W h 0 s := by
      funext x; exact conv_nbox_eq _ hh x
    rw [e, show ((0 : ℕ) : WithTop ℕ∞) = 0 by rfl, contDiff_zero]
    exact continuous_const.mul (continuous_intAvg (window_integrable W h 0) _)
  | p + 1 => by
    have e : window W h (p + 1 + 1) = fun x => h⁻¹ * ∫ s in (x - h / 2)..(x + h / 2), window W h (p + 1) s := by
      funext x; exact conv_nbox_eq _ hh x
    rw [e]
    exact contDiff_const.mul (contDiff_intAvg (window_contDiff W hh p) _)

/-- **(O2), THE SMOOTHNESS: for `p ≥ 6` the window is `C^4`**, at every `W` and `h`. -/
theorem smooth4_holds (W h : ℝ) : Smooth4 W h := by
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rcases le_or_gt h 0 with hh | hh
  · have e : window W h (q + 1) = fun _ => 0 := by
      funext x
      show conv (window W h q) (nbox h) x = 0
      rw [nbox_of_nonpos hh]
      simp [conv, convolution_lsmul]
    rw [e]; exact contDiff_const
  · exact (window_contDiff W hh q).of_le (by exact_mod_cast (show 4 ≤ q by omega))

/-! ## (O1) The convolution step -/

/-- The exponential weight `u ↦ e^(-b u)`. -/
def expWt (b : ℝ) (u : ℝ) : ℂ := Complex.exp (-(b : ℂ) * (u : ℂ))

theorem continuous_expWt (b : ℝ) : Continuous (expWt b) := by
  unfold expWt; fun_prop

theorem expWt_add (b t s : ℝ) : expWt b (t + s) = expWt b t * expWt b s := by
  unfold expWt; rw [← Complex.exp_add]; push_cast; ring_nf

/-- A compactly supported integrable real function, weighted by a continuous function, is integrable. -/
theorem integrable_weighted {f : ℝ → ℝ} (hf : Integrable f) (hc : HasCompactSupport f) {e : ℝ → ℂ} (he : Continuous e) :
    Integrable fun u => (f u : ℂ) * e u := by
  have hK : IsCompact (tsupport f) := hc
  have h1 : IntegrableOn (fun u => (f u : ℂ)) (tsupport f) := hf.ofReal.integrableOn
  have h2 := h1.mul_continuousOn he.continuousOn hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h2
  intro u hu
  apply subset_tsupport
  intro h0
  apply hu
  simp [h0]

/-- `paperFT` at complex `z` is Mathlib's Fourier transform of the function weighted by `e^(-(Im z) u)`, at the real frequency
`-(Re z)/(2π)`. -/
theorem paperFT_eq_fourier (F : ℝ → ℝ) (z : ℂ) :
    Zeta23.paperFT (phiC F) z = 𝓕 (fun u => (F u : ℂ) * expWt z.im u) (-z.re / (2 * Real.pi)) := by
  rw [Real.fourier_eq]
  unfold Zeta23.paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [phiC, expWt, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.I * z * (u : ℂ) = ((2 * Real.pi * -(u * (-z.re / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I + -(z.im : ℂ) * (u : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im z]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [RCLike.inner_apply, conj_trivial]
  rw [e, Complex.exp_add]
  ring_nf

/-- The weighted convolution is the convolution of the weighted functions. -/
theorem conv_weighted (f g : ℝ → ℝ) (b : ℝ) (u : ℝ) :
    (conv f g u : ℂ) * expWt b u =
      convolution (fun t => (f t : ℂ) * expWt b t) (fun t => (g t : ℂ) * expWt b t) (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  simp only [conv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have : expWt b u = expWt b t * expWt b (u - t) := by rw [← expWt_add]; ring_nf
  rw [this]
  push_cast
  ring

/-- **(O1), THE CONVOLUTION STEP, at every `p` and every complex `z`**, through Mathlib's convolution theorem for integrable functions
(`Real.fourier_mul_convolution_eq`, Mathlib/Analysis/Fourier/Convolution.lean :119 at de5ce8a9) with the weight `e^(-(Im z) u)`
carrying the real frequency to `z`. -/
theorem convStep_holds (W h : ℝ) : ConvStep W h := by
  intro p z
  have hf := integrable_weighted (window_integrable W h p) (window_hasCompactSupport W h p) (continuous_expWt z.im)
  have hg := integrable_weighted (nbox_integrable h) (nbox_hasCompactSupport h) (continuous_expWt z.im)
  have e : (fun u => (window W h (p + 1) u : ℂ) * expWt z.im u) =
      convolution (fun u => (window W h p u : ℂ) * expWt z.im u) (fun u => (nbox h u : ℂ) * expWt z.im u)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext fun u => conv_weighted (window W h p) (nbox h) z.im u
  rw [paperFT_eq_fourier, paperFT_eq_fourier, paperFT_eq_fourier, ← Real.fourier_mul_convolution_eq hf hg, e]

/-- **THE WINDOW'S OBLIGATIONS HOLD**, at every `W` and `h`. -/
theorem windowObligations_holds (W h : ℝ) : WindowObligations W h :=
  ⟨convStep_holds W h, smooth4_holds W h⟩

/-- **The compiled window of the bench's plateau family**, with no obligation left: (C1) and (C2) for `0 ≤ W` and `0 < h`. -/
theorem plateauRampWindow_holds {W h : ℝ} (hW : 0 ≤ W) (hh : 0 < h) : PlateauRampWindow W h :=
  plateauRampWindow_of hW hh (windowObligations_holds W h)

end PlateauRamp
end Schema
end SIDEExplicitFormula
