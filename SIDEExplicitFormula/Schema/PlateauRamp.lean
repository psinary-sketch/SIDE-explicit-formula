/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/PlateauRamp.lean
THIS PROGRAMME'S WORK (act b602, ruling (R212)(4); W-ORD-DETECTION-REGION's (E3), OPEN_TRAILS :12170) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(E3)'S COMPILED WINDOW OF THE BENCH'S PLATEAU FAMILY, BY b554'S CLOSED-FORM ROUTE (OPEN_TRAILS :11336, :11337), AS A PROP.
The bench's plateau window is a box convolved with a B-spline ramp (b519, b522 at p = 7); the kernel's detector (v0.16,
`Schema.detector`) uses a different base, `plateau`, whose ramp is Mathlib's `smoothTransition` (TwoPropertyWindow.lean),
raised to a power `2^j` -- a different window, as b546/b550 recorded. Here the bench's family is defined in the kernel:

* `box a` -- the indicator of `[-a, a]`; `nbox h` -- the box of width `h` normalised to integral 1 (the order-1 B-spline);
  `window W h p` -- `box W` convolved `p` times with `nbox h` (Mathlib's `convolution` with `lsmul`), the box of half-width
  `W` convolved with the order-`p` B-spline of half-width `p h / 2`.
* (C1) `ClosedFormFT W h` -- for every `p` and `z ≠ 0`, the transform (the kernel's `Zeta23.paperFT`) is
  `(2 sin(zW)/z) · (2 sin(z h/2)/(z h))^p`; (C2) `WindowInClassK W h` -- for `p ≥ 6` the window is `C^4`, even and compactly
  supported, and its self-convolution `weilTest` is in `classK`; `PlateauRampWindow W h` is the two together, the item.
* PROVED: the box's transform in closed form (`box_paperFT`, C1 at `p = 0`, `window_paperFT_zero`) and the normalised box's
  (`nbox_paperFT`); the window even (`window_even`) and compactly supported (`window_hasCompactSupport`) at every `p`.
* CARRIED TO TWO NAMED OBLIGATIONS (`WindowObligations`): (O1) `ConvStep`, the convolution theorem for the transform on the
  family (Mathlib at the pin holds it for Schwartz functions only, `fourier_convolution`, and the box is not one); (O2)
  `Smooth4`, the window `C^4` for `p ≥ 6` (convolution with a box raises the order by one; no Mathlib lemma at the pin).
  `plateauRampWindow_of` derives the item from them, at INTERFACES.
* ITS RELATION TO THE EPSTEIN PREMISES: INDEPENDENT. The window is a statement about test functions and names no zero
  configuration; `EpsteinPremises`' two fields (the explicit formula and the count for `Z_Q`) are facts about a
  configuration that no statement here concludes. The window is an input to the premises' explicit formula, not a discharge
  of it: `epstein_ef_at_window` evaluates `ef` at the window under the window's obligations.

Nothing here is a statement about the zeros of ζ, of any L-function or of any Epstein zeta function.
-/
import SIDEExplicitFormula.Schema.Epstein
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace PlateauRamp

open B321

/-- **The box of half-width `a`**: the indicator of `[-a, a]`. -/
def box (a : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (-a) a) (fun _ => 1)

/-- **The normalised box of width `h`** (integral 1): the order-1 B-spline. -/
def nbox (h : ℝ) : ℝ → ℝ := fun x => h⁻¹ * box (h / 2) x

/-- Convolution on `ℝ`: `conv f g x = ∫ t, f t * g (x - t)` (Mathlib's `convolution` with `lsmul`). -/
def conv (f g : ℝ → ℝ) : ℝ → ℝ := MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- **THE PLATEAU-RAMP WINDOW**: `box W` convolved `p` times with `nbox h` -- the box of half-width `W` convolved with the
order-`p` B-spline of half-width `p h / 2`. -/
def window (W h : ℝ) : ℕ → ℝ → ℝ
  | 0 => box W
  | p + 1 => conv (window W h p) (nbox h)

/-! ## Evenness and compact support -/

theorem box_even (a x : ℝ) : box a (-x) = box a x := by
  unfold box
  by_cases hx : x ∈ Set.Icc (-a) a
  · have h' : -x ∈ Set.Icc (-a) a := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.indicator_of_mem h', Set.indicator_of_mem hx]
  · have h' : -x ∉ Set.Icc (-a) a := fun hm => hx ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem hx]

theorem nbox_even (h x : ℝ) : nbox h (-x) = nbox h x := by
  unfold nbox
  rw [box_even]

theorem box_hasCompactSupport (a : ℝ) : HasCompactSupport (box a) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => Set.indicator_of_notMem hx _)

theorem nbox_hasCompactSupport (h : ℝ) : HasCompactSupport (nbox h) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(h / 2)) (b := h / 2)) (fun x hx => by
    show h⁻¹ * box (h / 2) x = 0
    rw [show box (h / 2) x = 0 from Set.indicator_of_notMem hx _, mul_zero])

/-- The convolution of two even functions is even. -/
theorem conv_even {f g : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = g x) (x : ℝ) :
    conv f g (-x) = conv f g x := by
  simp only [conv, MeasureTheory.convolution_lsmul, smul_eq_mul]
  rw [← integral_neg_eq_self]
  congr 1
  funext t
  show f (-t) * g (-x - -t) = f t * g (x - t)
  rw [hf, show -x - -t = -(x - t) by ring, hg]

/-- **The window is even**, at every `p`. -/
theorem window_even (W h : ℝ) : ∀ (p : ℕ) (x : ℝ), window W h p (-x) = window W h p x
  | 0, x => box_even W x
  | p + 1, x => conv_even (window_even W h p) (nbox_even h) x

/-- **The window is compactly supported**, at every `p`. -/
theorem window_hasCompactSupport (W h : ℝ) : ∀ p : ℕ, HasCompactSupport (window W h p)
  | 0 => box_hasCompactSupport W
  | p + 1 => HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (window_hasCompactSupport W h p) (nbox_hasCompactSupport h)

/-! ## The transform in closed form, at the box -/

/-- **The box's transform in closed form**: for `0 ≤ a` and `z ≠ 0`, `∫_{-a}^{a} e^{izu} du = 2 sin(za)/z`. -/
theorem box_paperFT {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (phiC (box a)) z = 2 * Complex.sin (z * (a : ℂ)) / z := by
  have hc : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have h1 : (fun u : ℝ => phiC (box a) u * Complex.exp (Complex.I * z * (u : ℂ))) =
      Set.indicator (Set.Icc (-a) a) (fun u : ℝ => Complex.exp (Complex.I * z * (u : ℂ))) := by
    funext u
    by_cases hu : u ∈ Set.Icc (-a) a
    · rw [Set.indicator_of_mem hu]
      simp only [phiC, box, Set.indicator_of_mem hu, Complex.ofReal_one, one_mul]
    · rw [Set.indicator_of_notMem hu]
      simp only [phiC, box, Set.indicator_of_notMem hu, Complex.ofReal_zero, zero_mul]
  unfold Zeta23.paperFT
  rw [h1, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_exp_mul_complex hc]
  have e1 : Complex.exp (z * (a : ℂ) * Complex.I) = Complex.exp (Complex.I * z * (a : ℂ)) := by
    congr 1
    ring
  have e2 : Complex.exp (-(z * (a : ℂ)) * Complex.I) = Complex.exp (Complex.I * z * ((-a : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [Complex.sin, e1, e2, div_eq_div_iff hc hz]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The normalised box's transform**: for `0 < h` and `z ≠ 0`, `2 sin(z h/2)/(z h)`. -/
theorem nbox_paperFT {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (phiC (nbox h)) z = 2 * Complex.sin (z * ((h / 2 : ℝ) : ℂ)) / (z * (h : ℂ)) := by
  have e : (fun u : ℝ => phiC (nbox h) u * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u => ((h : ℂ))⁻¹ * (phiC (box (h / 2)) u * Complex.exp (Complex.I * z * (u : ℂ))) := by
    funext u
    simp only [phiC, nbox]
    push_cast
    ring
  have hb := box_paperFT (a := h / 2) (by positivity) hz
  unfold Zeta23.paperFT at hb ⊢
  rw [e, MeasureTheory.integral_const_mul, hb]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  first
  | (field_simp; ring)
  | field_simp

/-! ## The item, as Props -/

/-- **(C1) THE TRANSFORM IN CLOSED FORM**: at every `p` and `z ≠ 0`, `(2 sin(zW)/z) · (2 sin(z h/2)/(z h))^p`. -/
def ClosedFormFT (W h : ℝ) : Prop :=
  ∀ (p : ℕ) (z : ℂ), z ≠ 0 → Zeta23.paperFT (phiC (window W h p)) z =
    (2 * Complex.sin (z * (W : ℂ)) / z) * (2 * Complex.sin (z * ((h / 2 : ℝ) : ℂ)) / (z * (h : ℂ))) ^ p

/-- **(C2) THE WINDOW IN classK**: for `p ≥ 6`, `C^4`, even, compactly supported, its self-convolution in `classK`. -/
def WindowInClassK (W h : ℝ) : Prop :=
  ∀ p : ℕ, 6 ≤ p → ContDiff ℝ 4 (window W h p) ∧ (∀ x, window W h p (-x) = window W h p x) ∧
    HasCompactSupport (window W h p) ∧ classK (Zeta23.EF.weilTest (phiC (window W h p)) (phiC (window W h p)))

/-- **(E3) THE COMPILED WINDOW OF THE BENCH'S PLATEAU FAMILY, AS A PROP**: (C1) and (C2). -/
def PlateauRampWindow (W h : ℝ) : Prop := ClosedFormFT W h ∧ WindowInClassK W h

/-- **C1 at `p = 0`, PROVED**: the window at `p = 0` is the box. -/
theorem window_paperFT_zero {W h : ℝ} (hW : 0 ≤ W) {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (phiC (window W h 0)) z =
      (2 * Complex.sin (z * (W : ℂ)) / z) * (2 * Complex.sin (z * ((h / 2 : ℝ) : ℂ)) / (z * (h : ℂ))) ^ 0 := by
  rw [pow_zero, mul_one]
  exact box_paperFT hW hz

/-! ## The obligations, named -/

/-- **(O1) THE CONVOLUTION STEP**: the transform of the next window is the transform of this one times the normalised box's. -/
def ConvStep (W h : ℝ) : Prop :=
  ∀ (p : ℕ) (z : ℂ), Zeta23.paperFT (phiC (window W h (p + 1))) z =
    Zeta23.paperFT (phiC (window W h p)) z * Zeta23.paperFT (phiC (nbox h)) z

/-- **(O2) THE SMOOTHNESS**: for `p ≥ 6` the window is `C^4`. -/
def Smooth4 (W h : ℝ) : Prop := ∀ p : ℕ, 6 ≤ p → ContDiff ℝ 4 (window W h p)

/-- **THE OBLIGATIONS WHERE THE PROOF STOPS, NAMED**. -/
structure WindowObligations (W h : ℝ) : Prop where
  conv_step : ConvStep W h
  smooth : Smooth4 W h

/-- **AT INTERFACES ON THE TWO OBLIGATIONS**: the compiled window of the bench's plateau family. -/
theorem plateauRampWindow_of {W h : ℝ} (hW : 0 ≤ W) (hh : 0 < h) (hP : WindowObligations W h) :
    PlateauRampWindow W h := by
  unfold PlateauRampWindow ClosedFormFT WindowInClassK
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · induction p with
    | zero => exact fun z hz => window_paperFT_zero hW hz
    | succ p ih =>
      intro z hz
      rw [hP.conv_step p z, ih z hz, nbox_paperFT hh hz, pow_succ]
      ring
  · have hs : ContDiff ℝ 4 (window W h p) := hP.smooth p hp
    have h2 : ContDiff ℝ 2 (window W h p) := hs.of_le (by
      first
      | norm_num
      | exact_mod_cast (show (2 : ℕ) ≤ 4 by norm_num)
      | decide)
    exact ⟨hs, window_even W h p, window_hasCompactSupport W h p,
      classK_of_real_even h2 (window_hasCompactSupport W h p)⟩

/-! ## The relation to the Epstein premises -/

/-- **THE WINDOW IS AN INPUT TO THE EPSTEIN PREMISES' EXPLICIT FORMULA, NOT A DISCHARGE OF IT**: under the window's own
obligations, `EpsteinPremises.ef` evaluates at the window's self-convolution. The premises are consumed, not concluded. -/
theorem epstein_ef_at_window (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hE : EpsteinPremises Z rhs) {W h : ℝ}
    (hW : 0 ≤ W) (hh : 0 < h) (hP : WindowObligations W h) (p : ℕ) (hp : 6 ≤ p) :
    (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) *
        Zeta23.paperFT (Zeta23.EF.weilTest (phiC (window W h p)) (phiC (window W h p))) (Zeta23.gammaOf ρ))
      = rhs (Zeta23.EF.weilTest (phiC (window W h p)) (phiC (window W h p))) := by
  have hw : PlateauRampWindow W h := plateauRampWindow_of hW hh hP
  unfold PlateauRampWindow WindowInClassK at hw
  obtain ⟨-, hK⟩ := hw
  obtain ⟨-, -, -, hk⟩ := hK p hp
  unfold classK at hk
  obtain ⟨he, hc, hs, -⟩ := hk
  exact hE.ef _ hc hs he

end PlateauRamp
end Schema
end SIDEExplicitFormula
