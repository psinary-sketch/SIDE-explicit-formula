/-
SIDE-explicit-formula -- SIDEExplicitFormula/TwoPropertyWindow.lean
THIS PROGRAMME'S WORK (act b524, ruling (R133)(5); W-ORD-WEIL-CONVERSE's (f)(i), the fold's (f1)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(f)(i) ON VARIANT (B). The window of (R129)(2): `h = (gamma_0^2 + D^2)(cos(gamma_0 .) phi)` for a real, compactly
supported `phi`, and `k = weilTest h h`. Proved here for EVERY real `phi` with `ContDiff R 4 phi` and compact support:
(i) `k` is in `classK` (a real `h` makes `k` even by translation invariance alone -- evenness of `phi` is not used);
(ii) `paperFT h gamma_0 = 0`; (iii) `paperFT h z = (gamma_0^2 - z^2) * paperFT (cos(gamma_0 .) phi) z`, by
integration by parts twice on the whole line (compact support kills the boundary terms).

THE PLATEAU (made concrete at b527, ruling (R137)(2)). `plateau F L` is `smoothTransition ((L - |u|) / (F L))`,
written as `smoothTransition ((L - u) / (F L)) * smoothTransition ((L + u) / (F L))` -- `Real.smoothTransition` in
Mathlib's closed form, no base chosen: flat (= 1) on `[-(1-F)L, (1-F)L]`, support `(-L, L)`, the two ramps together a
fraction `F` of the support, `C^n` for EVERY `n`, even. (At b524 it was a `ContDiffBump` over `someContDiffBumpBase`,
a base picked by `Classical.choice` with no values to evaluate -- b526.) The b519 values are the named instance
`b519Plateau a = plateau (1/4) (log a)`. **ITS RAMP IS THE exp(-1/x) TRANSITION, NOT THE ORDER-p B-SPLINE OF THE
NUMERICAL INSTRUMENT (b519, b522 at p = 7)**: the two share support, flat part, ramp fraction and the zero factor, and
differ in the ramp's profile; (i)-(iii) hold for either, being stated for every `C^4` compactly supported real `phi`.

THE HYPOTHESIS OF (f), STATED AND NOT PROVED (`f_pair_hypothesis`): at `rho_0 = beta + i gamma_0`, `delta = beta - 1/2`,
the real part of the pair's term (the four images' `paperFT k (gammaOf rho)`) is at most
`- fConst * delta^2 * |windowSlope|^2 * realizedGrowth phi delta ^ 2`, with `realizedGrowth phi delta =
(INT phi(u) cosh(delta u) du) / INT phi` -- defined as that integral, not as `exp(delta L)` ((R133)(4)).
The numerical instance: at a = 34 (variant (B), B-spline ramp p = 7, gamma_0 = 16.290216) G = 1.3607, read from
`relay/data/b522_cells.jsonl` (b522) and re-priced in `relay/data/b523_reread.json` (b523), where the pair's ratio to
the rest first reaches -1 and the cell is negative beyond its bound, VERIFIED-EST-TAIL.

THE (f) LEMMAS THAT REMAIN, by the fold's names (FINDINGS, W-ORD-WEIL-CONVERSE, b516):
  (f)(ii)  = (f2): the pair's term bounded above by the negative of order delta^2 (slope)^2 -- `f_pair_hypothesis`.
  (f)(iii) = (f3): the remaining zeros bounded above -- the uniformity over unknown zeros. (R133)(4)'s two ingredients,
           read off the Q0 instrument (b523: sigma_max and N(T) <= M0 + E): for zeta, the real parts -- the kernel's
           zero configuration lies in the closed strip 0 <= beta <= 1 (`Zeta23` Defs, `zetaZeroConfig`) -- and the
           count -- `Zeta23.RvM.zetaZeroConfig_local_count`.
  (f)(iv)  = (f4): the assembly -- not-RH, an off-line rho_0, this window at its ordinate, zeroSide k < 0 for a large
           enough width, b321_identity, not h2_sign.
Nothing here is a statement about the zeros of zeta or about RH.
-/
import SIDEExplicitFormula.H2Sign

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The plateau -/

/-- **The plateau**, ramp fraction `F`, half-width `L`: `phi(u) = smoothTransition ((L - |u|) / (F L))`, written as the
product of the two one-sided transitions so that it is visibly smooth (`plateau_apply_abs` proves the two forms equal):
flat (= 1) on `[-(1-F)L, (1-F)L]`, zero outside `(-L, L)`, the ramps a fraction `F` of the support. The hypotheses fix the
parameters' range; the formula does not use them. `Real.smoothTransition` is Mathlib's closed form
`expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`, `expNegInvGlue x = exp (-1/x)` for `x > 0` and `0` else. -/
def plateau (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) : ℝ → ℝ :=
  fun u => Real.smoothTransition ((L - u) / (F * L)) * Real.smoothTransition ((L + u) / (F * L))

/-- The plateau is `C^n` for every `n`. -/
theorem plateau_contDiff (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (n : ℕ∞) :
    ContDiff ℝ n (plateau F L hF0 hF1 hL) := by
  unfold plateau
  first
  | exact (Real.smoothTransition.contDiff.comp (((contDiff_const (c := L)).sub contDiff_id).div_const (F * L))).mul
      (Real.smoothTransition.contDiff.comp (((contDiff_const (c := L)).add contDiff_id).div_const (F * L)))
  | fun_prop

/-- The plateau is even. -/
theorem plateau_even (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (x : ℝ) :
    plateau F L hF0 hF1 hL (-x) = plateau F L hF0 hF1 hL x := by
  show Real.smoothTransition ((L - -x) / (F * L)) * Real.smoothTransition ((L + -x) / (F * L)) =
    Real.smoothTransition ((L - x) / (F * L)) * Real.smoothTransition ((L + x) / (F * L))
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/-- The plateau has compact support. -/
theorem plateau_hasCompactSupport (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) :
    HasCompactSupport (plateau F L hF0 hF1 hL) := by
  have hFL : 0 < F * L := mul_pos hF0 hL
  refine HasCompactSupport.intro (K := Set.Icc (-L) L) isCompact_Icc ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  show Real.smoothTransition ((L - x) / (F * L)) * Real.smoothTransition ((L + x) / (F * L)) = 0
  rcases hx with h | h
  · have h2 : (L + x) / (F * L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hFL.le
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]
  · have h1 : (L - x) / (F * L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hFL.le
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

/-- The plateau is flat, equal to 1, on `[-(1-F)L, (1-F)L]`. -/
theorem plateau_eq_one (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (x : ℝ) (hx : |x| ≤ (1 - F) * L) :
    plateau F L hF0 hF1 hL x = 1 := by
  have hFL : 0 < F * L := mul_pos hF0 hL
  have hx' : |x| ≤ L - F * L := by linarith [show (1 - F) * L = L - F * L by ring]
  have h1 : 1 ≤ (L - x) / (F * L) := by
    rw [one_le_div₀ hFL]
    linarith [le_abs_self x]
  have h2 : 1 ≤ (L + x) / (F * L) := by
    rw [one_le_div₀ hFL]
    linarith [neg_abs_le x]
  show Real.smoothTransition ((L - x) / (F * L)) * Real.smoothTransition ((L + x) / (F * L)) = 1
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

/-- The two forms agree: `plateau F L u = smoothTransition ((L - |u|) / (F L))` at every `u`. -/
theorem plateau_apply_abs (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (x : ℝ) :
    plateau F L hF0 hF1 hL x = Real.smoothTransition ((L - |x|) / (F * L)) := by
  have hFL : 0 < F * L := mul_pos hF0 hL
  have hle : F * L ≤ L := by nlinarith
  show Real.smoothTransition ((L - x) / (F * L)) * Real.smoothTransition ((L + x) / (F * L)) = _
  rcases le_total 0 x with hx | hx
  · have h2 : 1 ≤ (L + x) / (F * L) := by
      rw [one_le_div₀ hFL]
      linarith
    rw [Real.smoothTransition.one_of_one_le h2, mul_one, abs_of_nonneg hx]
  · have h1 : 1 ≤ (L - x) / (F * L) := by
      rw [one_le_div₀ hFL]
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, one_mul, abs_of_nonpos hx, sub_neg_eq_add]

/-- **The b519 values as the named instance:** ramp fraction `1/4`, half-width `log a`. -/
def b519Plateau (a : ℝ) (ha : 1 < a) : ℝ → ℝ :=
  plateau (1 / 4) (Real.log a) (by norm_num) (by norm_num) (Real.log_pos ha)

/-! ### The window -/

/-- `cos(gamma_0 u) phi(u)`. -/
def cosWin (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun u => Real.cos (γ₀ * u) * φ u

/-- **The window** `h = (gamma_0^2 + D^2)(cos(gamma_0 .) phi)`. -/
def window (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun u => γ₀ ^ 2 * cosWin γ₀ φ u + deriv (deriv (cosWin γ₀ φ)) u

/-- The window as the kernel's complex-valued test function. -/
def windowC (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ → ℂ := fun u => (window γ₀ φ u : ℂ)

/-- `cos(gamma_0 .) phi` as a complex-valued function. -/
def cosWinC (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ → ℂ := fun u => (cosWin γ₀ φ u : ℂ)

/-- **k = weilTest h h.** -/
def kWin (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ → ℂ := Zeta23.EF.weilTest (windowC γ₀ φ) (windowC γ₀ φ)

theorem cosWin_contDiff {γ₀ : ℝ} {φ : ℝ → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (cosWin γ₀ φ) := by
  unfold cosWin
  first
  | exact ((contDiff_const (c := γ₀)).mul contDiff_id).cos.mul hφ
  | fun_prop

theorem cosWin_hasCompactSupport {γ₀ : ℝ} {φ : ℝ → ℝ} (hφs : HasCompactSupport φ) :
    HasCompactSupport (cosWin γ₀ φ) := by
  show HasCompactSupport ((fun u => Real.cos (γ₀ * u)) * φ)
  exact hφs.mul_left

theorem window_contDiff {γ₀ : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) : ContDiff ℝ 2 (window γ₀ φ) := by
  have hg : ContDiff ℝ 4 (cosWin γ₀ φ) := cosWin_contDiff hφ
  have h3 : ContDiff ℝ 3 (deriv (cosWin γ₀ φ)) :=
    (hg.of_le (by norm_num) : ContDiff ℝ (3 + 1) (cosWin γ₀ φ)).deriv'
  have h2 : ContDiff ℝ 2 (deriv (deriv (cosWin γ₀ φ))) :=
    (h3.of_le (by norm_num) : ContDiff ℝ (2 + 1) (deriv (cosWin γ₀ φ))).deriv'
  have hg2 : ContDiff ℝ 2 (cosWin γ₀ φ) := hg.of_le (by norm_num)
  unfold window
  exact ((contDiff_const (c := γ₀ ^ 2)).mul hg2).add h2

theorem window_hasCompactSupport {γ₀ : ℝ} {φ : ℝ → ℝ} (hφs : HasCompactSupport φ) :
    HasCompactSupport (window γ₀ φ) := by
  have hg : HasCompactSupport (cosWin γ₀ φ) := cosWin_hasCompactSupport hφs
  show HasCompactSupport ((fun _ => γ₀ ^ 2) * cosWin γ₀ φ + deriv (deriv (cosWin γ₀ φ)))
  exact hg.mul_left.add hg.deriv.deriv

theorem windowC_contDiff {γ₀ : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) : ContDiff ℝ 2 (windowC γ₀ φ) :=
  Complex.ofRealCLM.contDiff.comp (window_contDiff hφ)

theorem windowC_hasCompactSupport {γ₀ : ℝ} {φ : ℝ → ℝ} (hφs : HasCompactSupport φ) :
    HasCompactSupport (windowC γ₀ φ) :=
  (window_hasCompactSupport hφs).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

/-- For a real-valued `f`, `weilTest f f` is even: translation invariance of Lebesgue measure. -/
theorem weilTest_ofReal_even (f : ℝ → ℝ) (x : ℝ) :
    Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-x) =
      Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) x := by
  have shift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => (f t : ℂ) * (f (t - x) : ℂ)) x
  simp only [add_sub_cancel_right] at shift
  simp only [Zeta23.EF.weilTest, convolution_def, Zeta23.EF.tilde, ContinuousLinearMap.mul_apply',
    Complex.conj_ofReal, neg_sub, sub_neg_eq_add]
  rw [← shift]
  congr 1
  ext t
  ring

/-- **(i) `k` is in classK.** -/
theorem kWin_classK (γ₀ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ) :
    classK (kWin γ₀ φ) := by
  have hh : ContDiff ℝ 2 (windowC γ₀ φ) := windowC_contDiff hφ
  have hhs : HasCompactSupport (windowC γ₀ φ) := windowC_hasCompactSupport hφs
  exact ⟨fun x => weilTest_ofReal_even (window γ₀ φ) x,
    Zeta23.EF.weilTest_contDiff hh hh.continuous hhs,
    Zeta23.EF.weilTest_hasCompactSupport hhs hhs,
    windowC γ₀ φ, hh, hhs, rfl⟩

/-! ### The factorisation -/

theorem hasDerivAt_expIz (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ)))
      (Complex.I * z * Complex.exp (Complex.I * z * (x : ℂ))) x := by
  have h := ((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * z)).cexp.comp_ofReal
  simp only [id_eq, mul_one] at h
  convert h using 1
  ring

/-- One integration by parts on the whole line: `INT F' e = -(i z) INT F e`, `e(u) = exp(i z u)`. -/
theorem ibp_step (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hFs : HasCompactSupport F) (z : ℂ) :
    (∫ u, ((deriv F u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) =
      -(Complex.I * z) * ∫ u, ((F u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) := by
  have hFc : Continuous (fun t => (F t : ℂ)) := Complex.continuous_ofReal.comp hF.continuous
  have hF'c : Continuous (fun t => ((deriv F t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hF.continuous_deriv le_rfl)
  have hec : Continuous (fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))) := by fun_prop
  have hFcs : HasCompactSupport (fun t => (F t : ℂ)) :=
    hFs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hF'cs : HasCompactSupport (fun t => ((deriv F t : ℝ) : ℂ)) :=
    hFs.deriv.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => (F t : ℂ)) (u' := fun t => ((deriv F t : ℝ) : ℂ))
    (v := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ)))
    (v' := fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * (t : ℂ)))
    (fun x _ => ((hF.differentiable one_ne_zero).differentiableAt.hasDerivAt).ofReal_comp)
    (fun x _ => hasDerivAt_expIz z x)
    ((hFc.mul (continuous_const.mul hec)).integrable_of_hasCompactSupport
      (hFcs.mul_right (f' := fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * (t : ℂ)))))
    ((hF'c.mul hec).integrable_of_hasCompactSupport
      (hF'cs.mul_right (f' := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ)))))
    ((hFc.mul hec).integrable_of_hasCompactSupport
      (hFcs.mul_right (f' := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ)))))
  have h2 : (∫ u, (F u : ℂ) * (Complex.I * z * Complex.exp (Complex.I * z * (u : ℂ)))) =
      (Complex.I * z) * ∫ u, (F u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    ext u
    ring
  rw [h2] at key
  linear_combination key

/-- Twice by parts: `paperFT (c g + g'') z = (c - z^2) paperFT g z` for a real `C^2` compactly supported `g`. -/
theorem paperFT_second_order (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g) (c : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun u => ((c * g u + deriv (deriv g) u : ℝ) : ℂ)) z =
      ((c : ℂ) - z ^ 2) * Zeta23.paperFT (fun u => (g u : ℂ)) z := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hdg : ContDiff ℝ 1 (deriv g) := (hg.of_le (by norm_num) : ContDiff ℝ (1 + 1) g).deriv'
  have hE : Continuous (fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))) := by fun_prop
  have hgc : Continuous (fun t => (g t : ℂ)) := Complex.continuous_ofReal.comp hg.continuous
  have hg2c : Continuous (fun t => ((deriv (deriv g) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hdg.continuous_deriv le_rfl)
  have i1 : Integrable (fun u => (c : ℂ) * ((g u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)))) :=
    ((hgc.mul hE).integrable_of_hasCompactSupport
      ((hgs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_right
        (f' := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))))).const_mul _
  have i2 : Integrable (fun u => ((deriv (deriv g) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) :=
    (hg2c.mul hE).integrable_of_hasCompactSupport
      ((hgs.deriv.deriv.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_right
        (f' := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))))
  unfold Zeta23.paperFT
  calc (∫ u, ((c * g u + deriv (deriv g) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)))
      = ∫ u, ((c : ℂ) * ((g u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) +
          ((deriv (deriv g) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) := by
        congr 1
        ext u
        push_cast
        ring
    _ = (c : ℂ) * (∫ u, (g u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) +
          ∫ u, ((deriv (deriv g) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) := by
        rw [integral_add i1 i2, integral_const_mul]
    _ = ((c : ℂ) - z ^ 2) * ∫ u, (g u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) := by
        rw [ibp_step (deriv g) hdg hgs.deriv z, ibp_step g hg1 hgs z]
        linear_combination (z ^ 2 * ∫ u, (g u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) * Complex.I_sq

/-- **(iii) the factorisation:** `paperFT h z = (gamma_0^2 - z^2) * paperFT (cos(gamma_0 .) phi) z`. -/
theorem paperFT_window (γ₀ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ) (z : ℂ) :
    Zeta23.paperFT (windowC γ₀ φ) z = ((γ₀ : ℂ) ^ 2 - z ^ 2) * Zeta23.paperFT (cosWinC γ₀ φ) z := by
  have h := paperFT_second_order (cosWin γ₀ φ) ((cosWin_contDiff hφ).of_le (by norm_num))
    (cosWin_hasCompactSupport hφs) (γ₀ ^ 2) z
  rw [Complex.ofReal_pow] at h
  exact h

/-- **(ii) the zero at the on-line point:** `paperFT h gamma_0 = 0`. -/
theorem paperFT_window_zero (γ₀ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ) :
    Zeta23.paperFT (windowC γ₀ φ) (γ₀ : ℂ) = 0 := by
  rw [paperFT_window γ₀ hφ hφs]
  simp

/-! ### The hypothesis of (f), stated and not proved -/

/-- **G, the plateau's realized growth at `delta`:** `INT phi cosh(delta u) du / INT phi` -- the integral, not
`exp(delta L)`. At a = 34 (B-spline ramp, p = 7) the instrument read G = 1.3607 (b522, b523). -/
def realizedGrowth (φ : ℝ → ℝ) (δ : ℝ) : ℝ := (∫ u, φ u * Real.cosh (δ * u)) / ∫ u, φ u

/-- The slope of `paperFT h` at `gamma_0`: `-2 gamma_0 * paperFT (cos(gamma_0 .) phi) gamma_0`, from (iii). -/
def windowSlope (γ₀ : ℝ) (φ : ℝ → ℝ) : ℂ := -2 * (γ₀ : ℂ) * Zeta23.paperFT (cosWinC γ₀ φ) (γ₀ : ℂ)

/-- The constant `c = 4`: four images, each `paperFT k (gammaOf rho) = paperFT h (gamma_0 -+ i delta)^2`, whose first
order in `delta` is `(slope * (-+ i delta))^2 = -delta^2 slope^2`, the growth `G` multiplying the transform off the line. -/
def fConst : ℝ := 4

/-- The pair's term: `paperFT k` at the four images `beta +- i gamma_0`, `1 - beta +- i gamma_0` of `rho_0`. -/
def pairTerm (γ₀ : ℝ) (φ : ℝ → ℝ) (β : ℝ) : ℂ :=
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ((β : ℂ) + (γ₀ : ℂ) * Complex.I)) +
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ((β : ℂ) - (γ₀ : ℂ) * Complex.I)) +
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ((1 - β : ℝ) + (γ₀ : ℂ) * Complex.I)) +
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ((1 - β : ℝ) - (γ₀ : ℂ) * Complex.I))

/-- **The hypothesis of (f)(ii), as a Prop, NOT PROVED:** the pair's term at `rho_0 = beta + i gamma_0` is at most
`- c delta^2 |slope|^2 G^2`, `delta = beta - 1/2`, `G = realizedGrowth phi delta`. -/
def f_pair_hypothesis (γ₀ : ℝ) (φ : ℝ → ℝ) (β : ℝ) : Prop :=
  (pairTerm γ₀ φ β).re ≤
    -fConst * (β - 1 / 2) ^ 2 * ‖windowSlope γ₀ φ‖ ^ 2 * realizedGrowth φ (β - 1 / 2) ^ 2

end B321
end SIDEExplicitFormula
