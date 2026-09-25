/-
SIDE-explicit-formula -- SIDEExplicitFormula/PowerWindow.lean
THIS PROGRAMME'S WORK (act b533, ruling (R143); W-ORD-WEIL-CONVERSE's f4, the power-window route, act one of two) --
NOT VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE POWER-WINDOW ROUTE TO f4, ITS FIRST HALF (L1-L6 of (R143)). For a real even window `g`, every zero term of
`k = weilTest g g` is `g^(z_rho)^2` (L1, `zero_term_sq`), and `k` is in classK (L2). The self-convolution `selfConv g`
is real (`selfConv_im_zero`) and its `j`-fold iterate `power g j` has transform `g^^(2^j)` (L3, `paperFT_power`), even,
smooth, supported in `[-2^j L, 2^j L]`. A real polynomial in `z^2` acts as the operator `SUM a_j (-1)^j D^(2j)` (L4,
`paperFT_polyOp`). The base window is the kernel's plateau, whose transform is nonzero at any given point for a small
enough width (L5, `base_nonzero_at`); for a fixed window the zeros with `|g^(gammaOf rho)|` above any positive level
are finitely many (`off_finite_above`), so an off-line zero of maximal score exists (`dominant_exists`), with `tieSet`
and `killSet` finite. A real interpolating polynomial with coefficients bounded independently of its targets exists
over any conjugation-closed node set (L6, `real_even_interpolant`). The seam of (R143)(4): `rh_strip` and
`rh_imp_rh_strip`; the reverse `rh_strip_imp_rh` a Prop, not proved. L7 and L8 are b534's. Nothing here is a statement
about the zeros of zeta or about RH.
-/
import SIDEExplicitFormula.RestBound
import SIDEExplicitFormula.H2Bridge
import Mathlib.LinearAlgebra.Lagrange

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### L1 -- the zero term of a real even window -/

/-- For a real even `g`: `conj (g^(conj z)) = g^(z)`. -/
theorem paperFT_conj_of_real_even {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (z : ℂ) :
    conj (Zeta23.paperFT (phiC g) (conj z)) = Zeta23.paperFT (phiC g) z := by
  rw [paperFT_ofReal_conj g (conj z), Complex.conj_conj, phiC_FT_neg hev]

/-- **L1:** for a real even continuous compactly supported `g`, `(weilTest g g)^(z) = g^(z)^2`. -/
theorem zero_term_sq {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (hc : Continuous g) (hs : HasCompactSupport g) (z : ℂ) :
    Zeta23.paperFT (Zeta23.EF.weilTest (phiC g) (phiC g)) z = (Zeta23.paperFT (phiC g) z) ^ 2 := by
  have hc' : Continuous (phiC g) := Complex.continuous_ofReal.comp hc
  have hs' : HasCompactSupport (phiC g) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  rw [Zeta23.EF.paperFT_weilTest hc' hc' hs' hs' z, paperFT_conj_of_real_even hev z, sq]

/-! ### L2 -- class membership -/

/-- `weilTest g g` is even for every real `g` (translation invariance; `g`'s own evenness is not used). -/
theorem weilTest_even_of_even (g : ℝ → ℝ) (x : ℝ) :
    Zeta23.EF.weilTest (phiC g) (phiC g) (-x) = Zeta23.EF.weilTest (phiC g) (phiC g) x :=
  weilTest_ofReal_even g x

/-- **L2:** for a real `C^2` compactly supported `g`, `weilTest g g` is in classK. -/
theorem classK_of_real_even {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    classK (Zeta23.EF.weilTest (phiC g) (phiC g)) := by
  have hh : ContDiff ℝ 2 (phiC g) := Complex.ofRealCLM.contDiff.comp hg
  have hhs : HasCompactSupport (phiC g) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  exact ⟨fun x => weilTest_ofReal_even g x, Zeta23.EF.weilTest_contDiff hh hh.continuous hhs,
    Zeta23.EF.weilTest_hasCompactSupport hhs hhs, phiC g, hh, hhs, rfl⟩

/-! ### L3 -- the powers -/

/-- The self-convolution, read back as a real function. -/
def selfConv (g : ℝ → ℝ) : ℝ → ℝ := fun x => (Zeta23.EF.weilTest (phiC g) (phiC g) x).re

theorem weilTest_phiC (g : ℝ → ℝ) (x : ℝ) :
    Zeta23.EF.weilTest (phiC g) (phiC g) x = ((∫ t, g t * g (t - x) : ℝ) : ℂ) := by
  have hre : ((∫ t, g t * g (t - x) : ℝ) : ℂ) = ∫ t, ((g t * g (t - x) : ℝ) : ℂ) := integral_ofReal.symm
  rw [hre]
  simp only [Zeta23.EF.weilTest, convolution_def, Zeta23.EF.tilde, ContinuousLinearMap.mul_apply', phiC,
    Complex.conj_ofReal, neg_sub]
  congr 1
  ext t
  first
  | (push_cast; ring)
  | push_cast
  | simp

/-- **The self-convolution of a real function is real.** -/
theorem selfConv_im_zero (g : ℝ → ℝ) (x : ℝ) : (Zeta23.EF.weilTest (phiC g) (phiC g) x).im = 0 := by
  rw [weilTest_phiC]
  exact Complex.ofReal_im _

theorem selfConv_eq (g : ℝ → ℝ) (x : ℝ) : selfConv g x = ∫ t, g t * g (t - x) := by
  show (Zeta23.EF.weilTest (phiC g) (phiC g) x).re = _
  rw [weilTest_phiC, Complex.ofReal_re]

theorem phiC_selfConv (g : ℝ → ℝ) : phiC (selfConv g) = Zeta23.EF.weilTest (phiC g) (phiC g) := by
  funext x
  show (((Zeta23.EF.weilTest (phiC g) (phiC g) x).re : ℝ) : ℂ) = Zeta23.EF.weilTest (phiC g) (phiC g) x
  rw [weilTest_phiC, Complex.ofReal_re]

theorem selfConv_even (g : ℝ → ℝ) (x : ℝ) : selfConv g (-x) = selfConv g x :=
  congrArg Complex.re (weilTest_ofReal_even g x)

theorem selfConv_support {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    Function.support (selfConv g) ⊆ Set.Icc (-(2 * L)) (2 * L) := by
  intro x hx
  by_contra hout
  apply hx
  rw [selfConv_eq]
  have hz : ∀ t, g t * g (t - x) = 0 := by
    intro t
    by_cases h1 : g t = 0
    · rw [h1, zero_mul]
    · have ht : t ∈ Set.Icc (-L) L := hs h1
      have h2 : g (t - x) = 0 := by
        by_contra h2
        have ht2 : t - x ∈ Set.Icc (-L) L := hs h2
        exact hout ⟨by linarith [ht.1, ht.2, ht2.1, ht2.2], by linarith [ht.1, ht.2, ht2.1, ht2.2]⟩
      rw [h2, mul_zero]
  simp [hz]

theorem selfConv_contDiff {g : ℝ → ℝ} {n : ℕ∞} (hg : ContDiff ℝ n g) (hs : HasCompactSupport g) :
    ContDiff ℝ n (selfConv g) := by
  have hh : ContDiff ℝ n (phiC g) := Complex.ofRealCLM.contDiff.comp hg
  have hhs : HasCompactSupport (phiC g) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hloc : LocallyIntegrable (Zeta23.EF.tilde (phiC g)) volume :=
    (Zeta23.EF.continuous_tilde hh.continuous).locallyIntegrable
  exact Complex.reCLM.contDiff.comp (hhs.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hh hloc)

/-- The `j`-fold iterated self-convolution. -/
def power (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | j + 1 => selfConv (power g j)

theorem power_even {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) : ∀ j x, power g j (-x) = power g j x
  | 0, x => hev x
  | j + 1, x => selfConv_even (power g j) x

theorem power_support {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    ∀ j, Function.support (power g j) ⊆ Set.Icc (-(2 ^ j * L)) (2 ^ j * L)
  | 0 => by
    show Function.support g ⊆ Set.Icc (-(2 ^ 0 * L)) (2 ^ 0 * L)
    simpa only [pow_zero, one_mul] using hs
  | j + 1 => by
    intro x hx
    have h := selfConv_support (power_support hs j) hx
    rw [pow_succ]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem power_contDiff {g : ℝ → ℝ} {L : ℝ} {n : ℕ∞} (hg : ContDiff ℝ n g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) : ∀ j, ContDiff ℝ n (power g j)
  | 0 => hg
  | j + 1 => selfConv_contDiff (power_contDiff hg hs j) (hasCompactSupport_of_Icc (power_support hs j))

/-- **L3:** `(power g j)^ = g^^(2^j)`. -/
theorem paperFT_power {g : ℝ → ℝ} {L : ℝ} {n : ℕ∞} (hev : ∀ x, g (-x) = g x) (hg : ContDiff ℝ n g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (z : ℂ) :
    ∀ j, Zeta23.paperFT (phiC (power g j)) z = (Zeta23.paperFT (phiC g) z) ^ (2 ^ j)
  | 0 => by
    show Zeta23.paperFT (phiC g) z = (Zeta23.paperFT (phiC g) z) ^ (2 ^ 0)
    rw [pow_zero, pow_one]
  | j + 1 => by
    show Zeta23.paperFT (phiC (selfConv (power g j))) z = _
    rw [phiC_selfConv, zero_term_sq (power_even hev j) (power_contDiff hg hs j).continuous
      (hasCompactSupport_of_Icc (power_support hs j)) z, paperFT_power hev hg hs z j, ← pow_mul, pow_succ]

/-! ### L4 -- the polynomial operator -/

def polyCoef (a : List ℝ) (j : ℕ) : ℝ := a.getD j 0

/-- `SUM_j a_j (-1)^j D^(2j) g`. -/
def polyOp (a : List ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun u => ∑ j ∈ Finset.range a.length, polyCoef a j * (-1) ^ j * iteratedDeriv (2 * j) g u

/-- `SUM_j a_j z^(2j)`. -/
def polyEval (a : List ℝ) (z : ℂ) : ℂ := ∑ j ∈ Finset.range a.length, (polyCoef a j : ℂ) * z ^ (2 * j)

theorem paperFT_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hc : ∀ j ∈ s, Continuous (f j)) (hs : ∀ j ∈ s, HasCompactSupport (f j)) (z : ℂ) :
    Zeta23.paperFT (phiC (fun u => ∑ j ∈ s, c j * f j u)) z = ∑ j ∈ s, (c j : ℂ) * Zeta23.paperFT (phiC (f j)) z := by
  have hint : ∀ j ∈ s, Integrable (fun u : ℝ => (c j : ℂ) * ((f j u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)))) :=
    fun j hj => (phiC_exp_integrable (hc j hj) (hs j hj) z).const_mul _
  simp only [Zeta23.paperFT, phiC]
  calc (∫ u, ((∑ j ∈ s, c j * f j u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)))
      = ∫ u, ∑ j ∈ s, (c j : ℂ) * ((f j u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) := by
        congr 1
        ext u
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = ∑ j ∈ s, ∫ u, (c j : ℂ) * ((f j u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) := integral_finsetSum s hint
    _ = ∑ j ∈ s, (c j : ℂ) * ∫ u, (f j u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) :=
        Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)

theorem neg_one_pow_mul_iz_pow (z : ℂ) (j : ℕ) : (-1 : ℂ) ^ j * (-(I * z)) ^ (2 * j) = z ^ (2 * j) := by
  have e2 : (-(I * z)) ^ 2 = -(z ^ 2) := by linear_combination (z ^ 2) * Complex.I_sq
  rw [pow_mul, e2, show -(z ^ 2) = (-1 : ℂ) * z ^ 2 by ring, mul_pow, ← mul_assoc, ← mul_pow,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow, one_mul, ← pow_mul]

/-- **L4:** `(polyOp a g)^(z) = (SUM_j a_j z^(2j)) g^(z)`. -/
theorem paperFT_polyOp (a : List ℝ) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ (2 * a.length) g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (z : ℂ) :
    Zeta23.paperFT (phiC (polyOp a g)) z = polyEval a z * Zeta23.paperFT (phiC g) z := by
  have hle : ∀ j ∈ Finset.range a.length, ((2 * j : ℕ) : WithTop ℕ∞) ≤ ((2 * a.length : ℕ) : WithTop ℕ∞) := by
    intro j hj
    have := Finset.mem_range.mp hj
    exact_mod_cast (show 2 * j ≤ 2 * a.length by omega)
  have hc : ∀ j ∈ Finset.range a.length, Continuous (iteratedDeriv (2 * j) g) :=
    fun j hj => hg.continuous_iteratedDeriv (2 * j) (hle j hj)
  have hcs : ∀ j ∈ Finset.range a.length, HasCompactSupport (iteratedDeriv (2 * j) g) :=
    fun j _ => hasCompactSupport_of_Icc (support_iteratedDeriv_Icc (2 * j) hs)
  have key := paperFT_sum (Finset.range a.length) (fun j => polyCoef a j * (-1) ^ j) (fun j => iteratedDeriv (2 * j) g)
    hc hcs z
  beta_reduce at key
  show Zeta23.paperFT (phiC (fun u => ∑ j ∈ Finset.range a.length, polyCoef a j * (-1) ^ j * iteratedDeriv (2 * j) g u)) z = _
  rw [key, polyEval, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [paperFT_iteratedDeriv (2 * j) g (hg.of_le (hle j hj)) (hasCompactSupport_of_Icc hs) z]
  have e := neg_one_pow_mul_iz_pow z j
  push_cast
  rw [← e]
  ring

theorem iteratedDeriv_even_even {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (j : ℕ) (x : ℝ) :
    iteratedDeriv (2 * j) g (-x) = iteratedDeriv (2 * j) g x := by
  have hfun : (fun y => g (-y)) = g := funext hev
  have h := iteratedDeriv_comp_neg (2 * j) g x
  rw [hfun] at h
  rw [h, pow_mul, neg_one_sq, one_pow, one_smul]

theorem polyOp_even (a : List ℝ) {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (x : ℝ) : polyOp a g (-x) = polyOp a g x := by
  unfold polyOp
  exact Finset.sum_congr rfl (fun j _ => by rw [iteratedDeriv_even_even hev j x])

theorem polyOp_support (a : List ℝ) {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    Function.support (polyOp a g) ⊆ Set.Icc (-L) L := by
  intro u hu
  by_contra hout
  apply hu
  unfold polyOp
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h0 : iteratedDeriv (2 * j) g u = 0 := by
    by_contra h
    exact hout (support_iteratedDeriv_Icc (2 * j) hs h)
  rw [h0, mul_zero]

theorem polyOp_contDiff (a : List ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyOp a g) := by
  unfold polyOp
  refine ContDiff.sum (fun j _ => ?_)
  refine contDiff_const.mul ?_
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv (2 * j) hg

/-! ### L5 -- the base window and the dominant zero -/

theorem plateau_support_Icc (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) :
    Function.support (plateau F L hF0 hF1 hL) ⊆ Set.Icc (-L) L := by
  have hFL : 0 < F * L := mul_pos hF0 hL
  intro x hx
  by_contra hout
  apply hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hout
  show Real.smoothTransition ((L - x) / (F * L)) * Real.smoothTransition ((L + x) / (F * L)) = 0
  rcases hout with h | h
  · have h2 : (L + x) / (F * L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hFL.le
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]
  · have h1 : (L - x) / (F * L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hFL.le
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

theorem plateau_nonneg (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) (x : ℝ) : 0 ≤ plateau F L hF0 hF1 hL x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_integral_pos (F L : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hL : 0 < L) :
    0 < ∫ u, plateau F L hF0 hF1 hL u := by
  have h0 : plateau F L hF0 hF1 hL 0 = 1 :=
    plateau_eq_one F L hF0 hF1 hL 0 (by rw [abs_zero]; exact mul_nonneg (by linarith) hL.le)
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((plateau_contDiff F L hF0 hF1 hL 0).continuous) (plateau_hasCompactSupport F L hF0 hF1 hL)
    (fun x => plateau_nonneg F L hF0 hF1 hL x) (by rw [h0]; exact one_ne_zero)

/-- **L5, the base:** at any `z`, the plateau's transform is nonzero for every small enough width. The route is the
estimate `|g^(z) - INT g| <= (1/2) INT g` once `|z| L <= 1/4`; no decay bound and no bound on any ordinate is used. -/
theorem base_nonzero_at (F : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (z : ℂ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ (L : ℝ) (hL : 0 < L), L ≤ L₀ → Zeta23.paperFT (phiC (plateau F L hF0 hF1 hL)) z ≠ 0 := by
  refine ⟨1 / (4 * (‖z‖ + 1)), by positivity, fun L hL hLL => ?_⟩
  set φ := plateau F L hF0 hF1 hL with hφdef
  have hcont : Continuous φ := (plateau_contDiff F L hF0 hF1 hL 0).continuous
  have hcs : HasCompactSupport φ := plateau_hasCompactSupport F L hF0 hF1 hL
  have hsupp := plateau_support_Icc F L hF0 hF1 hL
  have hS : 0 < ∫ u, φ u := plateau_integral_pos F L hF0 hF1 hL
  have hzL : ‖z‖ * L ≤ 1 / 4 := by
    have h1 : ‖z‖ * L ≤ ‖z‖ * (1 / (4 * (‖z‖ + 1))) := mul_le_mul_of_nonneg_left hLL (norm_nonneg z)
    have h2 : ‖z‖ * (1 / (4 * (‖z‖ + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith [norm_nonneg z]
    linarith
  have hφc : Continuous (fun u => (φ u : ℂ)) := Complex.continuous_ofReal.comp hcont
  have hφcs : HasCompactSupport (fun u => (φ u : ℂ)) := hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have iE : Integrable (fun u : ℝ => (φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) :=
    phiC_exp_integrable hcont hcs z
  have i1 : Integrable (fun u : ℝ => (φ u : ℂ)) := hφc.integrable_of_hasCompactSupport hφcs
  have hpt : ∀ u, ‖(φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖ ≤ φ u * (1 / 2) := by
    intro u
    by_cases h0 : φ u = 0
    · rw [h0]; simp
    · have hu : u ∈ Set.Icc (-L) L := hsupp h0
      have hnu : ‖Complex.I * z * (u : ℂ)‖ ≤ 1 / 4 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have : |u| ≤ L := abs_le.mpr ⟨hu.1, hu.2⟩
        nlinarith [norm_nonneg z, abs_nonneg u]
      have he : ‖Complex.exp (Complex.I * z * (u : ℂ)) - 1‖ ≤ 2 * ‖Complex.I * z * (u : ℂ)‖ :=
        Complex.norm_exp_sub_one_le (by linarith)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg F L hF0 hF1 hL u)]
      exact mul_le_mul_of_nonneg_left (by linarith) (plateau_nonneg F L hF0 hF1 hL u)
  have hdiff : Zeta23.paperFT (phiC φ) z - ((∫ u, φ u : ℝ) : ℂ) =
      ∫ u, (φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1) := by
    have hre : ((∫ u, φ u : ℝ) : ℂ) = ∫ u, ((φ u : ℝ) : ℂ) := integral_ofReal.symm
    rw [hre]
    simp only [Zeta23.paperFT, phiC]
    rw [← integral_sub iE i1]
    congr 1
    ext u
    ring
  have hbound : ‖Zeta23.paperFT (phiC φ) z - ((∫ u, φ u : ℝ) : ℂ)‖ ≤ (∫ u, φ u) * (1 / 2) := by
    rw [hdiff]
    calc ‖∫ u, (φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖
        ≤ ∫ u, ‖(φ u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ)) - 1)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u, φ u * (1 / 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hcont.integrable_of_hasCompactSupport hcs).mul_const _) (Filter.Eventually.of_forall hpt)
      _ = (∫ u, φ u) * (1 / 2) := integral_mul_const _ _
  intro h0
  rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at hbound
  linarith

/-- The score of a zero for a fixed window: `|g^(gammaOf rho)|`. -/
def offScore (g : ℝ → ℝ) (ρ : ℂ) : ℝ := ‖Zeta23.paperFT (phiC g) (Zeta23.gammaOf ρ)‖

/-- **L5:** for a fixed window, the zeros with score at least `c > 0` are finitely many. -/
theorem off_finite_above (Z : Zeta23.ZeroConfig) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ 4 g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    {ρ | ρ ∈ Z.carrier ∧ c ≤ offScore g ρ}.Finite := by
  set B : ℝ := (∫ u, |iteratedDeriv 4 g u|) * Real.exp (L / 2) with hB
  set T : ℝ := max 1 (B / c) with hT
  apply (Z.finite_window (-T - 1) T).subset
  intro ρ hρ
  obtain ⟨hρc, hcρ⟩ := hρ
  have hstrip := Z.strip ρ hρc
  set z := Zeta23.gammaOf ρ with hz
  have hre : z.re = ρ.im := by rw [hz]; exact gammaOf_re' ρ
  have him : |z.im| ≤ 1 / 2 := by
    rw [hz, gammaOf_im', abs_neg]
    exact abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  have hdec := paperFT_decay 4 hg hs z
  have hA : 0 ≤ ∫ u, |iteratedDeriv 4 g u| := integral_nonneg fun _ => abs_nonneg _
  have hexp : Real.exp (L * |z.im|) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  have h1 : offScore g ρ * ‖z‖ ^ 4 ≤ B := by
    show ‖Zeta23.paperFT (phiC g) z‖ * ‖z‖ ^ 4 ≤ B
    exact hdec.trans (mul_le_mul_of_nonneg_left hexp hA)
  have h2 : ‖z‖ ^ 4 ≤ B / c := by
    rw [le_div_iff₀ hc]
    have := mul_le_mul_of_nonneg_right hcρ (pow_nonneg (norm_nonneg z) 4)
    linarith
  have h3 : ‖z‖ ≤ T := by
    by_cases hz1 : ‖z‖ ≤ 1
    · exact hz1.trans (le_max_left _ _)
    · push_neg at hz1
      have a1 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
      have a2 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 4 := by nlinarith
      exact (a1.trans (a2.trans h2)).trans (le_max_right _ _)
  have h4 : |ρ.im| ≤ T := by
    rw [← hre]
    exact (Complex.abs_re_le_norm z).trans h3
  exact ⟨hρc, by linarith [neg_abs_le ρ.im], by linarith [le_abs_self ρ.im]⟩

/-- **L5, the dominant zero:** given an off-line zero of positive score, there is an off-line zero of maximal score. -/
theorem dominant_exists (Z : Zeta23.ZeroConfig) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ 4 g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) (ρ₁ : ℂ) (h₁ : ρ₁ ∈ Z.carrier) (hoff : ρ₁.re ≠ 1 / 2)
    (hpos : 0 < offScore g ρ₁) :
    ∃ ρs ∈ Z.carrier, ρs.re ≠ 1 / 2 ∧ 0 < offScore g ρs ∧
      ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → offScore g ρ ≤ offScore g ρs := by
  set S : Set ℂ := {ρ | ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ offScore g ρ₁ ≤ offScore g ρ} with hS
  have hfin : S.Finite :=
    (off_finite_above Z hg hs hL _ hpos).subset (fun ρ hρ => ⟨hρ.1, hρ.2.2⟩)
  have hne : S.Nonempty := ⟨ρ₁, h₁, hoff, le_rfl⟩
  obtain ⟨ρs, hρs, hmax⟩ := Set.exists_max_image S (offScore g) hfin hne
  refine ⟨ρs, hρs.1, hρs.2.1, lt_of_lt_of_le hpos hρs.2.2, fun ρ hρ hρoff => ?_⟩
  by_cases h : offScore g ρ₁ ≤ offScore g ρ
  · exact hmax ρ ⟨hρ, hρoff, h⟩
  · push_neg at h
    exact h.le.trans hρs.2.2

/-- The plateau, composed: for any off-line zero there is a width and a dominant off-line zero. -/
theorem plateau_dominant (Z : Zeta23.ZeroConfig) (F : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (ρ₁ : ℂ) (h₁ : ρ₁ ∈ Z.carrier)
    (hoff : ρ₁.re ≠ 1 / 2) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ ρs ∈ Z.carrier, ρs.re ≠ 1 / 2 ∧ 0 < offScore (plateau F L hF0 hF1 hL) ρs ∧
      ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → offScore (plateau F L hF0 hF1 hL) ρ ≤ offScore (plateau F L hF0 hF1 hL) ρs := by
  obtain ⟨L₀, hL₀, hne⟩ := base_nonzero_at F hF0 hF1 (Zeta23.gammaOf ρ₁)
  refine ⟨L₀, hL₀, ?_⟩
  have h4 : ContDiff ℝ 4 (plateau F L₀ hF0 hF1 hL₀) := by
    have := plateau_contDiff F L₀ hF0 hF1 hL₀ 4
    exact_mod_cast this
  exact dominant_exists Z h4 (plateau_support_Icc F L₀ hF0 hF1 hL₀) hL₀.le ρ₁ h₁ hoff
    (norm_pos_iff.mpr (hne L₀ hL₀ le_rfl))

/-- The off-line zeros of the maximal score `M`. -/
def tieSet (Z : Zeta23.ZeroConfig) (g : ℝ → ℝ) (M : ℝ) : Set ℂ := {ρ | ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ offScore g ρ = M}

/-- The on-line zeros of score at least `M`. -/
def killSet (Z : Zeta23.ZeroConfig) (g : ℝ → ℝ) (M : ℝ) : Set ℂ := {ρ | ρ ∈ Z.carrier ∧ ρ.re = 1 / 2 ∧ M ≤ offScore g ρ}

theorem tieSet_finite (Z : Zeta23.ZeroConfig) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ 4 g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) {M : ℝ} (hM : 0 < M) : (tieSet Z g M).Finite :=
  (off_finite_above Z hg hs hL M hM).subset (fun ρ hρ => ⟨hρ.1, le_of_eq hρ.2.2.symm⟩)

theorem killSet_finite (Z : Zeta23.ZeroConfig) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ 4 g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) {M : ℝ} (hM : 0 < M) : (killSet Z g M).Finite :=
  (off_finite_above Z hg hs hL M hM).subset (fun ρ hρ => ⟨hρ.1, hρ.2.2⟩)

theorem tieSet_nonempty (Z : Zeta23.ZeroConfig) (g : ℝ → ℝ) (ρs : ℂ) (h : ρs ∈ Z.carrier) (hoff : ρs.re ≠ 1 / 2) :
    (tieSet Z g (offScore g ρs)).Nonempty := ⟨ρs, h, hoff, rfl⟩

/-- **Stated, not proved (the act after):** distinct representatives of `tieSet` have distinct nonreal squares. Its
nonreal half needs `Im rho ≠ 0` as well as the off-line `delta ≠ 0`: `(gamma - i delta)^2` is real when `gamma = 0`. -/
def nodes_distinct_nonreal (Z : Zeta23.ZeroConfig) (g : ℝ → ℝ) (M : ℝ) : Prop :=
  (∀ ρ ∈ tieSet Z g M, ((Zeta23.gammaOf ρ) ^ 2).im ≠ 0) ∧
    ∀ ρ ∈ tieSet Z g M, ∀ ρ' ∈ tieSet Z g M, (Zeta23.gammaOf ρ) ^ 2 = (Zeta23.gammaOf ρ') ^ 2 → ρ' = ρ ∨ ρ' = 1 - ρ

/-! ### L6 -- the interpolant -/

/-- **L6:** over a conjugation-closed finite node set, every conjugation-symmetric target has a REAL interpolating
polynomial of degree below the number of nodes, with coefficients bounded by a constant depending only on the nodes
once the targets have modulus at most 1. Pure algebra; consumes nothing from Zeta23. -/
theorem real_even_interpolant (s : Finset ℂ) (hconj : ∀ w ∈ s, conj w ∈ s) :
    ∃ C : ℝ, ∀ r : ℂ → ℂ, (∀ w ∈ s, r (conj w) = conj (r w)) → (∀ w ∈ s, ‖r w‖ ≤ 1) →
      ∃ Q : Polynomial ℝ, (∀ w ∈ s, (Q.map (algebraMap ℝ ℂ)).eval w = r w) ∧ Q.degree < s.card ∧
        ∀ j, |Q.coeff j| ≤ C := by
  have hinj : Set.InjOn (id : ℂ → ℂ) s := Set.injOn_id _
  refine ⟨∑ j ∈ Finset.range s.card, ∑ i ∈ s, ‖(Lagrange.basis s id i).coeff j‖, fun r hr hr1 => ?_⟩
  set P := Lagrange.interpolate s id r with hP
  have hdeg : P.degree < s.card := Lagrange.degree_interpolate_lt r hinj
  have heval : ∀ w ∈ s, P.eval w = r w := fun w hw => Lagrange.eval_interpolate_at_node r hinj hw
  -- P has real coefficients: its conjugate interpolates the same data
  have hconjP : P.map (starRingEnd ℂ) = P := by
    rw [hP]
    apply Lagrange.eq_interpolate_of_eval_eq r hinj
    · rw [Polynomial.degree_map]
      exact hdeg
    · intro w hw
      rw [Polynomial.eval_map, show (id w : ℂ) = (starRingEnd ℂ) ((starRingEnd ℂ) w) from (Complex.conj_conj w).symm,
        Polynomial.eval₂_at_apply, heval (conj w) (hconj w hw), hr w hw, Complex.conj_conj]
  have hreal : ∀ n, P.coeff n ∈ Set.range (algebraMap ℝ ℂ) := by
    intro n
    have h := congrArg (fun q => Polynomial.coeff q n) hconjP
    simp only [Polynomial.coeff_map] at h
    refine ⟨(P.coeff n).re, ?_⟩
    rw [Complex.conj_eq_iff_re] at h
    rw [← h]
    rfl
  obtain ⟨Q, hQ⟩ := (Polynomial.lifts_iff_coeff_lifts P).mpr hreal
  rw [Polynomial.coe_mapRingHom] at hQ
  refine ⟨Q, fun w hw => by rw [hQ]; exact heval w hw, ?_, ?_⟩
  · rw [← Polynomial.degree_map Q (algebraMap ℝ ℂ), hQ]
    exact hdeg
  · intro j
    have hc : P.coeff j = (Q.coeff j : ℂ) := by rw [← hQ, Polynomial.coeff_map]; rfl
    have habs : |Q.coeff j| = ‖P.coeff j‖ := by rw [hc, Complex.norm_real, Real.norm_eq_abs]
    rw [habs]
    have hsum : P.coeff j = ∑ i ∈ s, r i * (Lagrange.basis s id i).coeff j := by
      rw [hP, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
      exact Finset.sum_congr rfl (fun i _ => Polynomial.coeff_C_mul _)
    have hb : ‖P.coeff j‖ ≤ ∑ i ∈ s, ‖(Lagrange.basis s id i).coeff j‖ := by
      rw [hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hr1 i hi)
    have hnn : ∀ j', 0 ≤ ∑ i ∈ s, ‖(Lagrange.basis s id i).coeff j'‖ :=
      fun j' => Finset.sum_nonneg (fun i _ => norm_nonneg _)
    by_cases hj : j < s.card
    · exact hb.trans (Finset.single_le_sum (fun j' _ => hnn j') (Finset.mem_range.mpr hj))
    · have hz : P.coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le hdeg (by exact_mod_cast (not_lt.mp hj))
      rw [hz, norm_zero]
      exact Finset.sum_nonneg (fun j' _ => hnn j')

/-! ### The seam of (R143)(4), probed -/

/-- **RH on the kernel's configuration:** every zero of the open-strip configuration lies on the line. -/
def rh_strip : Prop := ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ.re = 1 / 2

theorem rh_imp_rh_strip : RiemannHypothesis → rh_strip := by
  intro hRH ρ hρ
  have hρ' : Zeta23.IsNontrivialZero ρ := by
    rw [Zeta23.zetaZeroConfig_carrier] at hρ
    exact hρ
  exact Zeta23.RH_implies_on_line hRH hρ'

/-- **The seam, a Prop, NOT PROVED:** from the strip form to Mathlib's RH. It needs every Mathlib-nontrivial zero in the
open strip: the right half-plane is Mathlib's `riemannZeta_ne_zero_of_one_le_re`; the left half-plane (zeros with
`re <= 0` are the trivial zeros) is ABSENT from Mathlib at this pin by name. -/
def rh_strip_imp_rh : Prop := rh_strip → RiemannHypothesis

end B321
end SIDEExplicitFormula
