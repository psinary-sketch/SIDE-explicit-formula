/-
SIDE-explicit-formula -- SIDEExplicitFormula/PowerLimit.lean
THIS PROGRAMME'S WORK (act b534, ruling (R144); W-ORD-WEIL-CONVERSE's f4, the power-pwWindow route, act two of two) --
NOT VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SEAT'S CHOICE UNDER THE FERRY: a second module importing PowerWindow. PowerWindow.lean is not continued; a
comment-only note is appended there after `nodes_distinct_nonreal`, which stays as written, (R144)(2).

THE POWER-WINDOW ROUTE TO f4, ITS SECOND HALF (L7-L8 of (R144)). For a real pwWindow `h` the zero term of `weilTest h h`
is `h^(z) h^(-z)` (L7a, `zero_term_real`). A real polynomial of the derivative of every order acts on transforms as
`P(-iz)` (L7b, `paperFT_polyOpFull`); on the `j`-th power of an even base the term at a zero is
`P(w) P(-w) g0^(z)^(2^(j+1))`, `w = -(rho - 1/2)` (L7c, `kWindow_term`). The interpolation variable is
`v = (rho - 1/2)^2`, whose fibres are `{rho, 1 - rho}` by real algebra (`nodes_distinct`); the polynomial
`P(w) = S(w^2) K(w^2) (1 + c w)` kills the on-line zeros of maximal score through `K`, turns a real tie node negative
through `1 + c w`, and sets every other tie node's phase through `S`, interpolated by b533's `real_even_interpolant`
(L7d, `coeffs_exist`, `tie_term_neg`). The rest, divided by `M^(2^(j+1))`, tends to 0 by Tannery's theorem under a
dominant made summable by the kernel's local count (L7e, `dominant_summable`, `rest_tendsto_zero`), so for some `j`
the zero side has negative real part (`zeroSide_eventually_neg`), and with b321's identity `h2_sign` fails at every
off-line zero: `h2_sign ↔ rh_strip` (L8). The seam `rh_strip_imp_rh` stays a Prop; `h2_sign -> RiemannHypothesis`
is compiled FROM it (`h2_sign_imp_rh_of_seam`). Nothing here proves or assumes the seam.
-/
import SIDEExplicitFormula.PowerWindow
import Mathlib.Analysis.Normed.Group.Tannery

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### L7a -- the zero term of a real window -/

/-- For every real `g`: `conj (g^(conj z)) = g^(-z)`. -/
theorem paperFT_conj_of_real (g : ℝ → ℝ) (z : ℂ) :
    conj (Zeta23.paperFT (phiC g) (conj z)) = Zeta23.paperFT (phiC g) (-z) := by
  rw [paperFT_ofReal_conj g (conj z), Complex.conj_conj]

/-- For an even real `g`: `g^(-z) = g^(z)`. -/
theorem paperFT_neg_of_even {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (z : ℂ) :
    Zeta23.paperFT (phiC g) (-z) = Zeta23.paperFT (phiC g) z :=
  phiC_FT_neg hev z

/-- **L7a:** for a real continuous compactly supported `g`, `(weilTest g g)^(z) = g^(z) g^(-z)`. -/
theorem zero_term_real {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) (z : ℂ) :
    Zeta23.paperFT (Zeta23.EF.weilTest (phiC g) (phiC g)) z =
      Zeta23.paperFT (phiC g) z * Zeta23.paperFT (phiC g) (-z) := by
  have hc' : Continuous (phiC g) := Complex.continuous_ofReal.comp hc
  have hs' : HasCompactSupport (phiC g) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  rw [Zeta23.EF.paperFT_weilTest hc' hc' hs' hs' z, paperFT_conj_of_real g z]

/-! ### L7b -- the full operator -/

/-- `SUM_p a_p D^p g`, every order. -/
def polyOpFull (a : List ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun u => ∑ p ∈ Finset.range a.length, polyCoef a p * iteratedDeriv p g u

/-- `SUM_p a_p w^p`. -/
def polyEvalFull (a : List ℝ) (w : ℂ) : ℂ := ∑ p ∈ Finset.range a.length, (polyCoef a p : ℂ) * w ^ p

/-- **L7b:** `(polyOpFull a g)^(z) = (SUM_p a_p (-(i z))^p) g^(z)`. -/
theorem paperFT_polyOpFull (a : List ℝ) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ a.length g)
    (hs : Function.support g ⊆ Set.Icc (-L) L) (z : ℂ) :
    Zeta23.paperFT (phiC (polyOpFull a g)) z = polyEvalFull a (-(I * z)) * Zeta23.paperFT (phiC g) z := by
  have hle : ∀ p ∈ Finset.range a.length, ((p : ℕ) : WithTop ℕ∞) ≤ ((a.length : ℕ) : WithTop ℕ∞) := by
    intro p hp
    have := Finset.mem_range.mp hp
    exact_mod_cast this.le
  have hc : ∀ p ∈ Finset.range a.length, Continuous (iteratedDeriv p g) :=
    fun p hp => hg.continuous_iteratedDeriv p (hle p hp)
  have hcs : ∀ p ∈ Finset.range a.length, HasCompactSupport (iteratedDeriv p g) :=
    fun p _ => hasCompactSupport_of_Icc (support_iteratedDeriv_Icc p hs)
  have key := paperFT_sum (Finset.range a.length) (fun p => polyCoef a p) (fun p => iteratedDeriv p g) hc hcs z
  beta_reduce at key
  show Zeta23.paperFT (phiC (fun u => ∑ p ∈ Finset.range a.length, polyCoef a p * iteratedDeriv p g u)) z = _
  rw [key, polyEvalFull, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [paperFT_iteratedDeriv p g (hg.of_le (hle p hp)) (hasCompactSupport_of_Icc hs) z]
  ring

theorem polyOpFull_support (a : List ℝ) {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    Function.support (polyOpFull a g) ⊆ Set.Icc (-L) L := by
  intro u hu
  by_contra hout
  apply hu
  unfold polyOpFull
  refine Finset.sum_eq_zero (fun p _ => ?_)
  have h0 : iteratedDeriv p g u = 0 := by
    by_contra h
    exact hout (support_iteratedDeriv_Icc p hs h)
  rw [h0, mul_zero]

theorem polyOpFull_contDiff (a : List ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyOpFull a g) := by
  unfold polyOpFull
  refine ContDiff.sum (fun p _ => ?_)
  refine contDiff_const.mul ?_
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv p hg

/-! ### L7c -- the term of the power window -/

/-- The window: the full operator applied to the `j`-th power of the base. -/
def pwWindow (a : List ℝ) (g0 : ℝ → ℝ) (j : ℕ) : ℝ → ℝ := polyOpFull a (power g0 j)

/-- Its `weilTest`. -/
def kWindow (a : List ℝ) (g0 : ℝ → ℝ) (j : ℕ) : ℝ → ℂ :=
  Zeta23.EF.weilTest (phiC (pwWindow a g0 j)) (phiC (pwWindow a g0 j))

theorem pwWindow_contDiff (a : List ℝ) {g0 : ℝ → ℝ} {L : ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0)
    (hs : Function.support g0 ⊆ Set.Icc (-L) L) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pwWindow a g0 j) :=
  polyOpFull_contDiff a (power_contDiff hsm hs j)

theorem pwWindow_support (a : List ℝ) {g0 : ℝ → ℝ} {L : ℝ} (hs : Function.support g0 ⊆ Set.Icc (-L) L) (j : ℕ) :
    Function.support (pwWindow a g0 j) ⊆ Set.Icc (-(2 ^ j * L)) (2 ^ j * L) :=
  polyOpFull_support a (power_support hs j)

/-- **L7c:** the power window's `weilTest` is in classK. -/
theorem kWindow_classK (a : List ℝ) {g0 : ℝ → ℝ} {L : ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0)
    (hs : Function.support g0 ⊆ Set.Icc (-L) L) (j : ℕ) : classK (kWindow a g0 j) :=
  classK_of_real_even ((pwWindow_contDiff a hsm hs j).of_le (WithTop.coe_le_coe.mpr le_top))
    (hasCompactSupport_of_Icc (pwWindow_support a hs j))

/-- **L7c:** its transform at `z` is `P(-iz) P(iz) g0^(z)^(2^(j+1))`. -/
theorem kWindow_term (a : List ℝ) {g0 : ℝ → ℝ} {L : ℝ} (hev : ∀ x, g0 (-x) = g0 x)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0) (hs : Function.support g0 ⊆ Set.Icc (-L) L) (j : ℕ) (z : ℂ) :
    Zeta23.paperFT (kWindow a g0 j) z =
      polyEvalFull a (-(I * z)) * polyEvalFull a (I * z) * (Zeta23.paperFT (phiC g0) z) ^ (2 ^ (j + 1)) := by
  have hpw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (power g0 j) := power_contDiff hsm hs j
  have hw := pwWindow_contDiff a hsm hs j
  unfold kWindow
  rw [zero_term_real hw.continuous (hasCompactSupport_of_Icc (pwWindow_support a hs j)) z]
  unfold pwWindow
  rw [paperFT_polyOpFull a (hpw.of_le (by exact_mod_cast le_top)) (power_support hs j) z,
    paperFT_polyOpFull a (hpw.of_le (by exact_mod_cast le_top)) (power_support hs j) (-z),
    paperFT_power hev hsm hs z j, paperFT_power hev hsm hs (-z) j, paperFT_neg_of_even hev z]
  have e : -(I * -z) = I * z := by ring
  rw [e, show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
  ring

/-! ### L7d -- the interpolation variable, the reflection, the nodes -/

/-- `v_rho = (rho - 1/2)^2`. -/
def vOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) ^ 2

/-- `w_rho = -(i gammaOf rho) = -(rho - 1/2)`. -/
def wOf (ρ : ℂ) : ℂ := -(I * Zeta23.gammaOf ρ)

theorem wOf_eq (ρ : ℂ) : wOf ρ = -(ρ - 1 / 2) := by
  unfold wOf Zeta23.gammaOf
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ Complex.I_ne_zero]

theorem wOf_sq (ρ : ℂ) : wOf ρ ^ 2 = vOf ρ := by
  rw [wOf_eq]
  unfold vOf
  ring

theorem norm_wOf (ρ : ℂ) : ‖wOf ρ‖ = ‖Zeta23.gammaOf ρ‖ := by
  unfold wOf
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul]

theorem gammaOf_sq (ρ : ℂ) : Zeta23.gammaOf ρ ^ 2 = -vOf ρ := by
  have h := wOf_sq ρ
  unfold wOf at h
  rw [neg_sq, mul_pow, Complex.I_sq] at h
  linear_combination -h

theorem vOf_re (ρ : ℂ) : (vOf ρ).re = (ρ.re - 1 / 2) ^ 2 - ρ.im ^ 2 := by
  unfold vOf
  rw [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im]
  ring

theorem vOf_im (ρ : ℂ) : (vOf ρ).im = 2 * (ρ.re - 1 / 2) * ρ.im := by
  unfold vOf
  rw [sq, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im]
  ring

/-- Equal `v` forces `rho' ∈ {rho, 1 - rho}`, by real algebra; no non-reality is used. -/
theorem v_eq_iff (ρ ρ' : ℂ) (h : vOf ρ = vOf ρ') : ρ' = ρ ∨ ρ' = 1 - ρ := by
  unfold vOf at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h.symm with h1 | h1
  · left
    linear_combination h1
  · right
    linear_combination h1

/-- **L7d, `nodes_distinct` (R144)(2), PROVED:** on the tie set, equal `v` forces `rho' = rho` or `rho' = 1 - rho`.
It supersedes b533's `nodes_distinct_nonreal`, which stays as written and unproved. -/
theorem nodes_distinct (Z : Zeta23.ZeroConfig) (g : ℝ → ℝ) (M : ℝ) :
    ∀ ρ ∈ tieSet Z g M, ∀ ρ' ∈ tieSet Z g M, vOf ρ = vOf ρ' → ρ' = ρ ∨ ρ' = 1 - ρ :=
  fun ρ _ ρ' _ h => v_eq_iff ρ ρ' h

theorem reflect_re (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re := by
  rw [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]

theorem reflect_im (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im := by
  rw [Zeta23.reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]
  ring

theorem gammaOf_reflect (ρ : ℂ) : Zeta23.gammaOf (Zeta23.reflect ρ) = conj (Zeta23.gammaOf ρ) := by
  apply Complex.ext
  · rw [gammaOf_re', Complex.conj_re, gammaOf_re', reflect_im]
  · rw [gammaOf_im', Complex.conj_im, gammaOf_im', reflect_re]
    ring

theorem vOf_reflect (ρ : ℂ) : vOf (Zeta23.reflect ρ) = conj (vOf ρ) := by
  unfold vOf
  rw [Zeta23.reflect, map_pow, map_sub, map_div₀, map_one, map_ofNat]
  ring

theorem paperFT_conj_eq {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (z : ℂ) :
    Zeta23.paperFT (phiC g) (conj z) = conj (Zeta23.paperFT (phiC g) z) := by
  rw [← paperFT_conj_of_real_even hev z, Complex.conj_conj]

theorem offScore_reflect {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) (ρ : ℂ) :
    offScore g (Zeta23.reflect ρ) = offScore g ρ := by
  unfold offScore
  rw [gammaOf_reflect, paperFT_conj_eq hev, Complex.norm_conj]

theorem paperFT_of_sq_eq {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) {z z' : ℂ} (h : z' ^ 2 = z ^ 2) :
    Zeta23.paperFT (phiC g) z' = Zeta23.paperFT (phiC g) z := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · rw [h1]
  · rw [h1, paperFT_neg_of_even hev]

/-- The tie set is reflection-closed: the carrier's closure is the `ZeroConfig` field `reflect_mem`
(for `zetaZeroConfig`, `Zeta23.zeta_reflect_zero` through `Zeta23.zetaSeam`). -/
theorem tie_reflect (Z : Zeta23.ZeroConfig) {g : ℝ → ℝ} (hev : ∀ x, g (-x) = g x) {M : ℝ} {ρ : ℂ}
    (h : ρ ∈ tieSet Z g M) : Zeta23.reflect ρ ∈ tieSet Z g M := by
  refine ⟨Z.reflect_mem ρ h.1, ?_, ?_⟩
  · rw [reflect_re]
    intro h'
    apply h.2.1
    linarith
  · rw [offScore_reflect hev]
    exact h.2.2

/-! ### L7d -- the setup -/

/-- The fixed data of L7d: a real even smooth base supported in `[-L, L]`, and the dominant off-line score `M`. -/
structure PWSetup (Z : Zeta23.ZeroConfig) (g0 : ℝ → ℝ) (L M : ℝ) : Prop where
  hev : ∀ x, g0 (-x) = g0 x
  hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0
  hs : Function.support g0 ⊆ Set.Icc (-L) L
  hL : 0 ≤ L
  hM : 0 < M
  hdom : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → offScore g0 ρ ≤ M

variable {Z : Zeta23.ZeroConfig} {g0 : ℝ → ℝ} {L M : ℝ}

theorem PWSetup.c4 (H : PWSetup Z g0 L M) : ContDiff ℝ 4 g0 := H.hsm.of_le (WithTop.coe_le_coe.mpr le_top)

theorem PWSetup.tfin (H : PWSetup Z g0 L M) : (tieSet Z g0 M).Finite := tieSet_finite Z H.c4 H.hs H.hL H.hM

theorem PWSetup.kfin (H : PWSetup Z g0 L M) : (killSet Z g0 M).Finite := killSet_finite Z H.c4 H.hs H.hL H.hM

/-- `T`, as a Finset. -/
def TF (H : PWSetup Z g0 L M) : Finset ℂ := H.tfin.toFinset

/-- `Kset`, as a Finset. -/
def KF (H : PWSetup Z g0 L M) : Finset ℂ := H.kfin.toFinset

/-- `X`: the kill nodes, real and `<= 0`. -/
def Xr (H : PWSetup Z g0 L M) : Finset ℝ := (KF H).image (fun ρ => (vOf ρ).re)

/-- `K(v) = PROD_{x in X} (v - x)`, a real polynomial. -/
def Kp (H : PWSetup Z g0 L M) : Polynomial ℝ := ∏ x ∈ Xr H, (Polynomial.X - Polynomial.C x)

/-- `c = 1 + SUM_{rho in T} 1 / |Re rho - 1/2|`, so `c |Re rho - 1/2| > 1` on `T`. -/
def cE (H : PWSetup Z g0 L M) : ℝ := 1 + ∑ ρ ∈ TF H, 1 / |ρ.re - 1 / 2|

/-- `E(w) = 1 + c w`. -/
def Ep (H : PWSetup Z g0 L M) : Polynomial ℝ := 1 + Polynomial.C (cE H) * Polynomial.X

/-- `V = T.image v`, the interpolation nodes. -/
def VF (H : PWSetup Z g0 L M) : Finset ℂ := (TF H).image vOf

theorem mem_TF (H : PWSetup Z g0 L M) {ρ : ℂ} : ρ ∈ TF H ↔ ρ ∈ tieSet Z g0 M := H.tfin.mem_toFinset

theorem mem_KF (H : PWSetup Z g0 L M) {ρ : ℂ} : ρ ∈ KF H ↔ ρ ∈ killSet Z g0 M := H.kfin.mem_toFinset

theorem cE_pos (H : PWSetup Z g0 L M) : 0 < cE H := by
  unfold cE
  have : 0 ≤ ∑ ρ ∈ TF H, 1 / |ρ.re - 1 / 2| := Finset.sum_nonneg (fun i _ => by positivity)
  linarith

theorem cE_big (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) : 1 < cE H * |ρ.re - 1 / 2| := by
  have ha : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hρ.2.1)
  have hle : 1 / |ρ.re - 1 / 2| ≤ ∑ ρ' ∈ TF H, 1 / |ρ'.re - 1 / 2| :=
    Finset.single_le_sum (f := fun ρ' => 1 / |ρ'.re - 1 / 2|) (fun i _ => by positivity) ((mem_TF H).mpr hρ)
  have hlt : 1 / |ρ.re - 1 / 2| < cE H := by
    unfold cE
    linarith
  calc (1 : ℝ) = 1 / |ρ.re - 1 / 2| * |ρ.re - 1 / 2| := (one_div_mul_cancel ha.ne').symm
    _ < cE H * |ρ.re - 1 / 2| := mul_lt_mul_of_pos_right hlt ha

/-! ### L7d -- evaluations of real polynomials -/

theorem aeval_real (Q : Polynomial ℝ) (x : ℝ) : Polynomial.aeval (x : ℂ) Q = ((Q.eval x : ℝ) : ℂ) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval x Q

theorem aeval_conj (Q : Polynomial ℝ) (x : ℂ) : Polynomial.aeval (conj x) Q = conj (Polynomial.aeval x Q) := by
  refine Polynomial.induction_on' Q (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, map_add, hp, hq, map_add]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
      show (algebraMap ℝ ℂ) a = (a : ℂ) from rfl, Complex.conj_ofReal]

theorem aeval_X_sq_comp (Q : Polynomial ℝ) (w : ℂ) :
    Polynomial.aeval w (Q.comp (Polynomial.X ^ 2)) = Polynomial.aeval (w ^ 2) Q := by
  rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X]

/-- `P(w) = S(w^2) K(w^2) E(w)`. -/
def Pof (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) : Polynomial ℝ :=
  Q.comp (Polynomial.X ^ 2) * (Kp H).comp (Polynomial.X ^ 2) * Ep H

theorem aeval_Ep (H : PWSetup Z g0 L M) (w : ℂ) : Polynomial.aeval w (Ep H) = 1 + (cE H : ℂ) * w := by
  unfold Ep
  rw [map_add, map_one, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  try rfl

theorem Ep_prod (H : PWSetup Z g0 L M) (w : ℂ) :
    Polynomial.aeval w (Ep H) * Polynomial.aeval (-w) (Ep H) = 1 - (cE H : ℂ) ^ 2 * w ^ 2 := by
  rw [aeval_Ep, aeval_Ep]
  ring

theorem Pof_eval (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (w : ℂ) :
    Polynomial.aeval w (Pof H Q) =
      Polynomial.aeval (w ^ 2) Q * Polynomial.aeval (w ^ 2) (Kp H) * Polynomial.aeval w (Ep H) := by
  unfold Pof
  rw [map_mul, map_mul, aeval_X_sq_comp, aeval_X_sq_comp]

theorem Pof_prod (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (w : ℂ) :
    Polynomial.aeval w (Pof H Q) * Polynomial.aeval (-w) (Pof H Q) =
      (Polynomial.aeval (w ^ 2) Q) ^ 2 * (Polynomial.aeval (w ^ 2) (Kp H)) ^ 2 * (1 - (cE H : ℂ) ^ 2 * w ^ 2) := by
  rw [Pof_eval, Pof_eval, neg_sq, ← Ep_prod H w]
  ring

/-- The coefficient list `a` of a real polynomial, `a_p = P.coeff p`. -/
def coeffList (P : Polynomial ℝ) : List ℝ := (List.range (P.natDegree + 1)).map P.coeff

theorem polyEvalFull_coeffList (P : Polynomial ℝ) (w : ℂ) :
    polyEvalFull (coeffList P) w = Polynomial.aeval w P := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold polyEvalFull
  have hlen : (coeffList P).length = P.natDegree + 1 := by
    unfold coeffList
    rw [List.length_map, List.length_range]
  rw [hlen]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' : p < (coeffList P).length := by
    rw [hlen]
    exact Finset.mem_range.mp hp
  rw [polyCoef, List.getD_eq_getElem _ _ hp', Complex.real_smul]
  simp [coeffList]

/-! ### L7d -- the kill factor and the sign factor -/

theorem vOf_real_of_on (ρ : ℂ) (h : ρ.re = 1 / 2) : (((vOf ρ).re : ℝ) : ℂ) = vOf ρ := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, vOf_im, h]
    ring

/-- `K` vanishes at every kill node. -/
theorem Kp_kill (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ killSet Z g0 M) :
    Polynomial.aeval (vOf ρ) (Kp H) = 0 := by
  unfold Kp
  rw [map_prod]
  apply Finset.prod_eq_zero (i := (vOf ρ).re) (Finset.mem_image_of_mem (fun ρ => (vOf ρ).re) ((mem_KF H).mpr hρ))
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero]
  exact (vOf_real_of_on ρ hρ.2.1).symm

/-- `K(v_rho) ≠ 0` on `T`: a tie node is not real, or is real and positive; a kill node is real and `<= 0`
(`v_rho = 0` would need `Re rho = 1/2`). -/
theorem Kp_tie_ne (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) :
    Polynomial.aeval (vOf ρ) (Kp H) ≠ 0 := by
  unfold Kp
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro x hx
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hx
  have hk : ρ' ∈ killSet Z g0 M := (mem_KF H).mp hρ'
  intro heq
  have h1 : vOf ρ = (((vOf ρ').re : ℝ) : ℂ) := sub_eq_zero.mp heq
  have him := congrArg Complex.im h1
  have hre := congrArg Complex.re h1
  rw [Complex.ofReal_im, vOf_im] at him
  rw [Complex.ofReal_re, vOf_re, vOf_re, hk.2.1] at hre
  have ha : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ.2.1
  have hb : ρ.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd (by linarith : ρ.re - 1 / 2 = 0) ha
    · exact h
  rw [hb] at hre
  have hpos : 0 < (ρ.re - 1 / 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha))
  nlinarith [sq_nonneg ρ'.im]

/-- `1 - c^2 v_rho ≠ 0` on `T`. -/
theorem Efac_ne (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) : (1 - (cE H : ℂ) ^ 2 * vOf ρ) ≠ 0 := by
  intro h0
  have e : (1 - (cE H : ℂ) ^ 2 * vOf ρ) = 1 - ((cE H ^ 2 : ℝ) : ℂ) * vOf ρ := by rw [Complex.ofReal_pow]
  rw [e] at h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.zero_re, vOf_re] at hre
  rw [Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, Complex.zero_im, vOf_im] at him
  have hc := cE_pos H
  have hbig := cE_big H hρ
  have ha : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ.2.1
  have hc2 : 0 < cE H ^ 2 := by positivity
  have hb : ρ.im = 0 := by
    have h2 : cE H ^ 2 * (2 * (ρ.re - 1 / 2) * ρ.im) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (by linarith : ρ.re - 1 / 2 = 0) ha
      · exact h'
  rw [hb] at hre
  have h3 : (cE H * |ρ.re - 1 / 2|) ^ 2 = cE H ^ 2 * (ρ.re - 1 / 2) ^ 2 := by rw [mul_pow, sq_abs]
  have h4 : 1 < (cE H * |ρ.re - 1 / 2|) ^ 2 := by nlinarith
  rw [h3] at h4
  nlinarith

theorem gHat_ne (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) :
    Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ) ≠ 0 := by
  intro h
  have h2 : offScore g0 ρ = M := hρ.2.2
  unfold offScore at h2
  rw [h, norm_zero] at h2
  linarith [H.hM]

/-- `X_{rho,j} = K(v)^2 (1 - c^2 v) g0^(gammaOf rho)^(2^(j+1))`. -/
def Xval (H : PWSetup Z g0 L M) (j : ℕ) (ρ : ℂ) : ℂ :=
  (Polynomial.aeval (vOf ρ) (Kp H)) ^ 2 * (1 - (cE H : ℂ) ^ 2 * vOf ρ) *
    (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)) ^ (2 ^ (j + 1))

theorem Xval_ne (H : PWSetup Z g0 L M) (j : ℕ) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) : Xval H j ρ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Kp_tie_ne H hρ)) (Efac_ne H hρ)) (pow_ne_zero _ (gHat_ne H hρ))

/-- `N_rho = |K(v)^2 (1 - c^2 v)|`, independent of `j`. -/
def Nf (H : PWSetup Z g0 L M) (ρ : ℂ) : ℝ := ‖(Polynomial.aeval (vOf ρ) (Kp H)) ^ 2 * (1 - (cE H : ℂ) ^ 2 * vOf ρ)‖

theorem Xval_norm (H : PWSetup Z g0 L M) (j : ℕ) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) :
    ‖Xval H j ρ‖ = Nf H ρ * M ^ (2 ^ (j + 1)) := by
  unfold Xval Nf
  rw [norm_mul, norm_pow]
  have h2 : ‖Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)‖ = M := hρ.2.2
  rw [h2]

theorem Nf_pos (H : PWSetup Z g0 L M) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) : 0 < Nf H ρ :=
  norm_pos_iff.mpr (mul_ne_zero (pow_ne_zero _ (Kp_tie_ne H hρ)) (Efac_ne H hρ))

/-- At a REAL tie node (`Im rho = 0`), `X` is real and negative: no phase to set. -/
theorem Xval_real_neg (H : PWSetup Z g0 L M) (j : ℕ) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) (hρim : ρ.im = 0) :
    Xval H j ρ = -(‖Xval H j ρ‖ : ℂ) := by
  have ha : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ.2.1
  have hv : vOf ρ = (((ρ.re - 1 / 2) ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [vOf_re, hρim, Complex.ofReal_re]
      ring
    · rw [vOf_im, hρim, Complex.ofReal_im]
      ring
  have hK : Polynomial.aeval (vOf ρ) (Kp H) = (((Kp H).eval ((ρ.re - 1 / 2) ^ 2) : ℝ) : ℂ) := by
    rw [hv]
    exact aeval_real _ _
  have hz : conj (Zeta23.gammaOf ρ) = -Zeta23.gammaOf ρ := by
    apply Complex.ext
    · rw [Complex.conj_re, Complex.neg_re, gammaOf_re', hρim, neg_zero]
    · rw [Complex.conj_im, Complex.neg_im]
  have hpr : conj (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)) = Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ) := by
    rw [← paperFT_conj_eq H.hev, hz, paperFT_neg_of_even H.hev]
  have hp : Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ) =
      (((Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)).re : ℝ) : ℂ) :=
    (Complex.conj_eq_iff_re.mp hpr).symm
  have hk0 : (Kp H).eval ((ρ.re - 1 / 2) ^ 2) ≠ 0 := by
    intro h0
    apply Kp_tie_ne H hρ
    rw [hK, h0, Complex.ofReal_zero]
  have hp0 : (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)).re ≠ 0 := by
    intro h0
    apply gHat_ne H hρ
    rw [hp, h0, Complex.ofReal_zero]
  have he : 1 - cE H ^ 2 * (ρ.re - 1 / 2) ^ 2 < 0 := by
    have hbig := cE_big H hρ
    have h3 : (cE H * |ρ.re - 1 / 2|) ^ 2 = cE H ^ 2 * (ρ.re - 1 / 2) ^ 2 := by rw [mul_pow, sq_abs]
    nlinarith
  have hq : 0 < (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)).re ^ (2 ^ (j + 1)) :=
    Even.pow_pos (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩) hp0
  have hk2 : 0 < ((Kp H).eval ((ρ.re - 1 / 2) ^ 2)) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk0))
  have hr : ((Kp H).eval ((ρ.re - 1 / 2) ^ 2)) ^ 2 * (1 - cE H ^ 2 * (ρ.re - 1 / 2) ^ 2) *
      (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)).re ^ (2 ^ (j + 1)) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hk2 he) hq
  have hX : Xval H j ρ = ((((Kp H).eval ((ρ.re - 1 / 2) ^ 2)) ^ 2 * (1 - cE H ^ 2 * (ρ.re - 1 / 2) ^ 2) *
      (Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)).re ^ (2 ^ (j + 1)) : ℝ) : ℂ) := by
    unfold Xval
    rw [hK, hv]
    conv_lhs => rw [hp]
    push_cast
    ring
  rw [hX, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr, Complex.ofReal_neg, neg_neg]

/-! ### L7d -- the node values as functions of `v`, and the phase targets -/

open Classical in
/-- A tie zero over each node of `V`. -/
def rep (H : PWSetup Z g0 L M) (v : ℂ) : ℂ :=
  if h : ∃ ρ ∈ tieSet Z g0 M, vOf ρ = v then Classical.choose h else 0

theorem rep_spec (H : PWSetup Z g0 L M) {v : ℂ} (hv : v ∈ VF H) : rep H v ∈ tieSet Z g0 M ∧ vOf (rep H v) = v := by
  have h : ∃ ρ ∈ tieSet Z g0 M, vOf ρ = v := by
    unfold VF at hv
    obtain ⟨ρ, hρ, hv'⟩ := Finset.mem_image.mp hv
    exact ⟨ρ, (mem_TF H).mp hρ, hv'⟩
  unfold rep
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- `X` read at a node of `V`. -/
def XV (H : PWSetup Z g0 L M) (j : ℕ) (v : ℂ) : ℂ := Xval H j (rep H v)

theorem XV_node (H : PWSetup Z g0 L M) (j : ℕ) {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) : XV H j (vOf ρ) = Xval H j ρ := by
  have hv : vOf ρ ∈ VF H := by
    unfold VF
    exact Finset.mem_image_of_mem _ ((mem_TF H).mpr hρ)
  obtain ⟨-, hr⟩ := rep_spec H hv
  have hg : Zeta23.paperFT (phiC g0) (Zeta23.gammaOf (rep H (vOf ρ))) = Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ) :=
    paperFT_of_sq_eq H.hev (by rw [gammaOf_sq, gammaOf_sq, hr])
  unfold XV Xval
  rw [hr, hg]

/-- At the conjugate node the value is the conjugate: the closure is the reflection `rho ↦ 1 - conj rho`. -/
theorem XV_conj (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : XV H j (conj v) = conj (XV H j v) := by
  obtain ⟨hmem, hr⟩ := rep_spec H hv
  have h1 : conj v = vOf (Zeta23.reflect (rep H v)) := by rw [vOf_reflect, hr]
  rw [h1, XV_node H j (tie_reflect Z H.hev hmem)]
  unfold XV Xval
  rw [vOf_reflect, gammaOf_reflect, paperFT_conj_eq H.hev, aeval_conj]
  simp only [map_mul, map_pow, map_sub, map_one, Complex.conj_ofReal]

/-- The principal square root, `exp (log y / 2)`. -/
def sqrtC (y : ℂ) : ℂ := Complex.exp (Complex.log y / 2)

theorem sqrtC_sq {y : ℂ} (hy : y ≠ 0) : sqrtC y ^ 2 = y := by
  unfold sqrtC
  rw [← Complex.exp_nat_mul]
  have h2 : ((2 : ℕ) : ℂ) * (Complex.log y / 2) = Complex.log y := by
    push_cast
    ring
  rw [h2, Complex.exp_log hy]

theorem norm_sqrtC {y : ℂ} (hy : ‖y‖ = 1) : ‖sqrtC y‖ = 1 := by
  unfold sqrtC
  rw [Complex.norm_exp, Complex.div_ofNat_re, Complex.log_re, hy, Real.log_one, zero_div, Real.exp_zero]

/-- `Y = -conj X / |X|`, of modulus one; `Y X = -|X|`. -/
def Yv (H : PWSetup Z g0 L M) (j : ℕ) (v : ℂ) : ℂ := -(conj (XV H j v)) / (‖XV H j v‖ : ℂ)

theorem XV_ne (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : XV H j v ≠ 0 :=
  Xval_ne H j (rep_spec H hv).1

theorem norm_Yv (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : ‖Yv H j v‖ = 1 := by
  unfold Yv
  rw [norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (XV_ne H j hv))]

theorem Yv_ne (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : Yv H j v ≠ 0 := by
  intro h
  have h1 := norm_Yv H j hv
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem Yv_mul (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) :
    Yv H j v * XV H j v = -(‖XV H j v‖ : ℂ) := by
  have hn : (‖XV H j v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (XV_ne H j hv)
  unfold Yv
  calc -(conj (XV H j v)) / (‖XV H j v‖ : ℂ) * XV H j v
      = -((conj (XV H j v) * XV H j v) / (‖XV H j v‖ : ℂ)) := by ring
    _ = -((‖XV H j v‖ : ℂ) ^ 2 / (‖XV H j v‖ : ℂ)) := by rw [Complex.conj_mul']
    _ = -(‖XV H j v‖ : ℂ) := by rw [sq, mul_div_assoc, div_self hn, mul_one]

theorem Yv_conj (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : Yv H j (conj v) = conj (Yv H j v) := by
  unfold Yv
  rw [XV_conj H j hv, Complex.norm_conj, map_div₀, map_neg, Complex.conj_ofReal]

/-- **The phase targets.** `1` at a real node; a square root of `Y` at a node with `Im v > 0`; the conjugate of the
square root of `conj Y` at a node with `Im v < 0` -- so the targets are conjugation-symmetric by construction. -/
def rT (H : PWSetup Z g0 L M) (j : ℕ) (v : ℂ) : ℂ :=
  if v.im = 0 then 1 else if 0 < v.im then sqrtC (Yv H j v) else conj (sqrtC (conj (Yv H j v)))

theorem rT_conj (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : rT H j (conj v) = conj (rT H j v) := by
  have hc : (conj v).im = -v.im := Complex.conj_im v
  unfold rT
  by_cases h0 : v.im = 0
  · have h0' : (conj v).im = 0 := by rw [hc, h0, neg_zero]
    rw [if_pos h0', if_pos h0, map_one]
  · have h0' : (conj v).im ≠ 0 := by
      rw [hc]
      exact neg_ne_zero.mpr h0
    rw [if_neg h0', if_neg h0]
    by_cases hp : 0 < v.im
    · have hp' : ¬ 0 < (conj v).im := by
        rw [hc]
        linarith
      rw [if_neg hp', if_pos hp, Yv_conj H j hv, Complex.conj_conj]
    · have hp' : 0 < (conj v).im := by
        rw [hc]
        have : v.im < 0 := lt_of_le_of_ne (not_lt.mp hp) h0
        linarith
      rw [if_pos hp', if_neg hp, Yv_conj H j hv, Complex.conj_conj]

theorem rT_norm (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) : ‖rT H j v‖ ≤ 1 := by
  unfold rT
  split_ifs
  · exact le_of_eq norm_one
  · exact le_of_eq (norm_sqrtC (norm_Yv H j hv))
  · refine le_of_eq ?_
    rw [Complex.norm_conj]
    exact norm_sqrtC (by rw [Complex.norm_conj]; exact norm_Yv H j hv)

theorem rT_sq_mul (H : PWSetup Z g0 L M) (j : ℕ) {v : ℂ} (hv : v ∈ VF H) (him : v.im ≠ 0) :
    rT H j v ^ 2 * XV H j v = -(‖XV H j v‖ : ℂ) := by
  unfold rT
  rw [if_neg him]
  split_ifs with hp
  · rw [sqrtC_sq (Yv_ne H j hv)]
    exact Yv_mul H j hv
  · rw [← map_pow (starRingEnd ℂ), sqrtC_sq ((map_ne_zero (starRingEnd ℂ)).mpr (Yv_ne H j hv)), Complex.conj_conj]
    exact Yv_mul H j hv

theorem VF_conj (H : PWSetup Z g0 L M) : ∀ w ∈ VF H, conj w ∈ VF H := by
  intro w hw
  obtain ⟨hmem, hr⟩ := rep_spec H hw
  unfold VF
  rw [← hr, ← vOf_reflect]
  exact Finset.mem_image_of_mem _ ((mem_TF H).mpr (tie_reflect Z H.hev hmem))

/-! ### L7d -- the polynomial bounds and the coefficients -/

theorem poly_norm_le (Q : Polynomial ℝ) {n : ℕ} {C : ℝ} (hdeg : Q.natDegree < n) (hC : ∀ i, |Q.coeff i| ≤ C)
    (x : ℂ) : ‖Polynomial.aeval x Q‖ ≤ n * C * (1 + ‖x‖) ^ n := by
  rw [Polynomial.aeval_eq_sum_range' hdeg]
  calc ‖∑ i ∈ Finset.range n, Q.coeff i • x ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖Q.coeff i • x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, C * (1 + ‖x‖) ^ n := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [norm_smul, Real.norm_eq_abs, norm_pow]
        have h1 : ‖x‖ ^ i ≤ (1 + ‖x‖) ^ i := pow_le_pow_left₀ (norm_nonneg x) (by linarith) i
        have h2 : (1 + ‖x‖) ^ i ≤ (1 + ‖x‖) ^ n :=
          pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Finset.mem_range.mp hi).le
        exact mul_le_mul (hC i) (h1.trans h2) (by positivity) ((abs_nonneg _).trans (hC i))
    _ = n * C * (1 + ‖x‖) ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem fixed_poly_bound (Q : Polynomial ℝ) :
    ∃ B : ℝ, ∃ D : ℕ, 0 ≤ B ∧ ∀ x : ℂ, ‖Polynomial.aeval x Q‖ ≤ B * (1 + ‖x‖) ^ D := by
  have hC0 : 0 ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hC : ∀ i, |Q.coeff i| ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| := by
    intro i
    by_cases hi : i < Q.natDegree + 1
    · exact Finset.single_le_sum (f := fun i => |Q.coeff i|) (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hi)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]
      exact hC0
  exact ⟨((Q.natDegree + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|, Q.natDegree + 1,
    mul_nonneg (Nat.cast_nonneg _) hC0, fun x => poly_norm_le Q (Nat.lt_succ_self _) hC x⟩

/-- **L7d, the coefficients:** there are `B, D` such that for every `j` a real polynomial `S_j` interpolating the phase
targets on `V` makes every tie term equal to `-|X|`, and `|P_j(w)| <= B (1 + |w|)^D`, `P_j = S_j(w^2) K(w^2) E(w)`. -/
theorem coeffs_exist (H : PWSetup Z g0 L M) (hne : (tieSet Z g0 M).Nonempty) :
    ∃ B : ℝ, ∃ D : ℕ, 0 ≤ B ∧ ∀ j : ℕ, ∃ Q : Polynomial ℝ,
      (∀ ρ ∈ tieSet Z g0 M, (Polynomial.aeval (vOf ρ) Q) ^ 2 * Xval H j ρ = -(‖Xval H j ρ‖ : ℂ)) ∧
      ∀ w : ℂ, ‖Polynomial.aeval w (Pof H Q)‖ ≤ B * (1 + ‖w‖) ^ D := by
  obtain ⟨CV, hCV⟩ := real_even_interpolant (VF H) (VF_conj H)
  obtain ⟨BK, DK, hBK, hK⟩ := fixed_poly_bound (Kp H)
  obtain ⟨BE, DE, hBE, hE⟩ := fixed_poly_bound (Ep H)
  obtain ⟨ρ0, hρ0⟩ := hne
  have hn : 0 < (VF H).card := Finset.card_pos.mpr ⟨vOf ρ0, by
    unfold VF
    exact Finset.mem_image_of_mem _ ((mem_TF H).mpr hρ0)⟩
  refine ⟨(VF H).card * max CV 0 * BK * BE, 2 * (VF H).card + 2 * DK + DE,
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) hBK) hBE, fun j => ?_⟩
  obtain ⟨Q, hQe, hQd, hQc⟩ := hCV (rT H j) (fun w hw => rT_conj H j hw) (fun w hw => rT_norm H j hw)
  refine ⟨Q, fun ρ hρ => ?_, fun w => ?_⟩
  · have hv : vOf ρ ∈ VF H := by
      unfold VF
      exact Finset.mem_image_of_mem _ ((mem_TF H).mpr hρ)
    have hQv : Polynomial.aeval (vOf ρ) Q = rT H j (vOf ρ) := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hQe _ hv
    rw [hQv]
    by_cases him : (vOf ρ).im = 0
    · have hρim : ρ.im = 0 := by
        rw [vOf_im] at him
        rcases mul_eq_zero.mp him with h | h
        · exact absurd (by linarith : ρ.re - 1 / 2 = 0) (sub_ne_zero.mpr hρ.2.1)
        · exact h
      unfold rT
      rw [if_pos him, one_pow, one_mul]
      exact Xval_real_neg H j hρ hρim
    · rw [← XV_node H j hρ]
      exact rT_sq_mul H j hv him
  · have hy : (1 + ‖w ^ 2‖) ≤ (1 + ‖w‖) ^ 2 := by
      rw [norm_pow]
      nlinarith [norm_nonneg w]
    have hQn : Q.natDegree < (VF H).card := by
      by_cases hQ0 : Q = 0
      · rw [hQ0, Polynomial.natDegree_zero]
        exact hn
      · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQd
    have hM0 : (0 : ℝ) ≤ (VF H).card * max CV 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
    have b1 : ‖Polynomial.aeval (w ^ 2) Q‖ ≤ (VF H).card * max CV 0 * (1 + ‖w‖) ^ (2 * (VF H).card) := by
      calc ‖Polynomial.aeval (w ^ 2) Q‖ ≤ (VF H).card * max CV 0 * (1 + ‖w ^ 2‖) ^ (VF H).card :=
            poly_norm_le Q hQn (fun i => le_max_of_le_left (hQc i)) _
        _ ≤ (VF H).card * max CV 0 * ((1 + ‖w‖) ^ 2) ^ (VF H).card :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy _) hM0
        _ = (VF H).card * max CV 0 * (1 + ‖w‖) ^ (2 * (VF H).card) := by rw [← pow_mul]
    have b2 : ‖Polynomial.aeval (w ^ 2) (Kp H)‖ ≤ BK * (1 + ‖w‖) ^ (2 * DK) := by
      calc ‖Polynomial.aeval (w ^ 2) (Kp H)‖ ≤ BK * (1 + ‖w ^ 2‖) ^ DK := hK _
        _ ≤ BK * ((1 + ‖w‖) ^ 2) ^ DK := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy _) hBK
        _ = BK * (1 + ‖w‖) ^ (2 * DK) := by rw [← pow_mul]
    have b3 := hE w
    rw [Pof_eval, norm_mul, norm_mul]
    calc ‖Polynomial.aeval (w ^ 2) Q‖ * ‖Polynomial.aeval (w ^ 2) (Kp H)‖ * ‖Polynomial.aeval w (Ep H)‖
        ≤ ((VF H).card * max CV 0 * (1 + ‖w‖) ^ (2 * (VF H).card)) * (BK * (1 + ‖w‖) ^ (2 * DK)) *
            (BE * (1 + ‖w‖) ^ DE) :=
          mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hM0 (by positivity))) b3 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hM0 (by positivity)) (mul_nonneg hBK (by positivity)))
      _ = (VF H).card * max CV 0 * BK * BE * (1 + ‖w‖) ^ (2 * (VF H).card + 2 * DK + DE) := by ring

/-! ### L7d -- the terms -/

/-- The term of the power window at a zero: `S(v)^2 X_{rho,j}`. -/
theorem term_eq (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (j : ℕ) (ρ : ℂ) :
    Zeta23.paperFT (kWindow (coeffList (Pof H Q)) g0 j) (Zeta23.gammaOf ρ) =
      (Polynomial.aeval (vOf ρ) Q) ^ 2 * Xval H j ρ := by
  rw [kWindow_term _ H.hev H.hsm H.hs j, polyEvalFull_coeffList, polyEvalFull_coeffList]
  have e1 : -(I * Zeta23.gammaOf ρ) = wOf ρ := rfl
  have e2 : I * Zeta23.gammaOf ρ = -wOf ρ := by
    unfold wOf
    ring
  rw [e1, e2, Pof_prod, wOf_sq]
  unfold Xval
  ring

/-- **L7d, `tie_term_neg`:** on `T`, the term's real part is `-N_rho M^(2^(j+1))`. -/
theorem tie_term_neg (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (j : ℕ)
    (hQ : ∀ ρ ∈ tieSet Z g0 M, (Polynomial.aeval (vOf ρ) Q) ^ 2 * Xval H j ρ = -(‖Xval H j ρ‖ : ℂ))
    {ρ : ℂ} (hρ : ρ ∈ tieSet Z g0 M) :
    (Zeta23.paperFT (kWindow (coeffList (Pof H Q)) g0 j) (Zeta23.gammaOf ρ)).re = -(Nf H ρ * M ^ (2 ^ (j + 1))) := by
  rw [term_eq, hQ ρ hρ, Xval_norm H j hρ, Complex.neg_re, Complex.ofReal_re]

/-- On `Kset` the term is zero: `K(v) = 0`. -/
theorem kill_term_zero (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (j : ℕ) {ρ : ℂ} (hρ : ρ ∈ killSet Z g0 M) :
    Zeta23.paperFT (kWindow (coeffList (Pof H Q)) g0 j) (Zeta23.gammaOf ρ) = 0 := by
  rw [term_eq]
  unfold Xval
  rw [Kp_kill H hρ]
  ring

/-- **L7d, `rest_term_small`:** `|term_j(rho)| <= B^2 (1 + |w|)^(2D) offScore^(2^(j+1))` at every zero. -/
theorem rest_term_small (H : PWSetup Z g0 L M) (Q : Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ w : ℂ, ‖Polynomial.aeval w (Pof H Q)‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ) (ρ : ℂ) :
    ‖Zeta23.paperFT (kWindow (coeffList (Pof H Q)) g0 j) (Zeta23.gammaOf ρ)‖ ≤
      B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * offScore g0 ρ ^ (2 ^ (j + 1)) := by
  rw [kWindow_term _ H.hev H.hsm H.hs j, polyEvalFull_coeffList, polyEvalFull_coeffList]
  have e1 : -(I * Zeta23.gammaOf ρ) = wOf ρ := rfl
  have e2 : I * Zeta23.gammaOf ρ = -wOf ρ := by
    unfold wOf
    ring
  rw [e1, e2, norm_mul, norm_mul, norm_pow]
  have h1 := hB (wOf ρ)
  have h2 := hB (-wOf ρ)
  rw [norm_neg] at h2
  unfold offScore
  calc ‖Polynomial.aeval (wOf ρ) (Pof H Q)‖ * ‖Polynomial.aeval (-wOf ρ) (Pof H Q)‖ *
        ‖Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)‖ ^ (2 ^ (j + 1))
      ≤ (B * (1 + ‖wOf ρ‖) ^ D) * (B * (1 + ‖wOf ρ‖) ^ D) *
          ‖Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)‖ ^ (2 ^ (j + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)) (by positivity)
    _ = B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * ‖Zeta23.paperFT (phiC g0) (Zeta23.gammaOf ρ)‖ ^ (2 ^ (j + 1)) := by ring

/-! ### L7e -- the dominant and the limit -/

/-- `(1 + |ceil t|)^4 <= 128 (1 + x^4)` for `|t| <= x`. -/
theorem ceil_weight (x t : ℝ) (hx : 0 ≤ x) (htx : |t| ≤ x) : (1 + |((⌈t⌉ : ℤ) : ℝ)|) ^ 4 ≤ 128 * (1 + x ^ 4) := by
  have hceil := Int.ceil_eq_iff.mp (rfl : ⌈t⌉ = ⌈t⌉)
  have hm : |((⌈t⌉ : ℤ) : ℝ)| ≤ x + 1 :=
    abs_le.mpr ⟨by linarith [neg_abs_le t, hceil.2], by linarith [le_abs_self t, hceil.1]⟩
  have c : 1 + |((⌈t⌉ : ℤ) : ℝ)| ≤ 2 * (1 + x) := by linarith
  have d : (1 + x) ^ 4 ≤ 8 * (1 + x ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by positivity : (0 : ℝ) ≤ 7 * x ^ 2 + 10 * x + 7)]
  calc (1 + |((⌈t⌉ : ℤ) : ℝ)|) ^ 4 ≤ (2 * (1 + x)) ^ 4 := pow_le_pow_left₀ (by positivity) c 4
    _ = 16 * (1 + x) ^ 4 := by ring
    _ ≤ 128 * (1 + x ^ 4) := by linarith

/-- The decay constant of the base: `(INT |g0| + INT |g0''''|) e^{L/2}`. -/
def Aw (_H : PWSetup Z g0 L M) : ℝ := ((∫ u, |g0 u|) + ∫ u, |iteratedDeriv 4 g0 u|) * Real.exp (L / 2)

theorem Aw_nonneg (H : PWSetup Z g0 L M) : 0 ≤ Aw H := by
  unfold Aw
  have h0 : 0 ≤ ∫ u, |g0 u| := integral_nonneg fun _ => abs_nonneg _
  have h4 : 0 ≤ ∫ u, |iteratedDeriv 4 g0 u| := integral_nonneg fun _ => abs_nonneg _
  positivity

/-- **The per-zero weight:** `B^2 (1 + |w|)^(2D) (offScore / M)^(2^(D+1)) (1 + |ceil Im rho|)^4 <= const`. -/
theorem zero_weight (H : PWSetup Z g0 L M) (B : ℝ) (D : ℕ) (ρ : ℂ) (hρ : ρ ∈ Z.carrier) :
    B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)) * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 ≤
      128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1)) := by
  have hM := H.hM
  have hstrip := Z.strip ρ hρ
  have him : |(Zeta23.gammaOf ρ).im| ≤ 1 / 2 := by
    rw [gammaOf_im', abs_neg]
    exact abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  have hexp : Real.exp (L * |(Zeta23.gammaOf ρ).im|) ≤ Real.exp (L / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (Zeta23.gammaOf ρ).im, H.hL])
  have d0 := paperFT_decay_zero H.hsm.continuous H.hs (Zeta23.gammaOf ρ)
  have d4 := paperFT_decay 4 H.c4 H.hs (Zeta23.gammaOf ρ)
  have hI0 : 0 ≤ ∫ u, |g0 u| := integral_nonneg fun _ => abs_nonneg _
  have hI4 : 0 ≤ ∫ u, |iteratedDeriv 4 g0 u| := integral_nonneg fun _ => abs_nonneg _
  have e0 := mul_le_mul_of_nonneg_left hexp hI0
  have e4 := mul_le_mul_of_nonneg_left hexp hI4
  have hsA : offScore g0 ρ * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ≤ Aw H := by
    unfold offScore Aw
    nlinarith [d0, d4, e0, e4]
  have hs0 : 0 ≤ offScore g0 ρ := norm_nonneg _
  have hy1 : 1 ≤ 1 + ‖Zeta23.gammaOf ρ‖ ^ 4 := by
    have := pow_nonneg (norm_nonneg (Zeta23.gammaOf ρ)) 4
    linarith
  have hw : ‖wOf ρ‖ = ‖Zeta23.gammaOf ρ‖ := norm_wOf ρ
  have htx : |ρ.im| ≤ ‖Zeta23.gammaOf ρ‖ := by
    rw [← gammaOf_re' ρ]
    exact Complex.abs_re_le_norm _
  have hm := ceil_weight ‖Zeta23.gammaOf ρ‖ ρ.im (norm_nonneg _) htx
  have hp1 : (1 + ‖Zeta23.gammaOf ρ‖) ^ (2 * D) ≤ 8 ^ D * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ D := by
    have hx := norm_nonneg (Zeta23.gammaOf ρ)
    have e1 : (1 + ‖Zeta23.gammaOf ρ‖) ^ (2 * D) ≤ (1 + ‖Zeta23.gammaOf ρ‖) ^ (4 * D) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have e2 : (1 + ‖Zeta23.gammaOf ρ‖) ^ 4 ≤ 8 * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) := by
      nlinarith [mul_nonneg (sq_nonneg (‖Zeta23.gammaOf ρ‖ - 1))
        (by positivity : (0 : ℝ) ≤ 7 * ‖Zeta23.gammaOf ρ‖ ^ 2 + 10 * ‖Zeta23.gammaOf ρ‖ + 7)]
    calc (1 + ‖Zeta23.gammaOf ρ‖) ^ (2 * D) ≤ (1 + ‖Zeta23.gammaOf ρ‖) ^ (4 * D) := e1
      _ = ((1 + ‖Zeta23.gammaOf ρ‖) ^ 4) ^ D := by rw [pow_mul]
      _ ≤ (8 * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4)) ^ D := pow_le_pow_left₀ (by positivity) e2 D
      _ = 8 ^ D * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ D := by rw [mul_pow]
  have hyN : (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ (D + 1) ≤ (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ (2 ^ (D + 1)) :=
    pow_le_pow_right₀ hy1 (Nat.lt_two_pow_self (n := D + 1)).le
  have hsyN : (offScore g0 ρ * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4)) ^ (2 ^ (D + 1)) ≤ Aw H ^ (2 ^ (D + 1)) :=
    pow_le_pow_left₀ (mul_nonneg hs0 (by linarith)) hsA _
  have hsM : 0 ≤ (offScore g0 ρ / M) ^ (2 ^ (D + 1)) := pow_nonneg (div_nonneg hs0 hM.le) _
  have step1 : B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)) ≤
      B ^ 2 * (8 ^ D * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)) := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 (sq_nonneg B)) hsM
  have hK : 0 ≤ 128 * 8 ^ D * B ^ 2 / M ^ (2 ^ (D + 1)) := by positivity
  calc B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)) * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4
      ≤ B ^ 2 * (8 ^ D * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)) *
          (128 * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4)) :=
        mul_le_mul step1 hm (by positivity) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity)) hsM)
    _ = 128 * 8 ^ D * B ^ 2 / M ^ (2 ^ (D + 1)) *
          ((1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ (D + 1) * offScore g0 ρ ^ (2 ^ (D + 1))) := by
        rw [div_pow]
        ring
    _ ≤ 128 * 8 ^ D * B ^ 2 / M ^ (2 ^ (D + 1)) *
          ((1 + ‖Zeta23.gammaOf ρ‖ ^ 4) ^ (2 ^ (D + 1)) * offScore g0 ρ ^ (2 ^ (D + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hyN (pow_nonneg hs0 _)) hK
    _ = 128 * 8 ^ D * B ^ 2 / M ^ (2 ^ (D + 1)) *
          (offScore g0 ρ * (1 + ‖Zeta23.gammaOf ρ‖ ^ 4)) ^ (2 ^ (D + 1)) := by
        rw [mul_pow]
        ring
    _ ≤ 128 * 8 ^ D * B ^ 2 / M ^ (2 ^ (D + 1)) * Aw H ^ (2 ^ (D + 1)) := mul_le_mul_of_nonneg_left hsyN hK
    _ = 128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1)) := by
        rw [div_pow]
        ring

/-- b530's unit-interval grouping, for any weight `f` with `f (1 + |ceil Im rho|)^4 <= Bf`. -/
theorem weighted_finite_bound (Z : Zeta23.ZeroConfig) {A₀ : ℝ} (hcount : HCount Z A₀) (f : ℂ → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ ρ ∈ Z.carrier, f ρ * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 ≤ Bf)
    (s : Finset ℂ) (hsZ : ∀ ρ ∈ s, ρ ∈ Z.carrier) :
    (∑ ρ ∈ s, (Z.mult ρ : ℝ) * f ρ) ≤ 3 * A₀ * Bf * zeta3Sum := by
  have hA0 : 0 ≤ A₀ := by linarith [hcount.1]
  set c : ℂ → ℤ := fun ρ => ⌈ρ.im⌉ with hc
  set w : ℤ → ℝ := fun m => Bf / (1 + |(m : ℝ)|) ^ 4 with hw
  have step1 : (∑ ρ ∈ s, (Z.mult ρ : ℝ) * f ρ) ≤ ∑ ρ ∈ s, (Z.mult ρ : ℝ) * w (c ρ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hpos : 0 < (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 := by positivity
    show _ ≤ Bf / (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4
    exact (le_div_iff₀ hpos).mpr (hf ρ (hsZ ρ hρ))
  have step2 : (∑ ρ ∈ s, (Z.mult ρ : ℝ) * w (c ρ)) =
      ∑ m ∈ s.image c, w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image c) (g := c) (fun ρ hρ => Finset.mem_image_of_mem c hρ)]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [(Finset.mem_filter.mp hρ).2]
    ring
  have step3 : (∑ m ∈ s.image c, w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ)) ≤
      ∑ m ∈ s.image c, 3 * A₀ * Bf * (1 / (1 + |(m : ℝ)|) ^ 3) := by
    apply Finset.sum_le_sum
    intro m _
    have hwm : 0 ≤ w m := div_nonneg hBf (by positivity)
    have hf' := fiber_count Z s hsZ m
    have hcnt := hcount.2 ((m : ℝ) - 1)
    rw [sub_add_cancel] at hcnt
    have hlog : Real.log (|(m : ℝ) - 1| + 3) ≤ 3 * (1 + |(m : ℝ)|) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |(m : ℝ) - 1| + 3)
      have h2 : |(m : ℝ) - 1| ≤ |(m : ℝ)| + 1 :=
        abs_le.mpr ⟨by linarith [neg_abs_le (m : ℝ)], by linarith [le_abs_self (m : ℝ)]⟩
      linarith [abs_nonneg (m : ℝ)]
    have hN : (∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ)) ≤ A₀ * (3 * (1 + |(m : ℝ)|)) :=
      hf'.trans (hcnt.trans (mul_le_mul_of_nonneg_left hlog hA0))
    calc w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ) ≤ w m * (A₀ * (3 * (1 + |(m : ℝ)|))) :=
          mul_le_mul_of_nonneg_left hN hwm
      _ = 3 * A₀ * Bf * (1 / (1 + |(m : ℝ)|) ^ 3) := by
          show Bf / (1 + |(m : ℝ)|) ^ 4 * (A₀ * (3 * (1 + |(m : ℝ)|))) = 3 * A₀ * Bf * (1 / (1 + |(m : ℝ)|) ^ 3)
          have hq : (1 + |(m : ℝ)|) / (1 + |(m : ℝ)|) ^ 4 = 1 / (1 + |(m : ℝ)|) ^ 3 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            ring
          calc Bf / (1 + |(m : ℝ)|) ^ 4 * (A₀ * (3 * (1 + |(m : ℝ)|)))
              = 3 * A₀ * Bf * ((1 + |(m : ℝ)|) / (1 + |(m : ℝ)|) ^ 4) := by ring
            _ = 3 * A₀ * Bf * (1 / (1 + |(m : ℝ)|) ^ 3) := by rw [hq]
  have step4 : (∑ m ∈ s.image c, 3 * A₀ * Bf * (1 / (1 + |(m : ℝ)|) ^ 3)) ≤ 3 * A₀ * Bf * zeta3Sum := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (summable_zeta3.sum_le_tsum _ (fun m _ => by positivity)) (mul_nonneg (mul_nonneg (by norm_num) hA0) hBf)
  linarith [step1, step2, step3, step4]

theorem weighted_summable (Z : Zeta23.ZeroConfig) {A₀ : ℝ} (hcount : HCount Z A₀) (f : ℂ → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf0 : ∀ ρ ∈ Z.carrier, 0 ≤ f ρ)
    (hf : ∀ ρ ∈ Z.carrier, f ρ * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 ≤ Bf) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * f ρ) := by
  refine summable_of_sum_le (c := 3 * A₀ * Bf * zeta3Sum)
    (Pi.le_def.mpr fun ρ => mul_nonneg (Nat.cast_nonneg _) (hf0 ρ ρ.2)) (fun u => ?_)
  calc (∑ x ∈ u, (Z.mult (x : ℂ) : ℝ) * f x)
      = ∑ ρ ∈ u.map (Function.Embedding.subtype (· ∈ Z.carrier)), (Z.mult ρ : ℝ) * f ρ :=
        (Finset.sum_map u (Function.Embedding.subtype (· ∈ Z.carrier)) (fun ρ => (Z.mult ρ : ℝ) * f ρ)).symm
    _ ≤ 3 * A₀ * Bf * zeta3Sum := weighted_finite_bound Z hcount f Bf hBf hf _ (fun ρ hρ => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hρ
        exact i.2)

/-- **L7e, `dominant_summable`:** with `j_0 = D`, the dominant is summable over the zeros of zeta, by the kernel's
local count. -/
theorem dominant_summable (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (B : ℝ) (D : ℕ) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
      (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))) := by
  obtain ⟨A₀, h1, h2⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hM := H.hM
  have hA := Aw_nonneg H
  exact weighted_summable Zeta23.zetaZeroConfig ⟨h1, h2⟩
    (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
    (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
    (fun ρ _ => mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
    (fun ρ hρ => zero_weight H B D ρ hρ)

open Classical in
/-- The rest of the zero side: the zeros off `T`. -/
def fR (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (j : ℕ)
    (x : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then 0 else
    (Zeta23.zetaZeroConfig.mult x : ℂ) * Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x)

theorem fR_norm_le (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ)
    (x : Zeta23.zetaZeroConfig.carrier) (hT : (x : ℂ) ∉ tieSet Zeta23.zetaZeroConfig g0 M) :
    ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) := by
  have hterm := rest_term_small H (Q j) B D (hB j) j x
  have hMN : 0 < M ^ (2 ^ (j + 1)) := pow_pos H.hM _
  unfold fR
  rw [if_neg hT, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg H.hM.le,
    div_pow]
  have e : (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) *
      (offScore g0 x ^ (2 ^ (j + 1)) / M ^ (2 ^ (j + 1)))) =
      ((Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * offScore g0 x ^ (2 ^ (j + 1)))) /
        M ^ (2 ^ (j + 1)) := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)) hMN.le

theorem fR_bound (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) (j : ℕ) (hj : D ≤ j)
    (x : Zeta23.zetaZeroConfig.carrier) :
    ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) := by
  have hM := H.hM
  have hr0 : 0 ≤ offScore g0 x / M := div_nonneg (norm_nonneg _) hM.le
  have hbnd0 : 0 ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity)) (pow_nonneg hr0 _))
  by_cases hT : (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M
  · have h0 : fR H Q j x = 0 := by
      unfold fR
      rw [if_pos hT]
    rw [h0, zero_div, norm_zero]
    exact hbnd0
  by_cases hK : (x : ℂ) ∈ killSet Zeta23.zetaZeroConfig g0 M
  · have h0 : fR H Q j x = 0 := by
      unfold fR
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
  calc ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
      ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) :=
        fR_norm_le H Q B D hB j x hT
    _ ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hN) (by positivity))
          (Nat.cast_nonneg _)

/-- **L7e, `rest_tendsto_zero`:** the rest over `M^(2^(j+1))` tends to 0 (Tannery's theorem, the dominant of
`dominant_summable`, valid for `j >= D`). -/
theorem rest_tendsto_zero (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hB : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D) :
    Tendsto (fun j => ∑' x, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
  have hM := H.hM
  have hN : Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.lt_two_pow_self (n := j + 1)).le) (tendsto_add_atTop_nat 1)
  have hpt : ∀ x : Zeta23.zetaZeroConfig.carrier,
      Tendsto (fun j => fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
    intro x
    by_cases hT : (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M
    · have h0 : ∀ j, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR
        rw [if_pos hT, zero_div]
      simp only [h0]
      exact tendsto_const_nhds
    by_cases hK : (x : ℂ) ∈ killSet Zeta23.zetaZeroConfig g0 M
    · have h0 : ∀ j, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1)) = 0 := by
        intro j
        unfold fR
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
    have hc := hr.const_mul ((Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D)))
    rw [mul_zero] at hc
    refine squeeze_zero_norm (fun j => fR_norm_le H Q B D hB j x hT) (hc.congr (fun j => ?_))
    ring
  have hbd : ∀ᶠ j in atTop, ∀ x : Zeta23.zetaZeroConfig.carrier,
      ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
        (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
    Filter.eventually_atTop.mpr ⟨D, fun j hj x => fR_bound H Q B D hB j hj x⟩
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun j x => fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1)))
    (g := fun _ => (0 : ℂ)) (dominant_summable H B D) hpt hbd
  simpa using hlim

open Classical in
/-- `T` as a Finset of the carrier. -/
def sT (H : PWSetup Zeta23.zetaZeroConfig g0 L M) : Finset Zeta23.zetaZeroConfig.carrier :=
  (TF H).subtype (· ∈ Zeta23.zetaZeroConfig.carrier)

theorem mem_sT (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (x : Zeta23.zetaZeroConfig.carrier) :
    x ∈ sT H ↔ (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M := by
  classical
  unfold sT
  exact Finset.mem_subtype.trans (mem_TF H)

/-- **L7e, `zeroSide_eventually_neg`:** for some `j`, the zero side of the power window has negative real part. -/
theorem zeroSide_eventually_neg (H : PWSetup Zeta23.zetaZeroConfig g0 L M) (ρs : ℂ)
    (hρs : ρs ∈ tieSet Zeta23.zetaZeroConfig g0 M) :
    ∃ (a : List ℝ) (j : ℕ), (zeroSide (kWindow a g0 j)).re < 0 := by
  classical
  obtain ⟨B, D, hB0, hcoef⟩ := coeffs_exist H ⟨ρs, hρs⟩
  choose Q hQtie hQb using hcoef
  have hc0 : 0 < ∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x := by
    refine Finset.sum_pos (fun x hx => mul_pos ?_ (Nf_pos H ((mem_sT H x).mp hx)))
      ⟨⟨ρs, hρs.1⟩, (mem_sT H _).mpr hρs⟩
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (Zeta23.zetaZeroConfig.one_le_mult x x.2))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (rest_tendsto_zero H Q B D hQb) _ hc0
  have hj := hJ (max J D) (le_max_left _ _)
  rw [dist_zero_right] at hj
  refine ⟨coeffList (Pof H (Q (max J D))), max J D, ?_⟩
  have hDj : D ≤ max J D := le_max_right _ _
  have hM := H.hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMN : (M : ℂ) ^ (2 ^ (max J D + 1)) ≠ 0 := pow_ne_zero _ hM0
  have hsplit : ∀ x : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) =
        (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) +
          fR H Q (max J D) x := by
    intro x
    unfold fR
    split_ifs <;> simp
  have hzeroT : ∀ x ∉ sT H, (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) = 0 :=
    fun x hx => if_neg (fun h => hx ((mem_sT H x).mpr h))
  have hsumT : Summable (fun x : Zeta23.zetaZeroConfig.carrier =>
      if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0) :=
    summable_of_ne_finset_zero hzeroT
  have hsumR : Summable (fR H Q (max J D)) := by
    refine Summable.of_norm_bounded ((dominant_summable H B D).mul_left (M ^ (2 ^ (max J D + 1)))) (fun x => ?_)
    have hb := fR_bound H Q B D hQb (max J D) hDj x
    calc ‖fR H Q (max J D) x‖
        = ‖fR H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))‖ * ‖(M : ℂ) ^ (2 ^ (max J D + 1))‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hMN]
      _ ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) * M ^ (2 ^ (max J D + 1)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact mul_le_mul_of_nonneg_right hb (pow_nonneg hM.le _)
      _ = M ^ (2 ^ (max J D + 1)) * ((Zeta23.zetaZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := mul_comm _ _
  have hT : ∀ x ∈ sT H, ((Zeta23.zetaZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x)).re =
        -((Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x * M ^ (2 ^ (max J D + 1))) := by
    intro x hx
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      tie_term_neg H (Q (max J D)) (max J D) (hQtie (max J D)) ((mem_sT H x).mp hx)]
    ring
  have hR : (∑' x, fR H Q (max J D) x).re <
      (∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
    have h1 : (∑' x, fR H Q (max J D) x) =
        (∑' x, fR H Q (max J D) x / (M : ℂ) ^ (2 ^ (max J D + 1))) * (M : ℂ) ^ (2 ^ (max J D + 1)) := by
      rw [tsum_div_const, div_mul_cancel₀ _ hMN]
    have h2 : ‖∑' x, fR H Q (max J D) x‖ <
        (∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (max J D + 1)) := by
      rw [h1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact mul_lt_mul_of_pos_right hj (pow_pos hM _)
    exact lt_of_le_of_lt (Complex.re_le_norm _) h2
  have hTsum : (∑ x ∈ sT H, (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then
      (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) else 0)) =
      ∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q (max J D)))) g0 (max J D)) (Zeta23.gammaOf x) :=
    Finset.sum_congr rfl (fun x hx => if_pos ((mem_sT H x).mp hx))
  unfold zeroSide
  rw [tsum_congr hsplit, Summable.tsum_add hsumT hsumR, tsum_eq_sum hzeroT, hTsum, Complex.add_re, Complex.re_sum,
    Finset.sum_congr rfl hT, Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

/-! ### L8 -- the assembly -/

/-- The statement L7e delivers, as a Prop, so that the assembly below is compiled from it by name. -/
def zeroSideNeg : Prop :=
  ∀ (g0 : ℝ → ℝ) (L M : ℝ), PWSetup Zeta23.zetaZeroConfig g0 L M → ∀ ρs ∈ tieSet Zeta23.zetaZeroConfig g0 M,
    ∃ (a : List ℝ) (j : ℕ), (zeroSide (kWindow a g0 j)).re < 0

theorem zeroSideNeg_holds : zeroSideNeg := fun _ _ _ H ρs hρs => zeroSide_eventually_neg H ρs hρs

/-- The assembly from the named Prop: an off-line zero, the plateau's dominant zero, and a window in classK whose
zero side has negative real part contradict `h2_sign` through b321's identity. -/
theorem h2_sign_imp_rh_strip_of (hneg : zeroSideNeg) : h2_sign → rh_strip := by
  intro h2
  by_contra hno
  unfold rh_strip at hno
  push_neg at hno
  obtain ⟨ρ1, h1, hoff⟩ := hno
  have hF0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hF1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨L, hL, ρs, hρs, hoffs, hpos, hdom⟩ :=
    plateau_dominant Zeta23.zetaZeroConfig (1 / 2) hF0 hF1 ρ1 h1 hoff
  have H : PWSetup Zeta23.zetaZeroConfig (plateau (1 / 2) L hF0 hF1 hL) L
      (offScore (plateau (1 / 2) L hF0 hF1 hL) ρs) :=
    ⟨plateau_even _ _ hF0 hF1 hL, plateau_contDiff _ _ hF0 hF1 hL ⊤, plateau_support_Icc _ _ hF0 hF1 hL, hL.le,
      hpos, hdom⟩
  obtain ⟨a, j, hneg'⟩ := hneg _ L _ H ρs ⟨hρs, hoffs, rfl⟩
  have hk := kWindow_classK a H.hsm H.hs j
  have hsign := h2 _ hk
  obtain ⟨he, hc, hs, -⟩ := hk
  have hid := b321_identity _ hc hs he
  unfold b321Norm at hid
  rw [one_mul] at hid
  rw [← hid] at hsign
  have h0 := (Complex.nonneg_iff.mp hsign).1
  linarith

/-- **L8:** `h2_sign → rh_strip`. -/
theorem h2_sign_imp_rh_strip : h2_sign → rh_strip := h2_sign_imp_rh_strip_of zeroSideNeg_holds

/-- **L8:** `rh_strip → h2_sign`, b513's proof with its one use of `RH_implies_on_line` replaced by the strip
hypothesis. RHChain.lean is not edited. -/
theorem rh_strip_imp_h2_sign : rh_strip → h2_sign := by
  intro hstrip k hk
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  have hid := b321_identity (Zeta23.EF.weilTest h h) hc hs he
  have hflip : poleTerm (Zeta23.EF.weilTest h h) - primeSum (Zeta23.EF.weilTest h h)
      + archTerm (Zeta23.EF.weilTest h h) = zeroSide (Zeta23.EF.weilTest h h) := by
    rw [hid]
    unfold b321Norm
    rw [one_mul]
  rw [hflip]
  unfold zeroSide
  refine tsum_nonneg fun ρ => ?_
  have hre : (ρ : ℂ).re = 1 / 2 := hstrip (ρ : ℂ) ρ.2
  have him : (Zeta23.gammaOf (ρ : ℂ)).im = 0 := by
    unfold Zeta23.gammaOf
    rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, hre]
    first
      | rw [Complex.div_ofNat_re, Complex.one_re, sub_self, neg_zero]
      | norm_num
  have hcj : conj (Zeta23.gammaOf (ρ : ℂ)) = Zeta23.gammaOf (ρ : ℂ) :=
    Complex.conj_eq_iff_im.mpr him
  have hterm : Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ))
      = ((Complex.normSq (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ))) : ℝ) : ℂ) := by
    rw [Zeta23.EF.paperFT_weilTest hh.continuous hh.continuous hhs hhs, hcj,
      Complex.mul_conj (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ)))]
  have hm : (0 : ℂ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℂ) := by
    first
      | exact Nat.cast_nonneg _
      | (rw [← Complex.ofReal_natCast]; exact Complex.zero_le_real.mpr (Nat.cast_nonneg _))
  have hnn : (0 : ℂ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℂ)
      * Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ)) := by
    rw [hterm]
    exact mul_nonneg hm (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  exact hnn

/-- **L8:** Weil positivity on classK is RH on the kernel's configuration. -/
theorem h2_sign_iff_rh_strip : h2_sign ↔ rh_strip := ⟨h2_sign_imp_rh_strip, rh_strip_imp_h2_sign⟩

/-- **L8, (R144)(4):** `h2_sign → RiemannHypothesis`, compiled FROM the seam Prop. -/
theorem h2_sign_imp_rh_of_seam : rh_strip_imp_rh → h2_sign_imp_rh :=
  fun hseam h2 => hseam (h2_sign_imp_rh_strip h2)

/-- **L8:** the deposit's premise and Weil positivity, equivalent FROM the seam Prop. -/
theorem ch_iff_h2_sign_of_seam : rh_strip_imp_rh → (conservationHypothesis ↔ h2_sign) :=
  fun hseam => ⟨fun hch => rh_imp_h2_sign (ch_iff_rh.mp hch),
    fun h2 => ch_iff_rh.mpr (h2_sign_imp_rh_of_seam hseam h2)⟩

-- b532`s equivalence stays as it was left (a check, not a declaration).
example : h2_sign_imp_ch ↔ h2_sign_imp_rh := h2_sign_imp_ch_iff

end B321
end SIDEExplicitFormula
