/-
SIDE-explicit-formula -- SIDEExplicitFormula/LiWeil.lean
THIS PROGRAMME'S WORK (act b560, ruling (R170) and its (4) amendment; W-ORD-LI-WEIL-BRIDGE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LI-WEIL BRIDGE, STAGED, over the GENUINE zero configuration `Zeta23.zetaZeroConfig` (carrier the nontrivial zeros
of Mathlib's `riemannZeta`, multiplicity its analytic order; Statement/SeamClosed.lean:42).

STAGE A -- the terms. The configuration type `ZeroConfig` (Defs.lean:136) carries one symmetry, `reflect ρ = 1 - conj ρ`,
which fixes every point of the critical line; a term paired by it degenerates there. The pairing here is by
CONJUGATION (the author's (R170)(4) amendment): first the conjugation stability of the genuine instance, derived from
`riemannZeta_conj` and `analyticOrderAt_zeta_conj` (ZetaReflect.lean:78, :160) -- a fact about that instance, not a
field of the type; then `liTerm n ρ = 1 - (1 - ρ⁻¹) ^ n`, the pair `liTerm n ρ + liTerm n (conj ρ) = 2 Re (liTerm n ρ)`,
and at `Re ρ = 1/2` the real part nonnegative because `‖1 - ρ⁻¹‖ = 1`. (The same per-term fact is compiled in
SIDE-lv-conservation as `PartialPositivity.blTerm_nonneg_of_onLine`, on another toolchain; cited, not imported.)

Nothing here proves RH, h2_sign or any positivity of the Li coefficients without RH.
-/
import SIDEExplicitFormula.Seam

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace LiWeil

open Zeta23

/-! ## Stage A -- the conjugation stability of the genuine instance, and the terms -/

/-- A member of the genuine configuration is not the pole. -/
theorem ne_one_of_mem {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) : ρ ≠ 1 := by
  rw [zetaZeroConfig_carrier] at h
  obtain ⟨_, _, h1⟩ := h
  intro e
  rw [e, Complex.one_re] at h1
  exact lt_irrefl _ h1

/-- **Conjugation stability of the genuine instance (the set):** the conjugate of a nontrivial zero of `riemannZeta`
is one, from `riemannZeta_conj` (ZetaReflect.lean:78). -/
theorem conj_mem {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) : (starRingEnd ℂ) ρ ∈ zetaZeroConfig.carrier := by
  have hne := ne_one_of_mem h
  rw [zetaZeroConfig_carrier] at h ⊢
  obtain ⟨hz, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj hne, hz, map_zero]
  · rw [Complex.conj_re]; exact h0
  · rw [Complex.conj_re]; exact h1

/-- **Conjugation stability of the genuine instance (the multiplicity):** `mult (conj ρ) = mult ρ`, from
`analyticOrderAt_zeta_conj` (ZetaReflect.lean:160). -/
theorem mult_conj {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) :
    zetaZeroConfig.mult ((starRingEnd ℂ) ρ) = zetaZeroConfig.mult ρ := by
  rw [zetaZeroConfig_mult]
  unfold zeroMult
  rw [analyticOrderAt_zeta_conj (ne_one_of_mem h)]

/-- The Bombieri-Lagarias term at a point: `1 - (1 - ρ⁻¹) ^ n` (BALANCE_AND_POSITIVITY.md :70, :422). -/
def liTerm (n : ℕ) (ρ : ℂ) : ℂ := 1 - (1 - ρ⁻¹) ^ n

/-- The term paired with its conjugate's. -/
def pairTerm (n : ℕ) (ρ : ℂ) : ℂ := liTerm n ρ + liTerm n ((starRingEnd ℂ) ρ)

/-- The term at the conjugate is the conjugate of the term. -/
theorem liTerm_conj (n : ℕ) (ρ : ℂ) : liTerm n ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (liTerm n ρ) := by
  unfold liTerm
  rw [map_sub, map_one, map_pow, map_sub, map_one, map_inv₀]

/-- **The pair is real by construction:** `pairTerm n ρ = 2 * Re (liTerm n ρ)`. -/
theorem pairTerm_eq (n : ℕ) (ρ : ℂ) : pairTerm n ρ = ((2 * (liTerm n ρ).re : ℝ) : ℂ) := by
  rw [pairTerm, liTerm_conj, Complex.add_conj]

/-- The pair's imaginary part is zero. -/
theorem pairTerm_im (n : ℕ) (ρ : ℂ) : (pairTerm n ρ).im = 0 := by
  rw [pairTerm_eq, Complex.ofReal_im]

/-- The pair's real part is twice the term's. -/
theorem pairTerm_re (n : ℕ) (ρ : ℂ) : (pairTerm n ρ).re = 2 * (liTerm n ρ).re := by
  rw [pairTerm_eq, Complex.ofReal_re]

/-- On the critical line `‖ρ - 1‖ = ‖ρ‖`. -/
theorem norm_sub_one_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖ρ - 1‖ = ‖ρ‖ := by
  have hsq : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, h]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **On the critical line `‖1 - ρ⁻¹‖ = 1`.** -/
theorem norm_one_sub_inv_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖1 - ρ⁻¹‖ = 1 := by
  have hρ : ρ ≠ 0 := by
    intro e
    rw [e, Complex.zero_re] at h
    norm_num at h
  have he : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [he, norm_div, norm_sub_one_of_re_half h, div_self (norm_ne_zero_iff.mpr hρ)]

/-- **Stage A's nonnegativity, per zero:** at `Re ρ = 1/2` the real part of the term is nonnegative -- algebra over `ℂ`,
no fact about zeta. -/
theorem liTerm_re_nonneg_of_re_half (n : ℕ) {ρ : ℂ} (h : ρ.re = 1 / 2) : 0 ≤ (liTerm n ρ).re := by
  have h1 : ‖(1 - ρ⁻¹) ^ n‖ = 1 := by rw [norm_pow, norm_one_sub_inv_of_re_half h, one_pow]
  have h2 : ((1 - ρ⁻¹) ^ n).re ≤ 1 := (Complex.re_le_norm _).trans h1.le
  unfold liTerm
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- **The pair on the critical line is real and nonnegative.** -/
theorem pairTerm_re_nonneg_of_re_half (n : ℕ) {ρ : ℂ} (h : ρ.re = 1 / 2) : 0 ≤ (pairTerm n ρ).re := by
  rw [pairTerm_re]
  have := liTerm_re_nonneg_of_re_half n h
  linarith

/-! ## Stage B -- the decay, its constant named, and the summability over the genuine zeros -/

/-- **The second-order remainder of `(1 - w) ^ n`:** for `‖w‖ ≤ 1`, `‖(1 - w) ^ n - 1 + n w‖ ≤ n 2 ^ n ‖w‖ ^ 2`, by
induction from `(1 - w) ^ (n+1) - 1 + (n+1) w = (1 - w) ((1 - w) ^ n - 1 + n w) + n w ^ 2`. -/
theorem rem_bound {w : ℂ} (hw : ‖w‖ ≤ 1) : ∀ n : ℕ, ‖(1 - w) ^ n - 1 + (n : ℂ) * w‖ ≤ n * 2 ^ n * ‖w‖ ^ 2
  | 0 => by simp
  | n + 1 => by
    have ih := rem_bound hw n
    have key : (1 - w) ^ (n + 1) - 1 + ((n + 1 : ℕ) : ℂ) * w
        = (1 - w) * ((1 - w) ^ n - 1 + (n : ℂ) * w) + (n : ℂ) * w ^ 2 := by push_cast; ring
    rw [key]
    have h1w : ‖1 - w‖ ≤ 2 := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hn : (n : ℝ) ≤ 2 ^ (n + 1) := by
      have h2 : (n : ℝ) < 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self : n < 2 ^ n)
      have h3 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
      linarith
    have hx : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    have hr : 0 ≤ ‖(1 - w) ^ n - 1 + (n : ℂ) * w‖ := norm_nonneg _
    calc ‖(1 - w) * ((1 - w) ^ n - 1 + (n : ℂ) * w) + (n : ℂ) * w ^ 2‖
        ≤ ‖1 - w‖ * ‖(1 - w) ^ n - 1 + (n : ℂ) * w‖ + n * ‖w‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ 2 * (n * 2 ^ n * ‖w‖ ^ 2) + n * ‖w‖ ^ 2 := by
          have := mul_le_mul h1w ih hr (by norm_num)
          linarith
      _ ≤ ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * ‖w‖ ^ 2 := by
          have hm := mul_le_mul_of_nonneg_right hn hx
          have e : ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * ‖w‖ ^ 2 - (2 * (n * 2 ^ n * ‖w‖ ^ 2) + n * ‖w‖ ^ 2)
              = 2 ^ (n + 1) * ‖w‖ ^ 2 - n * ‖w‖ ^ 2 := by push_cast; ring
          linarith

/-- The real part of the term, bounded: for `1 ≤ ‖ρ‖` and `0 ≤ Re ρ ≤ 1`,
`|Re (liTerm n ρ)| ≤ (n + n 2 ^ n) / ‖ρ‖ ^ 2`. -/
theorem liTerm_re_abs_le (n : ℕ) {ρ : ℂ} (h1 : 1 ≤ ‖ρ‖) (h0 : 0 ≤ ρ.re) (hr1 : ρ.re ≤ 1) :
    |(liTerm n ρ).re| ≤ (n + n * 2 ^ n) / ‖ρ‖ ^ 2 := by
  have hn2 : 0 < ‖ρ‖ ^ 2 := by positivity
  have hw : ‖ρ⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1
  have hwn : ‖ρ⁻¹‖ ^ 2 = 1 / ‖ρ‖ ^ 2 := by rw [norm_inv, inv_pow, one_div]
  have hre : (ρ⁻¹).re = ρ.re / ‖ρ‖ ^ 2 := by rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hre0 : 0 ≤ (ρ⁻¹).re := by rw [hre]; positivity
  have hre1 : (ρ⁻¹).re ≤ 1 / ‖ρ‖ ^ 2 := by rw [hre]; exact div_le_div_of_nonneg_right hr1 hn2.le
  have he := rem_bound hw n
  have hdecomp : liTerm n ρ = (n : ℂ) * ρ⁻¹ - ((1 - ρ⁻¹) ^ n - 1 + (n : ℂ) * ρ⁻¹) := by unfold liTerm; ring
  have hre_d : (liTerm n ρ).re = n * (ρ⁻¹).re - ((1 - ρ⁻¹) ^ n - 1 + (n : ℂ) * ρ⁻¹).re := by
    rw [hdecomp, Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [hre_d]
  have hb := abs_le.mp ((Complex.abs_re_le_norm ((1 - ρ⁻¹) ^ n - 1 + (n : ℂ) * ρ⁻¹)).trans (hwn ▸ he))
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have t1 : (n : ℝ) * (ρ⁻¹).re ≤ n * (1 / ‖ρ‖ ^ 2) := mul_le_mul_of_nonneg_left hre1 hnn
  have t0 : 0 ≤ (n : ℝ) * (ρ⁻¹).re := mul_nonneg hnn hre0
  have e : ((n : ℝ) + n * 2 ^ n) / ‖ρ‖ ^ 2 = n * (1 / ‖ρ‖ ^ 2) + n * 2 ^ n * (1 / ‖ρ‖ ^ 2) := by ring
  rw [e, abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- **The decay constant, named:** `liConst n = 2 (n + n 2 ^ n)`. -/
def liConst (n : ℕ) : ℝ := 2 * (n + n * 2 ^ n)

theorem liConst_nonneg (n : ℕ) : 0 ≤ liConst n := by unfold liConst; positivity

/-- **Stage B's bound:** for `1 ≤ ‖ρ‖` and `0 ≤ Re ρ ≤ 1`, `‖pairTerm n ρ‖ ≤ liConst n / ‖ρ‖ ^ 2`. The pair decays like
`‖ρ‖⁻²` because the first-order part `n ρ⁻¹` enters only through its real part `n Re ρ / ‖ρ‖ ^ 2`. -/
theorem pairTerm_norm_le (n : ℕ) {ρ : ℂ} (h1 : 1 ≤ ‖ρ‖) (h0 : 0 ≤ ρ.re) (hr1 : ρ.re ≤ 1) :
    ‖pairTerm n ρ‖ ≤ liConst n / ‖ρ‖ ^ 2 := by
  rw [pairTerm_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  have := liTerm_re_abs_le n h1 h0 hr1
  unfold liConst
  rw [mul_div_assoc]
  linarith

/-- **Stage B's summability, over the genuine zeros:** `Σ_ρ m_ρ Re (pairTerm n ρ)` converges absolutely, from
`zero_sum_inv_sq` (ZeroSummability.lean:247, the kernel's local count in its log form) -- the finitely many zeros with
`|Im ρ| < 1` excepted as `EF_zero_sum_summable_gen` excepts them. -/
theorem pair_summable (n : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * (pairTerm n ρ).re) := by
  have hg : Summable (fun ρ : zetaZeroConfig.carrier =>
      (9 / 4 * liConst n) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    (WeilEF.zero_sum_inv_sq zetaSeam).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : (zetaZeroConfig.window (-1) 1).Finite := zetaZeroConfig.finite_window _ _
  have hSfin : ((fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) ⁻¹' (zetaZeroConfig.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ zetaZeroConfig.carrier := ρ.2
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
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
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hpb := pairTerm_norm_le n hnorm1 hstrip.1 hstrip.2
  have hre_le : |(pairTerm n ρ).re| ≤ ‖pairTerm n ρ‖ := Complex.abs_re_le_norm _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm]
  calc (zetaZeroConfig.mult ρ : ℝ) * |(pairTerm n ρ).re|
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (liConst n / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hre_le.trans hpb) hm
    _ = (zetaZeroConfig.mult ρ : ℝ) * liConst n * (1 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * liConst n * ((9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hm (liConst_nonneg n))
    _ = (9 / 4 * liConst n) * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        rw [zetaZeroConfig_mult]; ring

/-! ## Stage C -- the coefficient over the genuine zeros, and the forward half -/

/-- **The Li coefficient over the genuine zero configuration:** `λ_n := (1/2) Σ_ρ m_ρ Re (pairTerm n ρ)`, the sum over
the nontrivial zeros of Mathlib's `riemannZeta` (`zetaZeroConfig`, carrier `IsNontrivialZero`, multiplicity the analytic
order). Each conjugate pair is counted from both of its members, hence the half; `LiCoeff_eq` gives the unpaired form
`Σ_ρ m_ρ Re (1 - (1 - ρ⁻¹) ^ n)`. **The sum converges absolutely** (`pair_summable`, Stage B), so this `tsum` is the sum
and not a junk value. -/
def LiCoeff (n : ℕ) : ℝ :=
  (1 / 2) * ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * (pairTerm n ρ).re

/-- The coefficient as the sum of the real parts of the Bombieri-Lagarias terms, with multiplicity. -/
theorem LiCoeff_eq (n : ℕ) :
    LiCoeff n = ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * (liTerm n ρ).re := by
  unfold LiCoeff
  rw [← tsum_mul_left]
  congr 1
  ext ρ
  rw [pairTerm_re]
  ring

/-- The unpaired real-part sum converges absolutely as well. -/
theorem liTerm_re_summable (n : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * (liTerm n ρ).re) := by
  have h := (pair_summable n).mul_left (1 / 2)
  refine h.congr (fun ρ => ?_)
  rw [pairTerm_re]
  ring

/-- **The forward half, over the genuine zeros:** Mathlib's `RiemannHypothesis` gives `0 ≤ λ_n` for every `n`. Under RH
each zero lies on the line and each term's real part is nonnegative (`liTerm_re_nonneg_of_re_half`); `tsum_nonneg`
closes it. The sum is absolutely convergent (`pair_summable`), so the conclusion is about the convergent sum. -/
theorem rh_imp_li_nonneg : RiemannHypothesis → ∀ n : ℕ, 0 ≤ LiCoeff n := by
  intro hRH n
  unfold LiCoeff
  refine mul_nonneg (by norm_num) (tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) ?_)
  have hne := ne_one_of_mem ρ.2
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  obtain ⟨hz, h0, _⟩ := hmem
  have htriv : ¬∃ k : ℕ, (ρ : ℂ) = -2 * ((k : ℂ) + 1) := by
    rintro ⟨k, hk⟩
    rw [hk] at h0
    have hre : (-2 * ((k : ℂ) + 1)).re = -2 * ((k : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact pairTerm_re_nonneg_of_re_half n (hRH ρ hz htriv hne)

/-! ## Stage D -- the identity, priced and probed

The Bombieri-Lagarias test function in the kernel's variable. `paperFT k z = ∫ k u e^{i z u} du` (Defs.lean:60) and
`gammaOf ρ = (ρ - 1/2)/i`, so `paperFT k (gammaOf ρ) = ∫ k u e^{(ρ - 1/2) u} du`. With `P_n(y) = Σ_{j=1}^{n} C(n,j)
y^{j-1}/(j-1)!` and `k_n(u) = 1_{u<0} e^{u/2} P_n(u)`, the substitution `x = e^{u}` gives `∫_0^1 x^{ρ-1} P_n(log x) dx`,
which is `1 - (1 - 1/ρ)^n` for `Re ρ > 0` (the Bombieri-Lagarias form). `k_n` is one-sided with a jump at `0`
(`P_n(0) = n`) and is not compactly supported, so it is outside EF_lit's class (`ContDiff ℝ 2`, `HasCompactSupport`,
ExplicitFormula.lean:97-100). The truncation family multiplies the everywhere-smooth `e^{u/2} P_n(u)` by a smooth bump
supported in `(-∞, 0]`: each member is in EF_lit's class (the one truncation lemma), and EF_lit applies to it. The
passage to the limit -- the zero side's limit against `LiCoeff n` -- is STATED as a `Prop` and not proved. -/

/-- The Bombieri-Lagarias polynomial `P_n(y) = Σ_{j=1}^{n} C(n, j) y^{j-1} / (j-1)!`. -/
def blPoly (n : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) * y ^ j / (j.factorial : ℝ)

/-- The smooth profile `e^{u/2} P_n(u)`, as a complex-valued function. -/
def blSmooth (n : ℕ) (u : ℝ) : ℂ := ((Real.exp (u / 2) * blPoly n u : ℝ) : ℂ)

/-- **The Bombieri-Lagarias test function in the kernel's variable:** `k_n(u) = 1_{u<0} e^{u/2} P_n(u)`. -/
def blTest (n : ℕ) (u : ℝ) : ℂ := if u < 0 then blSmooth n u else 0

/-- **T1, stated (a `Prop`, not proved here):** the transform of `k_n` at `gammaOf ρ` is the Li term, for `Re ρ > 0`. -/
def blTransform (n : ℕ) : Prop := ∀ ρ : ℂ, 0 < ρ.re → paperFT (blTest n) (gammaOf ρ) = liTerm n ρ

/-- **The truncation family:** the smooth profile times a smooth bump `f` (a `ContDiffBump c`). -/
def truncMember (n : ℕ) {c : ℝ} (f : ContDiffBump c) (u : ℝ) : ℂ := ((f u : ℝ) : ℂ) * blSmooth n u

theorem blPoly_contDiff (n : ℕ) : ContDiff ℝ 2 (blPoly n) := by
  unfold blPoly
  exact ContDiff.sum fun j _ => (contDiff_const.mul (contDiff_id.pow j)).div_const _

theorem blSmooth_contDiff (n : ℕ) : ContDiff ℝ 2 (blSmooth n) := by
  unfold blSmooth
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul (blPoly_contDiff n))

/-- **Stage D's truncation lemma:** every member of the family is in EF_lit's class -- `ContDiff ℝ 2` with compact
support. -/
theorem truncMember_classEF (n : ℕ) {c : ℝ} (f : ContDiffBump c) :
    ContDiff ℝ 2 (truncMember n f) ∧ HasCompactSupport (truncMember n f) := by
  refine ⟨?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp (f.contDiff (n := 2))).mul (blSmooth_contDiff n)
  · have h : HasCompactSupport (fun u => ((f u : ℝ) : ℂ)) := f.hasCompactSupport.comp_left Complex.ofReal_zero
    exact h.mul_right

/-- On a bump supported left of `0`, the member is the bump times `k_n` itself. -/
theorem truncMember_eq (n : ℕ) {c : ℝ} (f : ContDiffBump c) (hc : c + f.rOut ≤ 0) (u : ℝ) :
    truncMember n f u = ((f u : ℝ) : ℂ) * blTest n u := by
  unfold truncMember blTest
  by_cases hu : u < 0
  · rw [if_pos hu]
  · rw [if_neg hu]
    have hf : f u = 0 := by
      by_contra hne
      have hmem : u ∈ Function.support f := hne
      rw [f.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
      linarith [hmem.2, not_lt.mp hu]
    rw [hf]
    simp

/-- **EF_lit at each member of the family** (Zeta23's EF_lit for the genuine instance, WeilEF/Main.lean:286): the zero
sum converges absolutely and equals the literature right-hand side. -/
theorem truncMember_EF (n : ℕ) {c : ℝ} (f : ContDiffBump c) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * paperFT (truncMember n f) (gammaOf ρ)) ∧
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT (truncMember n f) (gammaOf ρ)
      = EF.literatureRHS (truncMember n f) :=
  WeilEF.EF_lit_zetaZeroConfig _ (truncMember_classEF n f).1 (truncMember_classEF n f).2

/-- **The limit exchange, STATED (a `Prop`, not proved here) -- the HELD point.** Along any bumps supported left of `0`
that tend to `1` at every `u < 0`, the zero side of EF_lit at the truncations tends to `LiCoeff n`. At each member the
zero sum is absolutely convergent (EF_lit); the target is the paired (real-part) Li sum, whose unpaired terms decay only
like `n/ρ`. A dominant for the truncated transforms uniform along the family is what the Tannery route needs, and
EF_lit's own bound grows with the bump's derivatives near `0`: that is the pairing hazard, and it is not crossed here.
**FALSE AS STATED for `n ≥ 1` (b561's reading, relay `data/b561_decay_read.txt` (7), lines 42-55):** the one-sided
smoothing moves the jump's midpoint into `u < 0`, and the zero side drifts like `-(n/2) log(1/δ)` along every family in
the hypothesis. That is a derivation resting on Stirling and the Riemann-von Mangoldt count, neither compiled here; it
is not a theorem of this kernel. The `Prop` is kept as stated and not withdrawn (ruling (R172)(1)(a), act b562). -/
def LiLimitExchange (n : ℕ) : Prop :=
  ∀ (c : ℕ → ℝ) (fs : ∀ m, ContDiffBump (c m)), (∀ m, c m + (fs m).rOut ≤ 0) →
    (∀ u : ℝ, u < 0 → Filter.Tendsto (fun m => (fs m) u) Filter.atTop (nhds 1)) →
    Filter.Tendsto (fun m => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (truncMember n (fs m)) (gammaOf ρ)) Filter.atTop (nhds (LiCoeff n : ℂ))

/-- **The identity, conditional on the exchange:** if `LiLimitExchange n` holds, then along the same family the
literature right-hand sides of EF_lit -- the pole terms, the prime sum and the Γ-integral at the truncations -- tend to
`LiCoeff n`. The step is EF_lit itself (`truncMember_EF`); the exchange is the hypothesis, not proved. -/
theorem li_identity_of_exchange (n : ℕ) (hX : LiLimitExchange n) (c : ℕ → ℝ) (fs : ∀ m, ContDiffBump (c m))
    (hc : ∀ m, c m + (fs m).rOut ≤ 0) (h1 : ∀ u : ℝ, u < 0 → Filter.Tendsto (fun m => (fs m) u) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun m => EF.literatureRHS (truncMember n (fs m))) Filter.atTop (nhds (LiCoeff n : ℂ)) :=
  (hX c fs hc h1).congr fun m => (truncMember_EF n (fs m)).2

end LiWeil
end SIDEExplicitFormula
