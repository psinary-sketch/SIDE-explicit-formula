/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Growth.lean
THIS PROGRAMME'S WORK (act b733, ruling (R343)(3), relay data/b733_count_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE BOUNDS OF THE count FIELD. On `Re s ≥ 3/2` the series is within `Z_Q(3/2) − 2` of its first term `2`, so `|Z_Q(s)| ≤ Z_Q(3/2)` and `|Z_Q(s)| ≥ 4 − Z_Q(3/2)`, the lower
bound at the centre, which needs no Euler product and rests on `Z_Q(3/2) < 4` alone. The entire function `aE = (1 − s) Z_Q(s)` is `O(|s + 2|³)` on `Re s ≥ −1/2`: Phragmén–Lindelöf
between `Re s = 3/2` and its reflection `Re s = −1/2`, the order in the strip from `|1/Γ|` by the reflection formula and from `Λ₀` bounded by its Mellin integral.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Zeros
import Mathlib.Analysis.Complex.PhragmenLindelof

open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-! ### The lower bound at the centre -/

/-- `Z_Q(3/2)`, the real sum. -/
def totQ : ℝ := ∑' k, wQ k

theorem totQ_lt : totQ < 4 := zq_three_halves_tsum_lt

theorem totQ_nonneg : 0 ≤ totQ := tsum_nonneg wQ_nonneg

theorem norm_two_eq : ‖(2 : ℂ)‖ = 2 := by
  first
    | norm_num
    | simpa using Complex.norm_natCast 2

/-- `|Z_Q(s) − 2| ≤ Z_Q(3/2) − 2` on `Re s ≥ 3/2`. -/
theorem zq_sub_two_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖zqFn s - 2‖ ≤ totQ - 2 := by
  have hs1 : 1 < s.re := by linarith
  have h1 : LSeriesSummable aQ s := zq_summable s hs1
  have hone : LSeries.term aQ s 1 = 2 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    show ((rQ 1 : ℕ) : ℂ) / ((1 : ℕ) : ℂ) ^ s = 2
    rw [rQ_one, Nat.cast_one, Complex.one_cpow]
    norm_num
  have h2 : HasSum (LSeries.term aQ s) (LSeries aQ s) := Summable.hasSum h1
  have hE : HasSum (fun k => LSeries.term aQ s k - if k = 1 then (2 : ℂ) else 0) (LSeries aQ s - 2) :=
    h2.sub (hasSum_ite_eq (1 : ℕ) (2 : ℂ))
  have hG : HasSum (fun k => wQ k - if k = 1 then (2 : ℝ) else 0) (∑' k, wQ k - 2) :=
    wQ_summable.hasSum.sub (hasSum_ite_eq (1 : ℕ) (2 : ℝ))
  have hb : ∀ k, ‖LSeries.term aQ s k - if k = 1 then (2 : ℂ) else 0‖ ≤ wQ k - if k = 1 then (2 : ℝ) else 0 := by
    intro k
    by_cases hk : k = 1
    · subst hk
      refine le_of_eq ?_
      rw [if_pos rfl, if_pos rfl, hone, sub_self, norm_zero, wQ_one, sub_self]
    · rw [if_neg hk, if_neg hk, sub_zero, sub_zero, LSeries.norm_term_eq]
      by_cases h0 : k = 0
      · rw [if_pos h0]
        exact wQ_nonneg k
      · rw [if_neg h0]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        have hp : (k : ℝ) ^ (3 / 2 : ℝ) ≤ (k : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hk1 hs
        have hq : 0 < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
        show ‖((rQ k : ℕ) : ℂ)‖ / (k : ℝ) ^ s.re ≤ (rQ k : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)
        rw [Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hq hp
  have hn : ‖LSeries aQ s - 2‖ ≤ ∑' k, wQ k - 2 := by
    rw [← hE.tsum_eq]
    exact tsum_of_norm_bounded hG hb
  have h4 : zqFn s = LSeries aQ s := zqFn_agrees s hs1
  rw [h4]
  exact hn

/-- `|Z_Q(s)| ≤ Z_Q(3/2)` on `Re s ≥ 3/2`. -/
theorem zq_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖zqFn s‖ ≤ totQ := by
  have h := zq_sub_two_le hs
  have h3 : ‖zqFn s‖ ≤ ‖zqFn s - 2‖ + ‖(2 : ℂ)‖ := by
    calc ‖zqFn s‖ = ‖(zqFn s - 2) + 2‖ := by rw [sub_add_cancel]
      _ ≤ ‖zqFn s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
  rw [norm_two_eq] at h3
  linarith

/-- **THE LOWER BOUND AT THE CENTRE**: `|Z_Q(s)| ≥ 4 − Z_Q(3/2)` on `Re s ≥ 3/2`. -/
theorem zq_norm_ge {s : ℂ} (hs : 3 / 2 ≤ s.re) : 4 - totQ ≤ ‖zqFn s‖ := by
  have h := zq_sub_two_le hs
  have h3 : ‖(2 : ℂ)‖ ≤ ‖zqFn s - 2‖ + ‖zqFn s‖ := by
    calc ‖(2 : ℂ)‖ = ‖(2 - zqFn s) + zqFn s‖ := by rw [sub_add_cancel]
      _ ≤ ‖2 - zqFn s‖ + ‖zqFn s‖ := norm_add_le _ _
      _ = ‖zqFn s - 2‖ + ‖zqFn s‖ := by rw [norm_sub_rev]
  rw [norm_two_eq] at h3
  linarith

/-- `totQ` is `Z_Q(3/2)`: the bound reads `4 − Z_Q(3/2)`. -/
theorem zq_three_halves_eq : zqFn ((3 / 2 : ℝ) : ℂ) = (totQ : ℂ) := by
  have hs1 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have h4 : zqFn ((3 / 2 : ℝ) : ℂ) = LSeries aQ ((3 / 2 : ℝ) : ℂ) := zqFn_agrees _ hs1
  rw [h4]
  unfold LSeries totQ
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    have h0 : wQ 0 = 0 := by
      unfold wQ
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
    rw [LSeries.term_zero, h0, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn]
    show ((rQ n : ℕ) : ℂ) / (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ)) = ((wQ n : ℝ) : ℂ)
    unfold wQ
    rw [Complex.ofReal_div (rQ n : ℝ), Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

/-! ### The gamma bounds -/

theorem norm_Gamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw]
  unfold Complex.GammaIntegral
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  show ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖ = Real.exp (-x) * x ^ (w.re - 1)
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    Complex.sub_re, Complex.one_re]

theorem Gamma_Icc_bound : ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2), Real.Gamma x ≤ G := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2 : ℝ) (5 / 2)) := fun x hx => by
    have hx0 : 0 < x := by
      have h := hx.1
      linarith
    have hd : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma (fun m e => by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
    exact hd.continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image hc
  have h1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2), Real.Gamma x ≤ G := fun x hx => hG (Set.mem_image_of_mem _ hx)
  have h2 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (5 / 2) := ⟨by norm_num, by norm_num⟩
  exact ⟨G, (Real.Gamma_pos_of_pos one_pos).le.trans (h1 1 h2), h1⟩

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have e : (-z * Complex.I).re = z.im := by simp [Complex.mul_re]
    rw [e]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  have h3 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    have e : (z * Complex.I).re = -z.im := by simp [Complex.mul_re]
    rw [e]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : ‖(2 : ℂ) * Complex.sin z‖ ≤ Real.exp |z.im| + Real.exp |z.im| := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
    exact (norm_sub_le _ _).trans (add_le_add h1 h3)
  rw [norm_mul, norm_two_eq] at h2
  linarith

theorem norm_inv_Gamma_le {w : ℂ} (hw : w.re < 1) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.Gamma (1 - w.re) * Real.exp (Real.pi * |w.im|) / Real.pi := by
  have hre : 0 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hre
  have hGr : 0 < Real.Gamma (1 - w.re) := Real.Gamma_pos_of_pos (by linarith)
  have hpos : 0 ≤ Real.Gamma (1 - w.re) * Real.exp (Real.pi * |w.im|) / Real.pi :=
    div_nonneg (mul_nonneg hGr.le (Real.exp_pos _).le) Real.pi_pos.le
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  by_cases hs : Complex.sin ((Real.pi : ℂ) * w) = 0
  · rw [hs, div_zero] at hrefl
    rw [(mul_eq_zero.mp hrefl).resolve_right hG, inv_zero, norm_zero]
    exact hpos
  · have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * (Complex.sin ((Real.pi : ℂ) * w) / (Real.pi : ℂ)) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, hrefl, div_mul_div_comm, mul_comm (Real.pi : ℂ), div_self (mul_ne_zero hs hp)]
    have h1 : ‖Complex.Gamma (1 - w)‖ ≤ Real.Gamma (1 - w.re) := by
      have h := norm_Gamma_le hre
      rwa [Complex.sub_re, Complex.one_re] at h
    have h2 : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
      have h := norm_sin_le_exp ((Real.pi : ℂ) * w)
      have e : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp [Complex.mul_im]
      rwa [e, abs_mul, abs_of_pos Real.pi_pos] at h
    rw [hinv, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc ‖Complex.Gamma (1 - w)‖ * (‖Complex.sin ((Real.pi : ℂ) * w)‖ / Real.pi)
        ≤ Real.Gamma (1 - w.re) * (Real.exp (Real.pi * |w.im|) / Real.pi) :=
          mul_le_mul h1 (by gcongr) (div_nonneg (norm_nonneg _) Real.pi_pos.le) hGr.le
      _ = Real.Gamma (1 - w.re) * Real.exp (Real.pi * |w.im|) / Real.pi := by ring

/-- `1/Γ` on the strip, off the real axis: the reflection formula a unit to the left. -/
theorem inv_Gamma_strip : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
    ‖(Complex.Gamma s)⁻¹‖ ≤ K * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hG0, hG⟩ := Gamma_Icc_bound
  refine ⟨G / Real.pi, div_nonneg hG0 Real.pi_pos.le, fun s h1 h2 h3 => ?_⟩
  have hw : (s - 1).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have him : (s - 1).im = s.im := by rw [Complex.sub_im, Complex.one_im, sub_zero]
  have hn : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [him] at h
    linarith
  have hne : s - 1 ≠ 0 := fun h => by
    rw [h, norm_zero] at hn
    linarith
  have e : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
    have h := Complex.Gamma_add_one (s - 1) hne
    rwa [sub_add_cancel] at h
  have h4 := norm_inv_Gamma_le hw
  rw [him] at h4
  have h5 : Real.Gamma (1 - (s - 1).re) ≤ G := by
    have e2 : 1 - (s - 1).re = 2 - s.re := by
      rw [Complex.sub_re, Complex.one_re]
      ring
    rw [e2]
    exact hG _ ⟨by linarith, by linarith⟩
  have h6 : ‖s - 1‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have h7 : ‖(Complex.Gamma (s - 1))⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) / Real.pi :=
    h4.trans (by gcongr)
  rw [e, mul_inv, norm_mul, norm_inv]
  calc ‖s - 1‖⁻¹ * ‖(Complex.Gamma (s - 1))⁻¹‖ ≤ 1 * (G * Real.exp (Real.pi * |s.im|) / Real.pi) :=
        mul_le_mul h6 h7 (norm_nonneg _) zero_le_one
    _ = G / Real.pi * Real.exp (Real.pi * |s.im|) := by ring

/-! ### The entire factor on the strip -/

/-- **`Λ₀` is bounded on vertical strips**: its Mellin integrand is dominated by the two edges'. -/
theorem Lam0_bounded (a b : ℝ) : ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖zqPair.Λ₀ s‖ ≤ L := by
  have hc : ∀ x : ℝ, MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((x : ℂ) - 1) • zqPair.f_modif t) (Set.Ioi 0) :=
    fun x => (zqPair.isStrongFEPair_toStrongFEPair.hasMellin (x : ℂ)).1
  have hg : MeasureTheory.Integrable
      (fun t : ℝ => ‖(t : ℂ) ^ ((a : ℂ) - 1) • zqPair.f_modif t‖ + ‖(t : ℂ) ^ ((b : ℂ) - 1) • zqPair.f_modif t‖)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (MeasureTheory.Integrable.norm (hc a)).add (MeasureTheory.Integrable.norm (hc b))
  refine ⟨∫ t in Set.Ioi (0 : ℝ), (‖(t : ℂ) ^ ((a : ℂ) - 1) • zqPair.f_modif t‖
    + ‖(t : ℂ) ^ ((b : ℂ) - 1) • zqPair.f_modif t‖), fun s ha hb => ?_⟩
  show ‖∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • zqPair.f_modif t‖ ≤ _
  refine MeasureTheory.norm_integral_le_of_norm_le hg ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have key : ∀ z : ℂ, ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := fun z => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  rw [norm_smul, norm_smul, norm_smul, key s, key a, key b, Complex.ofReal_re, Complex.ofReal_re]
  have hr : t ^ (s.re - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
    rcases le_total 1 t with h | h
    · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ht0.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge ht0 h (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))
  calc t ^ (s.re - 1) * ‖zqPair.f_modif t‖ ≤ (t ^ (a - 1) + t ^ (b - 1)) * ‖zqPair.f_modif t‖ :=
        mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = t ^ (a - 1) * ‖zqPair.f_modif t‖ + t ^ (b - 1) * ‖zqPair.f_modif t‖ := add_mul _ _ _

theorem norm_qpow (s : ℂ) : ‖qBase ^ s‖ = lam ^ s.re := by
  rw [qBase_eq, Complex.norm_cpow_eq_rpow_re_of_pos lam_pos]

/-- The larger of the two edges' `lam ^ σ`, up to their sum. -/
def qMax : ℝ := lam ^ (-(1 / 2) : ℝ) + lam ^ (3 / 2 : ℝ)

theorem qMax_nonneg : 0 ≤ qMax :=
  add_nonneg (Real.rpow_nonneg lam_pos.le _) (Real.rpow_nonneg lam_pos.le _)

theorem norm_qpow_le {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : ‖qBase ^ s‖ ≤ qMax := by
  rw [norm_qpow]
  unfold qMax
  rcases le_total 1 lam with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h2).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg lam_pos.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge lam_pos h (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg lam_pos.le _))

theorem norm_le_of_sq {a b : ℂ} (h : a.re * a.re + a.im * a.im ≤ b.re * b.re + b.im * b.im) : ‖a‖ ≤ ‖b‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  rw [Complex.normSq_apply, Complex.normSq_apply]
  exact h

theorem add_two_re (s : ℂ) : (s + 2).re = s.re + 2 := by simp

theorem add_two_im (s : ℂ) : (s + 2).im = s.im := by simp

theorem norm_one_sub_le {s : ℂ} (h : -1 / 2 ≤ s.re) : ‖1 - s‖ ≤ ‖s + 2‖ := by
  refine norm_le_of_sq ?_
  rw [add_two_re, add_two_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith

theorem norm_add_one_le {s : ℂ} (h : -1 / 2 ≤ s.re) : ‖s + 1‖ ≤ ‖s + 2‖ := by
  refine norm_le_of_sq ?_
  rw [add_two_re, add_two_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  nlinarith

theorem norm_self_le {s : ℂ} (h : -1 / 2 ≤ s.re) : ‖s‖ ≤ ‖s + 2‖ := by
  refine norm_le_of_sq ?_
  rw [add_two_re, add_two_im]
  nlinarith

theorem one_le_norm_add_two {s : ℂ} (h : -1 / 2 ≤ s.re) : 1 ≤ ‖s + 2‖ := by
  have h1 := Complex.abs_re_le_norm (s + 2)
  have h2 := le_abs_self (s + 2).re
  rw [add_two_re] at h2
  linarith

/-- `aE` on the strip, off the real axis: `exp(π|t|)` times a polynomial. -/
theorem aE_strip_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
    ‖aE s‖ ≤ C * Real.exp (Real.pi * |s.im|) * ‖s + 2‖ ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := inv_Gamma_strip
  obtain ⟨L, hL⟩ := Lam0_bounded (-1 / 2) (3 / 2)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans
    (hL 1 (by rw [Complex.one_re]; norm_num) (by rw [Complex.one_re]; norm_num))
  have hC0 : 0 ≤ qMax * (K * (L + 2)) := mul_nonneg qMax_nonneg (mul_nonneg hK0 (by linarith))
  refine ⟨qMax * (K * (L + 2)), hC0, fun s h1 h2 h3 => ?_⟩
  have hQ := norm_qpow_le h1 h2
  have hn : 1 ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    linarith
  have hs0 : s ≠ 0 := fun h => by
    rw [h, norm_zero] at hn
    linarith
  have hN1 := one_le_norm_add_two h1
  have hN0 : 0 ≤ ‖s + 2‖ := norm_nonneg _
  have ha := norm_one_sub_le h1
  have e : aE s = qBase ^ s * ((Complex.Gamma s)⁻¹ * ((1 - s) * zqPair.Λ₀ s - 1)
      - (1 - s) * (s⁻¹ * (Complex.Gamma s)⁻¹)) := by
    unfold aE
    rw [Complex.Gamma_add_one s hs0, mul_inv]
  have hb1 : ‖(1 - s) * zqPair.Λ₀ s - 1‖ ≤ ‖s + 2‖ * L + 1 := (norm_sub_le _ _).trans (by
    rw [norm_mul, norm_one]
    exact add_le_add (mul_le_mul ha (hL s h1 h2) (norm_nonneg _) hN0) le_rfl)
  have hinv : ‖s‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hb2 : ‖(1 - s) * (s⁻¹ * (Complex.Gamma s)⁻¹)‖ ≤ ‖s + 2‖ * (1 * ‖(Complex.Gamma s)⁻¹‖) := by
    rw [norm_mul, norm_mul, norm_inv]
    exact mul_le_mul ha (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hN0
  have hb : ‖(Complex.Gamma s)⁻¹ * ((1 - s) * zqPair.Λ₀ s - 1) - (1 - s) * (s⁻¹ * (Complex.Gamma s)⁻¹)‖
      ≤ ‖(Complex.Gamma s)⁻¹‖ * (‖s + 2‖ * (L + 2)) := by
    calc _ ≤ ‖(Complex.Gamma s)⁻¹ * ((1 - s) * zqPair.Λ₀ s - 1)‖ + ‖(1 - s) * (s⁻¹ * (Complex.Gamma s)⁻¹)‖ :=
          norm_sub_le _ _
      _ ≤ ‖(Complex.Gamma s)⁻¹‖ * (‖s + 2‖ * L + 1) + ‖s + 2‖ * (1 * ‖(Complex.Gamma s)⁻¹‖) :=
          add_le_add (by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)) hb2
      _ ≤ ‖(Complex.Gamma s)⁻¹‖ * (‖s + 2‖ * (L + 2)) := by
          nlinarith [mul_nonneg (norm_nonneg (Complex.Gamma s)⁻¹) (sub_nonneg.mpr hN1)]
  have hpos : 0 ≤ ‖s + 2‖ * (L + 2) := mul_nonneg hN0 (by linarith)
  have hN3 : ‖s + 2‖ ≤ ‖s + 2‖ ^ 3 := le_self_pow₀ hN1 (by norm_num)
  have hE : 0 ≤ qMax * (K * (L + 2)) * Real.exp (Real.pi * |s.im|) := mul_nonneg hC0 (Real.exp_pos _).le
  rw [e, norm_mul]
  calc ‖qBase ^ s‖ * _ ≤ qMax * (K * Real.exp (Real.pi * |s.im|) * (‖s + 2‖ * (L + 2))) :=
        mul_le_mul hQ (hb.trans (mul_le_mul_of_nonneg_right (hK s h1 h2 h3) hpos)) (norm_nonneg _) qMax_nonneg
    _ = qMax * (K * (L + 2)) * Real.exp (Real.pi * |s.im|) * ‖s + 2‖ := by ring
    _ ≤ qMax * (K * (L + 2)) * Real.exp (Real.pi * |s.im|) * ‖s + 2‖ ^ 3 :=
        mul_le_mul_of_nonneg_left hN3 hE

/-! ### The two edges -/

theorem aE_right {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖aE s‖ ≤ totQ * ‖s + 2‖ ^ 3 := by
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs
    norm_num at hs
  have h1 : -1 / 2 ≤ s.re := by linarith
  have hN1 := one_le_norm_add_two h1
  have hN3 : ‖s + 2‖ ≤ ‖s + 2‖ ^ 3 := le_self_pow₀ hN1 (by norm_num)
  rw [aE_eq hs1, norm_mul]
  calc ‖1 - s‖ * ‖zqFn s‖ ≤ ‖s + 2‖ * totQ :=
        mul_le_mul (norm_one_sub_le h1) (zq_norm_le hs) (norm_nonneg _) (norm_nonneg _)
    _ = totQ * ‖s + 2‖ := mul_comm _ _
    _ ≤ totQ * ‖s + 2‖ ^ 3 := mul_le_mul_of_nonneg_left hN3 totQ_nonneg

/-- The left edge, read off the right edge by the functional equation. -/
theorem aE_left {s : ℂ} (hs : s.re = -1 / 2) : ‖aE s‖ ≤ lam ^ (-2 : ℝ) * totQ * ‖s + 2‖ ^ 3 := by
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs
    norm_num at hs
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs
    norm_num at hs
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m e => by
    have h2 : s.re = -(m : ℝ) := by
      rw [e]
      simp
    have h3 : (2 : ℝ) * (m : ℝ) = 1 := by linarith
    have h4 : 2 * m = 1 := by exact_mod_cast h3
    omega)
  have hre1 : (1 - s).re = 3 / 2 := by
    rw [Complex.sub_re, Complex.one_re, hs]
    norm_num
  have hG' : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    rw [hre1]
    norm_num)
  have hfe := zq_fe hs0 hs1 hG hG'
  have hc : 1 - s = (conj s + 1) + 1 := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.add_re, Complex.one_re, Complex.conj_re, hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.add_im, Complex.one_im, Complex.conj_im]
      ring
  have hc0 : conj s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : conj s + 1 ≠ 0 := fun h => by
    have h2 := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, Complex.conj_re, hs, Complex.zero_re] at h2
    norm_num at h2
  have h2 : Complex.Gamma (1 - s) = (conj s + 1) * (conj s * Complex.Gamma (conj s)) := by
    rw [hc, Complex.Gamma_add_one _ hc1, Complex.Gamma_add_one _ hc0]
  have h3 : conj s + 1 = conj (s + 1) := by rw [map_add, map_one]
  have hn : ‖Complex.Gamma (1 - s)‖ = ‖s + 1‖ * (‖s‖ * ‖Complex.Gamma s‖) := by
    rw [h2, norm_mul, norm_mul, h3, Complex.norm_conj, Complex.norm_conj, Complex.Gamma_conj, Complex.norm_conj]
  have hqs : ‖qBase ^ (-s)‖ = lam ^ (1 / 2 : ℝ) := by
    have e : (-s).re = 1 / 2 := by
      rw [Complex.neg_re, hs]
      norm_num
    rw [norm_qpow, e]
  have hq1 : ‖qBase ^ (-(1 - s))‖ = lam ^ (-(3 / 2) : ℝ) := by
    have e : (-(1 - s)).re = -(3 / 2) := by rw [Complex.neg_re, hre1]
    rw [norm_qpow, e]
  have hAB : lam ^ (-(3 / 2) : ℝ) = lam ^ (1 / 2 : ℝ) * lam ^ (-2 : ℝ) := by
    rw [← Real.rpow_add lam_pos]
    congr 1
    norm_num
  have hN := congrArg norm hfe
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hqs, hq1, hn, hAB] at hN
  have hApos : 0 < lam ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos lam_pos _
  have hL : 0 ≤ lam ^ (-2 : ℝ) := (Real.rpow_pos_of_pos lam_pos _).le
  have hGpos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr hG
  have hZ : ‖zqFn s‖ = lam ^ (-2 : ℝ) * ‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖ := by
    have h5 : lam ^ (1 / 2 : ℝ) * ‖Complex.Gamma s‖ * ‖zqFn s‖
        = lam ^ (1 / 2 : ℝ) * ‖Complex.Gamma s‖ * (lam ^ (-2 : ℝ) * ‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖) := by
      rw [hN]
      ring
    exact mul_left_cancel₀ (mul_pos hApos hGpos).ne' h5
  have h1' : -1 / 2 ≤ s.re := hs.ge
  have h0 := norm_one_sub_le h1'
  have ha := norm_add_one_le h1'
  have hb := norm_self_le h1'
  have hd : ‖zqFn (1 - s)‖ ≤ totQ := zq_norm_le hre1.ge
  have e1 : lam ^ (-2 : ℝ) * ‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖ ≤ lam ^ (-2 : ℝ) * ‖s + 2‖ * ‖s + 2‖ * totQ := by
    have h6 := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)) hd (norm_nonneg _)
      (mul_nonneg (norm_nonneg (s + 2)) (norm_nonneg (s + 2)))
    calc lam ^ (-2 : ℝ) * ‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖ = lam ^ (-2 : ℝ) * (‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖) := by ring
      _ ≤ lam ^ (-2 : ℝ) * (‖s + 2‖ * ‖s + 2‖ * totQ) := mul_le_mul_of_nonneg_left h6 hL
      _ = lam ^ (-2 : ℝ) * ‖s + 2‖ * ‖s + 2‖ * totQ := by ring
  rw [aE_eq hs1, norm_mul, hZ]
  calc ‖1 - s‖ * (lam ^ (-2 : ℝ) * ‖s + 1‖ * ‖s‖ * ‖zqFn (1 - s)‖)
      ≤ ‖s + 2‖ * (lam ^ (-2 : ℝ) * ‖s + 2‖ * ‖s + 2‖ * totQ) :=
        mul_le_mul h0 e1 (mul_nonneg (mul_nonneg (mul_nonneg hL (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
          (norm_nonneg _)
    _ = lam ^ (-2 : ℝ) * totQ * ‖s + 2‖ ^ 3 := by ring

/-! ### Phragmén–Lindelöf -/

/-- The constant of the growth bound. -/
def growthM : ℝ := totQ + lam ^ (-2 : ℝ) * totQ

theorem growthM_nonneg : 0 ≤ growthM :=
  add_nonneg totQ_nonneg (mul_nonneg (Real.rpow_nonneg lam_pos.le _) totQ_nonneg)

/-- **THE GROWTH BOUND**: `|aE(s)| ≤ M |s + 2|³` on `Re s ≥ −1/2`, by Phragmén–Lindelöf between the two edges for
`aE(s)/(s + 2)³`, whose a-priori order `exp(π|t|)` is below the `exp(exp(c|t|))`, `c < π/2`, the strip of width `2` allows. -/
theorem aE_growth : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → ‖aE s‖ ≤ M * ‖s + 2‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := aE_strip_bound
  have hpos : ∀ z : ℂ, -1 / 2 ≤ z.re → 0 < ‖z + 2‖ ^ 3 := fun z hz =>
    pow_pos (lt_of_lt_of_le zero_lt_one (one_le_norm_add_two hz)) 3
  have hne : ∀ z : ℂ, -1 / 2 ≤ z.re → z + 2 ≠ 0 := fun z hz h => by
    have h1 := one_le_norm_add_two hz
    rw [h, norm_zero] at h1
    linarith
  have hd : DifferentiableOn ℂ (fun z : ℂ => aE z / (z + 2) ^ 3) {z : ℂ | -1 / 2 ≤ z.re} := by
    intro z hz
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (z + 2) ^ 3) z := by fun_prop
    have h3 : DifferentiableAt ℂ (fun z : ℂ => aE z / (z + 2) ^ 3) z :=
      DifferentiableAt.div (aE_differentiable z) h2 (pow_ne_zero 3 (hne z hz))
    exact h3.differentiableWithinAt
  have hcl : closure (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2)) ⊆ {z : ℂ | -1 / 2 ≤ z.re} :=
    closure_minimal (fun z hz => hz.1.le) (isClosed_le continuous_const Complex.continuous_re)
  have hfd : DiffContOnCl ℂ (fun z : ℂ => aE z / (z + 2) ^ 3) (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2)) :=
    (hd.mono hcl).diffContOnCl
  have hO : Asymptotics.IsBigO
      (Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2)))
      (fun z : ℂ => aE z / (z + 2) ^ 3) (fun z : ℂ => Real.exp (Real.pi * Real.exp (1 * |z.im|))) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.eventually_inf_principal.mpr ?_)
    have h1 : ∀ᶠ z in Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop, (1 : ℝ) ≤ (_root_.abs ∘ Complex.im) z :=
      Filter.tendsto_comap.eventually (Filter.eventually_ge_atTop 1)
    filter_upwards [h1] with z hz1 hz2
    have hz3 : -1 / 2 < z.re ∧ z.re < 3 / 2 := hz2
    have hz4 : 1 ≤ |z.im| := hz1
    rw [norm_div, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le, div_le_iff₀ (hpos z hz3.1.le)]
    have hb := hC z hz3.1.le hz3.2.le hz4
    have h5 : |z.im| ≤ Real.exp (1 * |z.im|) := by
      have h6 := Real.add_one_le_exp (1 * |z.im|)
      rw [one_mul] at h6 ⊢
      linarith
    have h7 : Real.exp (Real.pi * |z.im|) ≤ Real.exp (Real.pi * Real.exp (1 * |z.im|)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h5 Real.pi_pos.le)
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hC0)
      (hpos z hz3.1.le).le)
  have hc1 : (1 : ℝ) < Real.pi / (3 / 2 - (-1 / 2)) := by
    have h := Real.pi_gt_three
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have hT := totQ_nonneg
  have hLT : 0 ≤ lam ^ (-2 : ℝ) * totQ := mul_nonneg (Real.rpow_nonneg lam_pos.le _) hT
  have hl : ∀ z : ℂ, z.re = -1 / 2 → ‖aE z / (z + 2) ^ 3‖ ≤ growthM := fun z hz => by
    have hz1 : -1 / 2 ≤ z.re := hz.ge
    rw [norm_div, norm_pow, div_le_iff₀ (hpos z hz1)]
    refine (aE_left hz).trans (mul_le_mul_of_nonneg_right ?_ (hpos z hz1).le)
    unfold growthM
    linarith
  have hr : ∀ z : ℂ, z.re = 3 / 2 → ‖aE z / (z + 2) ^ 3‖ ≤ growthM := fun z hz => by
    have hz1 : -1 / 2 ≤ z.re := by
      rw [hz]
      norm_num
    rw [norm_div, norm_pow, div_le_iff₀ (hpos z hz1)]
    refine (aE_right hz.ge).trans (mul_le_mul_of_nonneg_right ?_ (hpos z hz1).le)
    unfold growthM
    linarith
  refine ⟨growthM, growthM_nonneg, fun s hs => ?_⟩
  rcases le_total s.re (3 / 2) with h | h
  · have h2 := PhragmenLindelof.vertical_strip (a := -1 / 2) (b := 3 / 2) (C := growthM)
      (f := fun z : ℂ => aE z / (z + 2) ^ 3) hfd ⟨1, hc1, Real.pi, hO⟩ hl hr hs h
    have h3 : ‖aE s / (s + 2) ^ 3‖ ≤ growthM := h2
    rwa [norm_div, norm_pow, div_le_iff₀ (hpos s hs)] at h3
  · refine (aE_right h).trans (mul_le_mul_of_nonneg_right ?_ (hpos s hs).le)
    have h3 : totQ ≤ growthM := by
      unfold growthM
      linarith
    exact h3

end ZQ
end Schema
end SIDEExplicitFormula
