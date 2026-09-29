/-
SIDE-explicit-formula -- SIDEExplicitFormula/LiWeilExchange.lean
THIS PROGRAMME'S WORK (act b561, ruling (R171); W-ORD-LI-WEIL-BRIDGE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LI-WEIL BRIDGE AT THE LIMIT EXCHANGE, in the order relay `data/b560_stageD.txt` gives it.

(D1) `blTransform` DISCHARGED: the transform of the Bombieri-Lagarias test function `k_n(u) = 1_{u<0} e^{u/2} P_n(u)` at
`gammaOf ρ` is the Li term `1 - (1 - ρ⁻¹) ^ n`, for `Re ρ > 0`. The route: `paperFT k (gammaOf ρ) = ∫_{u<0} P_n(u) e^{ρ u} du`;
the reflection `u ↦ -u`; `∫_{x>0} x^j e^{-ρ x} dx = j! / ρ^(j+1)` by induction, integrating by parts on `Ioi 0`; the
binomial sum `Σ_{j<n} C(n, j+1) (-1)^j ρ^{-(j+1)} = 1 - (1 - ρ⁻¹)^n`.

(D3) is NOT written: the decay read (relay `data/b561_decay_read.txt`) finds that no dominant for the paired truncated
transforms uniform along the family exists -- the uniform bound is of order `n/‖ρ‖` -- and derives that `LiLimitExchange n`
as stated in LiWeil.lean is expected false for `n ≥ 1` (a derivation, not a theorem of the kernel).

Nothing here proves RH or any positivity of the Li coefficients.
-/
import SIDEExplicitFormula.LiWeil

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace LiWeil

open Zeta23

/-! ## (D1) -- the transform of the Bombieri-Lagarias test function -/

/-- The norm of the integrand: `‖x ^ j e^{-ρ x}‖ = x ^ j e^{-(Re ρ) x}` for `x > 0`. -/
theorem norm_pow_mul_cexp {ρ : ℂ} (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ j * cexp (-(ρ * x))‖ = x ^ j * Real.exp (-(ρ.re * x)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp]
  congr 2
  simp [Complex.neg_re, Complex.mul_re]

/-- `x ^ j e^{-ρ x}` is integrable on `(0, ∞)` for `Re ρ > 0`. -/
theorem integrableOn_pow_mul_cexp {ρ : ℂ} (hρ : 0 < ρ.re) (j : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ j * cexp (-(ρ * x))) (Ioi 0) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (j : ℝ)) (p := 1) (b := ρ.re)
    (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) one_pos hρ
  refine Integrable.mono' hr (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_pow_mul_cexp j hx, Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- **The Gamma integral at a complex rate, for natural exponents:** `∫_{x>0} x ^ j e^{-ρ x} dx = j! / ρ ^ (j+1)` for
`Re ρ > 0`, by induction, integrating by parts on `Ioi 0`. -/
theorem integral_pow_mul_cexp {ρ : ℂ} (hρ : 0 < ρ.re) :
    ∀ j : ℕ, ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ j * cexp (-(ρ * x)) = (j.factorial : ℂ) / ρ ^ (j + 1)
  | 0 => by
    have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ; exact lt_irrefl _ hρ
    have h := integral_exp_mul_complex_Ioi (a := -ρ) (by rw [Complex.neg_re]; linarith) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have e : (fun x : ℝ => cexp (-(ρ * x))) = fun x : ℝ => cexp (-ρ * x) := by
      funext x; ring_nf
    rw [e, h]
    simp
  | j + 1 => by
    have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ; exact lt_irrefl _ hρ
    have ih := integral_pow_mul_cexp hρ j
    set u : ℝ → ℂ := fun x => (x : ℂ) ^ (j + 1) with hu
    set u' : ℝ → ℂ := fun x => ((j + 1 : ℕ) : ℂ) * (x : ℂ) ^ j with hu'
    set v : ℝ → ℂ := fun x => -cexp (-(ρ * x)) / ρ with hv
    set v' : ℝ → ℂ := fun x => cexp (-(ρ * x)) with hv'
    have hdu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
      intro x _
      have := (hasDerivAt_pow (j + 1) (x : ℂ)).comp_ofReal
      simpa [hu, hu'] using this
    have hdv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
      intro x _
      have h1 : HasDerivAt (fun z : ℂ => -cexp (-(ρ * z)) / ρ) (cexp (-(ρ * x))) (x : ℂ) := by
        have h2 := (((hasDerivAt_id (x : ℂ)).const_mul ρ).neg.cexp).neg.div_const ρ
        refine (h2.congr_deriv ?_)
        simp only [id, mul_one, Pi.neg_apply]
        field_simp
      simpa [hv, hv'] using h1.comp_ofReal
    have huv' : IntegrableOn (u * v') (Ioi 0) := by
      simpa [hu, hv', Pi.mul_def] using integrableOn_pow_mul_cexp hρ (j + 1)
    have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
      have h3 : IntegrableOn (fun x : ℝ => (-((j + 1 : ℕ) : ℂ) / ρ) * ((x : ℂ) ^ j * cexp (-(ρ * x)))) (Ioi 0) :=
        (integrableOn_pow_mul_cexp hρ j).const_mul _
      refine h3.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [hu', hv, Pi.mul_apply]
      ring
    have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (u * v) := by
        simp only [hu, hv]
        fun_prop
      have := hc.tendsto 0
      simp only [hu, hv, Pi.mul_apply, Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero j), zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hinf : Tendsto (u * v) atTop (𝓝 0) := by
      have hb : Tendsto (fun x : ℝ => (ρ.re * x) ^ (j + 1) * Real.exp (-(ρ.re * x))) atTop (𝓝 0) :=
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (j + 1)).comp (tendsto_id.const_mul_atTop hρ)
      have hb' := hb.const_mul ((1 / ρ.re) ^ (j + 1) / ‖ρ‖)
      rw [mul_zero] at hb'
      refine squeeze_zero_norm' ?_ hb'
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hu, hv, Pi.mul_apply]
      rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp]
      have hre : (-(ρ * (x : ℂ))).re = -(ρ.re * x) := by simp [Complex.mul_re]
      have e : x ^ (j + 1) = (1 / ρ.re) ^ (j + 1) * (ρ.re * x) ^ (j + 1) := by
        rw [← mul_pow]; congr 1; field_simp
      rw [hre, e]
      apply le_of_eq
      ring
    have ibp := integral_Ioi_mul_deriv_eq_deriv_mul hdu hdv huv' hu'v h0 hinf
    have e1 : (∫ x in Ioi (0 : ℝ), u' x * v x)
        = -(((j + 1 : ℕ) : ℂ) / ρ) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ j * cexp (-(ρ * x)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      simp only [hu', hv]
      ring
    have e2 : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (j + 1) * cexp (-(ρ * x))) = ∫ x in Ioi (0 : ℝ), u x * v' x := rfl
    rw [e2, ibp, e1, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The Bombieri-Lagarias polynomial at `-x`, as a complex finite sum. -/
theorem blPoly_neg_cast (n : ℕ) (x : ℝ) :
    ((blPoly n (-x) : ℝ) : ℂ) = ∑ j ∈ Finset.range n, ((n.choose (j + 1) : ℂ) * (-1) ^ j / (j.factorial : ℂ)) * (x : ℂ) ^ j := by
  unfold blPoly
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [neg_pow]
  ring

/-- **The binomial sum:** `Σ_{j<n} C(n, j+1) (-1)^j ρ^{-(j+1)} = 1 - (1 - ρ⁻¹) ^ n`. -/
theorem binomial_li (n : ℕ) (ρ : ℂ) :
    ∑ j ∈ Finset.range n, (n.choose (j + 1) : ℂ) * (-1) ^ j / ρ ^ (j + 1) = liTerm n ρ := by
  unfold liTerm
  have h := add_pow (-ρ⁻¹) (1 : ℂ) n
  rw [Finset.sum_range_succ'] at h
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at h
  rw [show (1 : ℂ) - ρ⁻¹ = -ρ⁻¹ + 1 by ring, h]
  have : ∀ j ∈ Finset.range n, (-ρ⁻¹) ^ (j + 1) * (n.choose (j + 1) : ℂ)
      = -((n.choose (j + 1) : ℂ) * (-1) ^ j / ρ ^ (j + 1)) := by
    intro j _
    rw [neg_pow, inv_pow, pow_succ (-1 : ℂ) j]
    field_simp
  rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
  ring

/-- The integrand of `paperFT (blTest n)` at `gammaOf ρ`: `1_{u<0} P_n(u) e^{ρ u}`. -/
theorem blTest_integrand (n : ℕ) (ρ : ℂ) (u : ℝ) :
    blTest n u * cexp (Complex.I * gammaOf ρ * u) = (Iio (0 : ℝ)).indicator (fun u : ℝ => ((blPoly n u : ℝ) : ℂ) * cexp (ρ * u)) u := by
  unfold blTest blSmooth
  by_cases hu : u < 0
  · rw [if_pos hu, Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
    have e : Complex.I * gammaOf ρ * (u : ℂ) = (ρ - 1 / 2) * u := by
      unfold gammaOf
      field_simp
    rw [e, Complex.ofReal_mul, Complex.ofReal_exp, mul_comm (cexp _) _, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · rw [if_neg hu, Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu), zero_mul]

/-- **(D1) DISCHARGED: `blTransform n` holds** -- the transform of `k_n` at `gammaOf ρ` is `liTerm n ρ` for `Re ρ > 0`. -/
theorem blTransform_holds (n : ℕ) : blTransform n := by
  intro ρ hρ
  unfold paperFT
  simp_rw [blTest_integrand]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
  rw [← neg_zero, ← integral_comp_neg_Ioi]
  have e : ∀ x : ℝ, ((blPoly n (-x) : ℝ) : ℂ) * cexp (ρ * ((-x : ℝ) : ℂ))
      = ∑ j ∈ Finset.range n, ((n.choose (j + 1) : ℂ) * (-1) ^ j / (j.factorial : ℂ)) * ((x : ℂ) ^ j * cexp (-(ρ * x))) := by
    intro x
    rw [blPoly_neg_cast, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring_nf
  simp_rw [e]
  rw [integral_finsetSum _ (fun j _ => (integrableOn_pow_mul_cexp hρ j).const_mul _)]
  simp_rw [integral_const_mul, integral_pow_mul_cexp hρ]
  rw [← binomial_li n ρ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  field_simp

/-! ## (D2) -- the member transforms tend to the jump's at each fixed zero -/

/-- The jump's integrand is integrable on `ℝ` for `Re ρ > 0`: `1_{u<0} P_n(u) e^{ρ u}`, from (D1)'s integrability on
`Ioi 0` reflected by `u ↦ -u`. -/
theorem integrable_blTest_integrand (n : ℕ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    Integrable (fun u : ℝ => blTest n u * cexp (Complex.I * gammaOf ρ * u)) := by
  simp_rw [blTest_integrand]
  rw [integrable_indicator_iff measurableSet_Iio]
  have hI : IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range n,
      ((n.choose (j + 1) : ℂ) * (-1) ^ j / (j.factorial : ℂ)) * ((x : ℂ) ^ j * cexp (-(ρ * x)))) (Ioi 0) :=
    integrable_finset_sum _ (fun j _ => (integrableOn_pow_mul_cexp hρ j).const_mul _)
  have hr := hI.comp_neg
  rw [Set.neg_Ioi, neg_zero] at hr
  refine hr.congr_fun (fun u _ => ?_) measurableSet_Iio
  have hb := blPoly_neg_cast n (-u)
  rw [neg_neg] at hb
  show _ = ((blPoly n u : ℝ) : ℂ) * cexp (ρ * u)
  rw [hb, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  ring_nf

/-- **(D2):** along any family of bumps supported left of `0` and tending to `1` at every `u < 0`, the transform of the
member at `gammaOf ρ` tends to the transform of `k_n`, for each fixed `ρ` with `Re ρ > 0` -- dominated convergence in `u`,
the dominant `‖k_n(u) e^{i γ u}‖` since `0 ≤ f ≤ 1`. It is per zero; it says nothing uniform over the zeros. -/
theorem truncMember_transform_tendsto (n : ℕ) {ρ : ℂ} (hρ : 0 < ρ.re) (c : ℕ → ℝ) (fs : ∀ m, ContDiffBump (c m))
    (hc : ∀ m, c m + (fs m).rOut ≤ 0) (h1 : ∀ u : ℝ, u < 0 → Tendsto (fun m => (fs m) u) atTop (𝓝 1)) :
    Tendsto (fun m => paperFT (truncMember n (fs m)) (gammaOf ρ)) atTop (𝓝 (paperFT (blTest n) (gammaOf ρ))) := by
  unfold paperFT
  set g : ℝ → ℂ := fun u => blTest n u * cexp (Complex.I * gammaOf ρ * u) with hg
  have hF : ∀ m, (fun u => truncMember n (fs m) u * cexp (Complex.I * gammaOf ρ * u))
      = fun u => (((fs m) u : ℝ) : ℂ) * g u := by
    intro m
    funext u
    rw [truncMember_eq n (fs m) (hc m) u, hg]
    ring
  simp_rw [hF]
  refine tendsto_integral_of_dominated_convergence (fun u => ‖g u‖) (fun m => ?_) (integrable_blTest_integrand n hρ).norm
    (fun m => Filter.Eventually.of_forall fun u => ?_) (Filter.Eventually.of_forall fun u => ?_)
  · exact ((Complex.continuous_ofReal.comp (fs m).continuous).aestronglyMeasurable).mul
      (integrable_blTest_integrand n hρ).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fs m).nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) (fs m).le_one
  · by_cases hu : u < 0
    · have := ((Complex.continuous_ofReal.tendsto 1).comp (h1 u hu)).mul_const (g u)
      simpa using this
    · have : g u = 0 := by
        rw [hg]
        simp only
        unfold blTest
        rw [if_neg hu, zero_mul]
      rw [this, show blTest n u * cexp (Complex.I * gammaOf ρ * (u : ℂ)) = 0 from this]
      simp only [mul_zero]
      apply tendsto_const_nhds

end LiWeil
end SIDEExplicitFormula
