/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Amplify.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (3)(5) and (4) G2) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G2, THE COMPANIONS, GENERAL. (i) The interpolant from a vector of values, `dcVec`, of which `discreteCauchy` is the instance at the nodes; a
change of at most `δ` in each value moves it by at most `δ Σ_{k<M} (r/ρ)^k` on `‖u‖ ≤ r` (the amplification A). (ii) A polynomial's Lipschitz
bound on a disc, `Σ_k ‖a_k‖ k r^(k−1)` (L_P), proved. (iii) The node rounding: for `f` DiffContOnCl on `ball c R`, `‖f‖ ≤ B` on the sphere,
`‖f a − f b‖ ≤ B R ‖a − b‖ / (R − s)^2` for `a, b` within `s < R` of `c`, by the Cauchy integral formula. No constant of the programme in any binder.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Interp

open Complex Metric Finset Set
open scoped Real

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- The interpolant from a vector of values: `∑_{k<M} (u/ρ)^k • ((1/M) ∑_{j<M} (ω^j)^(-k) • v j)`. -/
noncomputable def dcVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : ℕ → E) (ω : ℂ) (ρ : ℝ) (M : ℕ) (u : ℂ) : E :=
  ∑ k ∈ range M, (u / (ρ : ℂ)) ^ k • ((M : ℂ)⁻¹ • ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k • v j)

theorem discreteCauchy_eq_dcVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c ω : ℂ) (ρ : ℝ) (M : ℕ) (u : ℂ) :
    discreteCauchy f c ω ρ M u = dcVec (fun j => f (c + (ρ : ℂ) * ω ^ j)) ω ρ M u := rfl

/-- **(i) The amplification.** Values moved by at most `δ` move the interpolant by at most `δ Σ_{k<M} (r/ρ)^k` on `‖u‖ ≤ r`. -/
theorem norm_dcVec_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ω u : ℂ} {ρ r δ : ℝ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M) (hρ : 0 < ρ) (hu : ‖u‖ ≤ r)
    {v v' : ℕ → E} (hv : ∀ j < M, ‖v j - v' j‖ ≤ δ) :
    ‖dcVec v ω ρ M u - dcVec v' ω ρ M u‖ ≤ δ * ∑ k ∈ range M, (r / ρ) ^ k := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hu
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  unfold dcVec
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  rw [norm_smul, norm_smul]
  have hj : ‖∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k • (v j - v' j)‖ ≤ M * δ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => δ) fun j hj => ?_).trans (le_of_eq ?_))
    · rw [norm_smul, norm_pow, norm_inv, norm_pow, hω.norm'_eq_one hM.ne', one_pow, inv_one, one_pow, one_mul]
      exact hv j (Finset.mem_range.1 hj)
    · simp
  have hk : ‖(u / (ρ : ℂ)) ^ k‖ ≤ (r / ρ) ^ k := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hρ.le) (div_le_div_of_nonneg_right hu hρ.le) k
  have hMn : ‖(M : ℂ)⁻¹‖ = (M : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  rw [hMn]
  calc ‖(u / (ρ : ℂ)) ^ k‖ * ((M : ℝ)⁻¹ * ‖∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k • (v j - v' j)‖)
      ≤ (r / ρ) ^ k * ((M : ℝ)⁻¹ * (M * δ)) :=
        mul_le_mul hk (mul_le_mul_of_nonneg_left hj (by positivity)) (by positivity) (pow_nonneg (div_nonneg hr hρ.le) k)
    _ = δ * (r / ρ) ^ k := by rw [inv_mul_cancel_left₀ hMr, mul_comm]

theorem norm_pow_sub_pow_le {u u' : ℂ} {r : ℝ} (hu : ‖u‖ ≤ r) (hu' : ‖u'‖ ≤ r) (k : ℕ) :
    ‖u ^ k - u' ^ k‖ ≤ k * r ^ (k - 1) * ‖u - u'‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hu
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i ∈ range k, ‖u ^ i * u' ^ (k - 1 - i)‖ ≤ r ^ (k - 1) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖u‖ ^ i * ‖u'‖ ^ (k - 1 - i) ≤ r ^ i * r ^ (k - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu i) (pow_le_pow_left₀ (norm_nonneg _) hu' _) (by positivity) (pow_nonneg hr _)
      _ = r ^ (k - 1) := by
          rw [← pow_add]
          congr 1
          omega
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **(ii) L_P.** `‖Σ_{k<M} a_k u^k − Σ_{k<M} a_k u'^k‖ ≤ (Σ_{k<M} ‖a_k‖ k r^(k−1)) ‖u − u'‖` on `‖u‖, ‖u'‖ ≤ r`. -/
theorem norm_poly_sub_le (a : ℕ → ℂ) (M : ℕ) {u u' : ℂ} {r : ℝ} (hu : ‖u‖ ≤ r) (hu' : ‖u'‖ ≤ r) :
    ‖∑ k ∈ range M, a k * u ^ k - ∑ k ∈ range M, a k * u' ^ k‖ ≤
      (∑ k ∈ range M, ‖a k‖ * (k * r ^ (k - 1))) * ‖u - u'‖ := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le hu hu' k) (norm_nonneg _)

/-- **(iii) The node rounding.** `‖f a − f b‖ ≤ B R ‖a − b‖ / (R − s)^2` for `a, b` within `s < R` of `c`. -/
theorem DiffContOnCl.norm_sub_le_of_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c a b : ℂ} {R s B : ℝ} (hs : 0 ≤ s) (hsR : s < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hB : ∀ w ∈ sphere c R, ‖f w‖ ≤ B) (ha : ‖a - c‖ ≤ s) (hb : ‖b - c‖ ≤ s) :
    ‖f a - f b‖ ≤ B * R * ‖a - b‖ / (R - s) ^ 2 := by
  have hR : 0 < R := hs.trans_lt hsR
  have hRs : 0 < R - s := sub_pos.2 hsR
  have hcont : ContinuousOn f (closedBall c R) := by simpa [closure_ball c hR.ne'] using hf.continuousOn
  have hsph : ContinuousOn f (sphere c R) := hcont.mono sphere_subset_closedBall
  have haB : a ∈ ball c R := by rw [mem_ball, dist_eq_norm]; exact ha.trans_lt hsR
  have hbB : b ∈ ball c R := by rw [mem_ball, dist_eq_norm]; exact hb.trans_lt hsR
  have hia : CircleIntegrable (fun z => (z - a)⁻¹ • f z) c R := by
    simpa using ContinuousOn.circleIntegrable hR.le (continuousOn_sub_inv_smul hsph haB 1)
  have hib : CircleIntegrable (fun z => (z - b)⁻¹ • f z) c R := by
    simpa using ContinuousOn.circleIntegrable hR.le (continuousOn_sub_inv_smul hsph hbB 1)
  rw [← hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul haB, ← hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hbB,
    ← smul_sub, ← circleIntegral.integral_sub hia hib]
  have hbound : ∀ z ∈ sphere c R, ‖(z - a)⁻¹ • f z - (z - b)⁻¹ • f z‖ ≤ ‖a - b‖ / (R - s) ^ 2 * B := by
    intro z hz
    have hzR : ‖z - c‖ = R := by rwa [mem_sphere, dist_eq_norm] at hz
    have hza : R - s ≤ ‖z - a‖ := by
      have h := norm_sub_norm_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring, hzR] at h
      linarith
    have hzb : R - s ≤ ‖z - b‖ := by
      have h := norm_sub_norm_le (z - c) (b - c)
      rw [show z - c - (b - c) = z - b by ring, hzR] at h
      linarith
    have hza0 : z - a ≠ 0 := norm_pos_iff.1 (hRs.trans_le hza)
    have hzb0 : z - b ≠ 0 := norm_pos_iff.1 (hRs.trans_le hzb)
    have h1 : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ hza0
    have h2 : (z - b) * (z - b)⁻¹ = 1 := mul_inv_cancel₀ hzb0
    have hk : (z - a)⁻¹ - (z - b)⁻¹ = (a - b) * ((z - a)⁻¹ * (z - b)⁻¹) := by
      linear_combination (-(z - a)⁻¹) * h2 + (z - b)⁻¹ * h1
    rw [← sub_smul, hk, norm_smul, norm_mul, norm_mul, norm_inv, norm_inv]
    have hia' : ‖z - a‖⁻¹ ≤ (R - s)⁻¹ := inv_anti₀ hRs hza
    have hib' : ‖z - b‖⁻¹ ≤ (R - s)⁻¹ := inv_anti₀ hRs hzb
    have hB' := hB z hz
    have hBn : 0 ≤ B := (norm_nonneg _).trans hB'
    calc ‖a - b‖ * (‖z - a‖⁻¹ * ‖z - b‖⁻¹) * ‖f z‖ ≤ ‖a - b‖ * ((R - s)⁻¹ * (R - s)⁻¹) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hia' hib' (by positivity) (by positivity)) (norm_nonneg _)) hB'
            (norm_nonneg _) (by positivity)
      _ = ‖a - b‖ / (R - s) ^ 2 * B := by rw [div_eq_mul_inv, ← inv_pow]; ring
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hbound).trans (le_of_eq ?_)
  ring

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
