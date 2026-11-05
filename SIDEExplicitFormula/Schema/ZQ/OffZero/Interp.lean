/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Interp.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (3)(5) and (7.1), G1) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G1, THE ALIASING LEMMA, GENERAL. For `f` complex-differentiable on the open disc `ball c R` and continuous on its closure, bounded by `B` on
the sphere, `ω` a primitive `M`-th root of unity and `0 < ρ < R`, the discrete Cauchy interpolant from the `M` nodes `c + ρ ω^j` differs from
`f` at `c + u`, `‖u‖ ≤ r < R`, by at most `B R (r^M + ρ^M) / ((R - r)(R^M - ρ^M))`: the `r^M` term the truncation, the `ρ^M` term the aliasing.
By the Cauchy integral formula and a finite identity of the roots of unity; no power series. No constant of the programme in any binder.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

open Complex Metric Finset Set
open scoped Real

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- The discrete Cauchy interpolant of `f` from the `M` nodes `c + ρ ω^j`, at `c + u`:
`∑_{k<M} (u/ρ)^k • ((1/M) ∑_{j<M} (ω^j)^(-k) • f (c + ρ ω^j))`. -/
noncomputable def discreteCauchy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c ω : ℂ) (ρ : ℝ) (M : ℕ) (u : ℂ) : E :=
  ∑ k ∈ range M, (u / (ρ : ℂ)) ^ k • ((M : ℂ)⁻¹ • ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k • f (c + (ρ : ℂ) * ω ^ j))

/-- The root sums: `∑_{j<M} (ω^j)^(-k) (ω^j)^n` is `M` when `n = k` and `0` otherwise, for `k, n < M`. -/
theorem rootSum_inv_pow_mul_pow {ω : ℂ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M)
    {k n : ℕ} (hk : k < M) (hn : n < M) :
    ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (ω ^ j) ^ n = if n = k then (M : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ((ω ^ j)⁻¹) ^ k * (ω ^ j) ^ n = (ω ^ (M - k + n)) ^ j := by
    intro j
    have hx : (ω ^ j) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h1 : (ω ^ j) ^ (M - k) * (ω ^ j) ^ k = 1 := by rw [← pow_add, Nat.sub_add_cancel hk.le, hx]
    have h2 : (ω ^ j) ^ (M - k) = ((ω ^ j)⁻¹) ^ k := by rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h1
    rw [← h2, ← pow_add, ← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun j _ => hpow j)]
  by_cases hnk : n = k
  · rw [if_pos hnk, hnk, Nat.sub_add_cancel hk.le, hω.pow_eq_one]
    simp
  · rw [if_neg hnk]
    have hne : ω ^ (M - k + n) ≠ 1 := by
      intro h
      rw [hω.pow_eq_one_iff_dvd] at h
      obtain ⟨q, hq⟩ := h
      rcases q with _ | _ | q
      · simp only [Nat.mul_zero] at hq
        omega
      · simp only [Nat.zero_add, Nat.mul_one] at hq
        omega
      · have h3 : M * 2 ≤ M * (q + 1 + 1) := Nat.mul_le_mul_left M (by omega)
        rw [← hq] at h3
        clear hq
        omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]

/-- The kernel at one weight: `(1/M) ∑_j (ω^j)^(-k) / (v - ρ ω^j) = ρ^k v^(M-1-k) / (v^M - ρ^M)` for `k < M`. -/
theorem nodeKernel_eq {ω v : ℂ} {ρ : ℂ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M)
    (hv : v ^ M ≠ ρ ^ M) {k : ℕ} (hk : k < M) :
    (M : ℂ)⁻¹ * ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (v - ρ * ω ^ j)⁻¹ = ρ ^ k * v ^ (M - 1 - k) / (v ^ M - ρ ^ M) := by
  have hD : v ^ M - ρ ^ M ≠ 0 := sub_ne_zero.2 hv
  have hMc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hinv : ∀ j : ℕ, (v - ρ * ω ^ j)⁻¹ = (∑ i ∈ range M, v ^ i * (ρ * ω ^ j) ^ (M - 1 - i)) / (v ^ M - ρ ^ M) := by
    intro j
    have ha : (ρ * ω ^ j) ^ M = ρ ^ M := by
      rw [mul_pow, ← pow_mul, mul_comm j M, pow_mul, hω.pow_eq_one, one_pow, mul_one]
    have hS := geom_sum₂_mul v (ρ * ω ^ j) M
    rw [ha] at hS
    have hva : v - ρ * ω ^ j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hS
      exact hD hS.symm
    rw [eq_div_iff hD, ← hS, mul_comm (∑ i ∈ range M, v ^ i * (ρ * ω ^ j) ^ (M - 1 - i)), ← mul_assoc,
      inv_mul_cancel₀ hva, one_mul]
  have key : ∀ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (v - ρ * ω ^ j)⁻¹ =
      ∑ i ∈ range M, (v ^ i * ρ ^ (M - 1 - i) / (v ^ M - ρ ^ M)) * (((ω ^ j)⁻¹) ^ k * (ω ^ j) ^ (M - 1 - i)) := by
    intro j _
    rw [hinv j, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (M - 1 - k)]
  · rw [show M - 1 - (M - 1 - k) = k by omega, rootSum_inv_pow_mul_pow hM hω hk hk, if_pos rfl]
    have h1 : (M : ℂ)⁻¹ * (M : ℂ) = 1 := inv_mul_cancel₀ hMc
    linear_combination (ρ ^ k * v ^ (M - 1 - k) / (v ^ M - ρ ^ M)) * h1
  · intro i hi hik
    have hi' := Finset.mem_range.1 hi
    rw [rootSum_inv_pow_mul_pow hM hω hk (by omega : M - 1 - i < M), if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- The whole kernel: `∑_{k<M} (u/ρ)^k (1/M) ∑_j (ω^j)^(-k) / (v - ρ ω^j) = (v^M - u^M) / ((v - u)(v^M - ρ^M))`. -/
theorem kernel_eq {ω v u : ℂ} {ρ : ℂ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M) (hρ : ρ ≠ 0)
    (hv : v ^ M ≠ ρ ^ M) (hvu : v ≠ u) :
    ∑ k ∈ range M, (u / ρ) ^ k * ((M : ℂ)⁻¹ * ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (v - ρ * ω ^ j)⁻¹) =
      (v ^ M - u ^ M) / ((v - u) * (v ^ M - ρ ^ M)) := by
  have hD : v ^ M - ρ ^ M ≠ 0 := sub_ne_zero.2 hv
  have hsum : ∑ k ∈ range M, (u / ρ) ^ k * ((M : ℂ)⁻¹ * ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (v - ρ * ω ^ j)⁻¹) =
      (∑ k ∈ range M, u ^ k * v ^ (M - 1 - k)) / (v ^ M - ρ ^ M) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [nodeKernel_eq hM hω hv (Finset.mem_range.1 hk), div_pow]
    have h1 : ρ ^ k / ρ ^ k = 1 := div_self (pow_ne_zero _ hρ)
    linear_combination (u ^ k * v ^ (M - 1 - k) / (v ^ M - ρ ^ M)) * h1
  have hg := geom_sum₂_mul u v M
  rw [hsum, div_eq_div_iff hD (mul_ne_zero (sub_ne_zero.2 hvu) hD)]
  linear_combination (-(v ^ M - ρ ^ M)) * hg

/-- A circle integral of a finite sum of circle-integrable functions is the sum of their integrals. -/
theorem circleIntegral_finsetSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (s : Finset ι) {g : ι → ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (g i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, g i z) = ∑ i ∈ s, ∮ z in C(c, R), g i z := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum fun i hi => (h i hi).out

/-- The node `c + ρ ω^j` lies in `ball c R` when `0 < ρ < R`. -/
theorem node_mem_ball {c ω : ℂ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M) {ρ R : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < R) (j : ℕ) : c + (ρ : ℂ) * ω ^ j ∈ ball c R := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_pow, hω.norm'_eq_one hM.ne', one_pow, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hρ.le]
  exact hρR

/-- `z ↦ (a * (z - w)⁻¹) • f z` is continuous on the sphere when `w` lies in the ball. -/
theorem continuousOn_sub_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {c w : ℂ} {R : ℝ} (hf : ContinuousOn f (sphere c R)) (hw : w ∈ ball c R) (a : ℂ) :
    ContinuousOn (fun z => (a * (z - w)⁻¹) • f z) (sphere c R) := by
  refine ContinuousOn.smul (continuousOn_const.mul (ContinuousOn.inv₀ (continuous_id'.sub continuous_const).continuousOn
    fun z hz => ?_)) hf
  intro h
  rw [sub_eq_zero] at h
  rw [mem_sphere, h] at hz
  rw [mem_ball] at hw
  linarith

/-- **The identity.** `f (c + u) - P(c + u) = (2πi)⁻¹ ∮ ((u^M - ρ^M) / ((z - c - u)((z - c)^M - ρ^M))) • f z`. -/
theorem sub_discreteCauchy_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c ω u : ℂ} {R ρ : ℝ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M) (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hu : ‖u‖ < R) :
    f (c + u) - discreteCauchy f c ω ρ M u =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (((u ^ M - (ρ : ℂ) ^ M) / ((z - c - u) * ((z - c) ^ M - (ρ : ℂ) ^ M))) • f z) := by
  have hR : 0 < R := hρ.trans hρR
  have hcont : ContinuousOn f (closedBall c R) := by simpa [closure_ball c hR.ne'] using hf.continuousOn
  have hsph : ContinuousOn f (sphere c R) := hcont.mono sphere_subset_closedBall
  have hcu : c + u ∈ ball c R := by rwa [mem_ball, dist_eq_norm, add_sub_cancel_left]
  have hnode := node_mem_ball (c := c) hM hω hρ hρR
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hval : ∀ w ∈ ball c R, f w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z :=
    fun w hw => (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm
  set a : ℕ → ℕ → ℂ := fun k j => (u / (ρ : ℂ)) ^ k * ((M : ℂ)⁻¹ * ((ω ^ j)⁻¹) ^ k) with ha
  -- the interpolant as a double sum of values
  have hP : discreteCauchy f c ω ρ M u = ∑ k ∈ range M, ∑ j ∈ range M, a k j • f (c + (ρ : ℂ) * ω ^ j) := by
    unfold discreteCauchy
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    simp only [ha]
    ring
  -- the double sum of integrals as one integral
  have hI : (∮ z in C(c, R), ∑ k ∈ range M, ∑ j ∈ range M, (a k j * (z - (c + (ρ : ℂ) * ω ^ j))⁻¹) • f z) =
      ∑ k ∈ range M, ∑ j ∈ range M, a k j • ∮ z in C(c, R), (z - (c + (ρ : ℂ) * ω ^ j))⁻¹ • f z := by
    rw [circleIntegral_finsetSum _ (fun k _ => ContinuousOn.circleIntegrable hR.le
      (continuousOn_finsetSum _ fun j _ => continuousOn_sub_inv_smul hsph (hnode j) (a k j)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [circleIntegral_finsetSum _ (fun j _ => ContinuousOn.circleIntegrable hR.le (continuousOn_sub_inv_smul hsph (hnode j) (a k j)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [mul_smul]
    exact circleIntegral.integral_smul _ _ _ _
  have hint1 : CircleIntegrable (fun z => (z - (c + u))⁻¹ • f z) c R := by
    simpa using ContinuousOn.circleIntegrable hR.le (continuousOn_sub_inv_smul hsph hcu 1)
  have hint2 : CircleIntegrable (fun z => ∑ k ∈ range M, ∑ j ∈ range M, (a k j * (z - (c + (ρ : ℂ) * ω ^ j))⁻¹) • f z) c R :=
    ContinuousOn.circleIntegrable hR.le (continuousOn_finsetSum _ fun k _ =>
      continuousOn_finsetSum _ fun j _ => continuousOn_sub_inv_smul hsph (hnode j) (a k j))
  have hN : ∀ k j, a k j • f (c + (ρ : ℂ) * ω ^ j) =
      (2 * π * I : ℂ)⁻¹ • (a k j • ∮ z in C(c, R), (z - (c + (ρ : ℂ) * ω ^ j))⁻¹ • f z) := by
    intro k j
    rw [hval _ (hnode j), smul_comm]
  rw [hP, Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hN k j))]
  simp_rw [← Finset.smul_sum]
  rw [← hI, hval _ hcu, ← smul_sub, ← circleIntegral.integral_sub hint1 hint2]
  congr 1
  refine circleIntegral.integral_congr hR.le fun z hz => ?_
  beta_reduce
  simp_rw [← Finset.sum_smul]
  rw [← sub_smul]
  congr 1
  -- the scalar identity on the sphere
  have hzR : ‖z - c‖ = R := by rwa [mem_sphere, dist_eq_norm] at hz
  have hvM : (z - c) ^ M ≠ (ρ : ℂ) ^ M := by
    intro h
    have h' := congrArg norm h
    rw [norm_pow, norm_pow, hzR, Complex.norm_real, Real.norm_of_nonneg hρ.le] at h'
    exact (pow_lt_pow_left₀ hρR hρ.le hM.ne').ne' h'
  have hvu : z - c ≠ u := by
    intro h
    rw [← h, hzR] at hu
    exact lt_irrefl _ hu
  have hK := kernel_eq (v := z - c) (u := u) hM hω hρc hvM hvu
  have hsplit : ∑ k ∈ range M, ∑ j ∈ range M, a k j * (z - (c + (ρ : ℂ) * ω ^ j))⁻¹ =
      ∑ k ∈ range M, (u / (ρ : ℂ)) ^ k * ((M : ℂ)⁻¹ * ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * (z - c - (ρ : ℂ) * ω ^ j)⁻¹) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha, show z - (c + (ρ : ℂ) * ω ^ j) = z - c - (ρ : ℂ) * ω ^ j by ring]
    ring
  rw [hsplit, hK, show z - (c + u) = z - c - u by ring]
  have hD : (z - c) ^ M - (ρ : ℂ) ^ M ≠ 0 := sub_ne_zero.2 hvM
  have h2 : ((z - c) ^ M - (ρ : ℂ) ^ M) * ((z - c) ^ M - (ρ : ℂ) ^ M)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-(z - c - u)⁻¹) * h2

/-- **G1, the aliasing lemma.** For `f` differentiable on `ball c R` and continuous on its closure, `‖f‖ ≤ B` on the sphere, `ω` a primitive
`M`-th root of unity, `0 < ρ < R` and `‖u‖ ≤ r < R`: `‖f (c + u) - discreteCauchy f c ω ρ M u‖ ≤ B R (r^M + ρ^M) / ((R - r)(R^M - ρ^M))`. -/
theorem DiffContOnCl.norm_sub_discreteCauchy_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c ω u : ℂ} {R ρ r B : ℝ} {M : ℕ} (hM : 0 < M) (hω : IsPrimitiveRoot ω M) (hρ : 0 < ρ) (hρR : ρ < R)
    (hr : 0 ≤ r) (hrR : r < R) (hf : DiffContOnCl ℂ f (ball c R)) (hB : ∀ w ∈ sphere c R, ‖f w‖ ≤ B) (hu : ‖u‖ ≤ r) :
    ‖f (c + u) - discreteCauchy f c ω ρ M u‖ ≤ B * R * (r ^ M + ρ ^ M) / ((R - r) * (R ^ M - ρ ^ M)) := by
  have hR : 0 < R := hρ.trans hρR
  have hRr : 0 < R - r := sub_pos.2 hrR
  have hRM : 0 < R ^ M - ρ ^ M := sub_pos.2 (pow_lt_pow_left₀ hρR hρ.le hM.ne')
  have hN : 0 ≤ r ^ M + ρ ^ M := add_nonneg (pow_nonneg hr _) (pow_nonneg hρ.le _)
  have hX : 0 ≤ (r ^ M + ρ ^ M) / ((R - r) * (R ^ M - ρ ^ M)) := div_nonneg hN (mul_pos hRr hRM).le
  rw [sub_discreteCauchy_eq hM hω hρ hρR hf (hu.trans_lt hrR)]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (C := B * ((r ^ M + ρ ^ M) / ((R - r) * (R ^ M - ρ ^ M)))) fun z hz => ?_).trans (le_of_eq (by ring))
  have hzR : ‖z - c‖ = R := by rwa [mem_sphere, dist_eq_norm] at hz
  rw [norm_smul, mul_comm B]
  refine mul_le_mul ?_ (hB z hz) (norm_nonneg _) hX
  rw [norm_div, norm_mul]
  have hnum : ‖u ^ M - (ρ : ℂ) ^ M‖ ≤ r ^ M + ρ ^ M := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    gcongr
  have hd1 : R - r ≤ ‖z - c - u‖ := by
    have := norm_sub_norm_le (z - c) u
    linarith
  have hd2 : R ^ M - ρ ^ M ≤ ‖(z - c) ^ M - (ρ : ℂ) ^ M‖ := by
    have := norm_sub_norm_le ((z - c) ^ M) ((ρ : ℂ) ^ M)
    rw [norm_pow, norm_pow, hzR, Complex.norm_real, Real.norm_of_nonneg hρ.le] at this
    exact this
  exact div_le_div₀ hN hnum (mul_pos hRr hRM) (mul_le_mul hd1 hd2 hRM.le (norm_nonneg _))

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
