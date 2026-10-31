/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperGammaBound.lean
THIS PROGRAMME'S WORK (act b729, ruling (R339)(4); branch keiper-b725, no main, no tag) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE BOUND ON γ_1 AND THE SIGN OF λ_2. `stieltjes_one_lt : (stieltjes 1).re < -1/20`, and from it, through
`liCoeff_two_pos_of_stieltjes_one`, `liCoeff_two_pos : 0 < LiWeil.LiCoeff 2`.

THE ROUTE. For v > 0 write ψ(x) = x^(-1-v) - x^(-1), and T(M) = Σ_{n ≤ M} ψ(n) + ((M + 1/2)^(-v) - 1) / v + log (M + 1/2).
ψ is concave on [9/2, ∞) (`psiV_concave`: its second derivative is nonpositive there because `log (9/2) ≥ 3/2`), so the midpoint rule runs one way
(`Psi_step`), T is monotone from M = 4 (`TV_mono`), and T tends to ζ₀(1 + v) - γ (`TV_tendsto`, `zeta0_re`). Hence ζ₀(1 + v) - γ ≥ T(4), and T(4) is
bounded below by hand with `Real.exp_bound` (`TV_four_ge`): at first order in v, log(9/2)²/2 - log 2 - log 3 / 3 > 0.066. The right slope of ζ₀ at 1
then gives Re ζ₀'(1) ≥ 3/50 (`deriv_bound`), and γ_1 = -ζ₀'(1).

THE SCOPE: the one rung λ_2. Nothing here is a statement about the zeros of ζ beyond these theorems' own words, or proves RH or any sign of any
other λ_n.
-/
import SIDEExplicitFormula.KeiperGammaOne
import Mathlib

open Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperTwo

open Keiper

/-- ψ(x) = x^(-1-v) - x^(-1) -/
def psiV (v x : ℝ) : ℝ := x ^ (-v - 1) - x ^ (-1 : ℝ)

/-- ψ' -/
def psiV1 (v x : ℝ) : ℝ := (-v - 1) * x ^ (-v - 1 - 1) - (-1) * x ^ ((-1 : ℝ) - 1)

/-- ψ'' -/
def psiV2 (v x : ℝ) : ℝ :=
  (-v - 1) * ((-v - 1 - 1) * x ^ (-v - 1 - 1 - 1)) - (-1) * (((-1 : ℝ) - 1) * x ^ ((-1 : ℝ) - 1 - 1))

/-- an antiderivative of ψ -/
def PsiV (v x : ℝ) : ℝ := (-1 / v) * x ^ (-v) - Real.log x

theorem hasDerivAt_psiV (v : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (psiV v) (psiV1 v x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-v - 1)) ((-v - 1) * x ^ (-v - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ (-1 : ℝ)) ((-1) * x ^ ((-1 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  exact h1.fun_sub h2

theorem hasDerivAt_psiV1 (v : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (psiV1 v) (psiV2 v x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-v - 1 - 1)) ((-v - 1 - 1) * x ^ (-v - 1 - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ ((-1 : ℝ) - 1)) (((-1 : ℝ) - 1) * x ^ ((-1 : ℝ) - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h3 : HasDerivAt (fun y : ℝ => (-v - 1) * y ^ (-v - 1 - 1)) ((-v - 1) * ((-v - 1 - 1) * x ^ (-v - 1 - 1 - 1))) x :=
    h1.const_mul (-v - 1)
  have h4 : HasDerivAt (fun y : ℝ => (-1) * y ^ ((-1 : ℝ) - 1)) ((-1) * (((-1 : ℝ) - 1) * x ^ ((-1 : ℝ) - 1 - 1))) x :=
    h2.const_mul (-1)
  exact h3.fun_sub h4

theorem hasDerivAt_PsiV {v : ℝ} (hv : 0 < v) {x : ℝ} (hx : 0 < x) : HasDerivAt (PsiV v) (psiV v x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-v)) (-v * x ^ (-v - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => (-1 / v) * y ^ (-v)) ((-1 / v) * (-v * x ^ (-v - 1))) x :=
    h1.const_mul (-1 / v)
  have h3 : HasDerivAt (fun y : ℝ => (-1 / v) * y ^ (-v) - Real.log y) ((-1 / v) * (-v * x ^ (-v - 1)) - x⁻¹) x :=
    h2.fun_sub (Real.hasDerivAt_log hx.ne')
  have e : psiV v x = (-1 / v) * (-v * x ^ (-v - 1)) - x⁻¹ := by
    have hv' : v ≠ 0 := hv.ne'
    have e1 : (-1 / v) * (-v * x ^ (-v - 1)) = x ^ (-v - 1) := by
      field_simp
    unfold psiV
    rw [e1, Real.rpow_neg_one]
  rw [e]
  exact h3

/-- 3/2 ≤ log (9/2): e³ < 81/4 -/
theorem log_nine_half_ge : (3 / 2 : ℝ) ≤ Real.log (9 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have h3 := Real.exp_pos (3 / 2)
  have h4 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0.le h2.le 3
  have h5 : (2.7182818286 : ℝ) ^ 3 < 81 / 4 := by norm_num
  by_contra hc
  have hc' : (9 / 2 : ℝ) < Real.exp (3 / 2) := not_le.mp hc
  nlinarith [mul_pos (sub_pos.mpr hc') (by linarith : (0 : ℝ) < Real.exp (3 / 2) + 9 / 2)]

/-- log (9/2) ≤ 2: 9/2 ≤ e² -/
theorem log_nine_half_le : Real.log (9 / 2) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.exp_one_gt_d9
  rw [h1]
  nlinarith

theorem rpow_lower {v x : ℝ} (hv : 0 ≤ v) (hx : 9 / 2 ≤ x) : 1 + 3 / 2 * v + v ^ 2 / 2 ≤ x ^ v := by
  have hL := log_nine_half_ge
  have h1 : (9 / 2 : ℝ) ^ v ≤ x ^ v := Real.rpow_le_rpow (by norm_num) hx hv
  have h2 : (9 / 2 : ℝ) ^ v = Real.exp (Real.log (9 / 2) * v) := Real.rpow_def_of_pos (by norm_num) v
  have h3 := Real.quadratic_le_exp_of_nonneg (x := Real.log (9 / 2) * v) (mul_nonneg (by linarith) hv)
  have h4 : 3 / 2 * v ≤ Real.log (9 / 2) * v := mul_le_mul_of_nonneg_right hL hv
  have h5 : (3 / 2 * v) ^ 2 ≤ (Real.log (9 / 2) * v) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
  have h6 : 0 ≤ v ^ 2 := sq_nonneg v
  nlinarith

theorem psiV2_nonpos {v x : ℝ} (hv : 0 < v) (hx : 9 / 2 ≤ x) : psiV2 v x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have e1 : x ^ (-v - 1 - 1 - 1) = x ^ ((-1 : ℝ) - 1 - 1) * x ^ (-v) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hX : 0 < x ^ ((-1 : ℝ) - 1 - 1) := Real.rpow_pos_of_pos hx0 _
  have hY := rpow_lower hv.le hx
  have hY0 : 0 < x ^ v := Real.rpow_pos_of_pos hx0 _
  have hE : x ^ (-v) * x ^ v = 1 := by
    rw [← Real.rpow_add hx0]
    simp
  have hE0 : 0 < x ^ (-v) := Real.rpow_pos_of_pos hx0 _
  unfold psiV2
  rw [e1]
  generalize x ^ ((-1 : ℝ) - 1 - 1) = X at hX ⊢
  generalize x ^ (-v) = E at hE hE0 ⊢
  generalize x ^ v = Y at hY hY0 hE
  have h1 : (1 + v) * (2 + v) ≤ 2 * Y := by nlinarith [sq_nonneg v]
  have h2 : (1 + v) * (2 + v) * E ≤ 2 * Y * E := mul_le_mul_of_nonneg_right h1 hE0.le
  have h3 : (1 + v) * (2 + v) * E - 2 ≤ 0 := by nlinarith
  have h4 : ((1 + v) * (2 + v) * E - 2) * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h3 hX.le
  nlinarith

theorem psiV_concave {v : ℝ} (hv : 0 < v) : ConcaveOn ℝ (Set.Ici (9 / 2)) (psiV v) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := psiV1 v) (f'' := psiV2 v) (convex_Ici _) ?_ ?_ ?_ ?_
  · intro x hx
    have h : (9 / 2 : ℝ) ≤ x := Set.mem_Ici.mp hx
    exact (hasDerivAt_psiV v (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have h : (9 / 2 : ℝ) ≤ x := Set.mem_Ici.mp (interior_subset hx)
    exact (hasDerivAt_psiV v (by linarith)).hasDerivWithinAt
  · intro x hx
    have h : (9 / 2 : ℝ) ≤ x := Set.mem_Ici.mp (interior_subset hx)
    exact (hasDerivAt_psiV1 v (by linarith)).hasDerivWithinAt
  · intro x hx
    exact psiV2_nonpos hv (Set.mem_Ici.mp (interior_subset hx))

theorem psi_mid {v n h : ℝ} (hv : 0 < v) (hn : 5 ≤ n) (h0 : 0 ≤ h) (h1 : h ≤ 1 / 2) :
    psiV v (n + h) + psiV v (n - h) ≤ 2 * psiV v n := by
  have hc := (psiV_concave hv).2 (Set.mem_Ici.mpr (by linarith : (9 / 2 : ℝ) ≤ n + h))
    (Set.mem_Ici.mpr (by linarith : (9 / 2 : ℝ) ≤ n - h)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have e : (1 / 2 : ℝ) • (n + h) + (1 / 2 : ℝ) • (n - h) = n := by
    simp only [smul_eq_mul]
    ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  linarith

/-- THE MIDPOINT RULE, ONE WAY: `Ψ(n + 1/2) - Ψ(n - 1/2) ≤ ψ(n)` -/
theorem Psi_step {v n : ℝ} (hv : 0 < v) (hn : 5 ≤ n) : PsiV v (n + 1 / 2) - PsiV v (n - 1 / 2) ≤ psiV v n := by
  have hd : ∀ h ∈ Set.Icc (0 : ℝ) (1 / 2), HasDerivAt (fun h : ℝ => PsiV v (n + h) - PsiV v (n - h) - 2 * h * psiV v n)
      (psiV v (n + h) + psiV v (n - h) - 2 * psiV v n) h := by
    intro h hh
    have h1 : HasDerivAt (fun h : ℝ => PsiV v (n + h)) (psiV v (n + h)) h :=
      HasDerivAt.comp_const_add n h (hasDerivAt_PsiV hv (by linarith [hh.1]))
    have h2 : HasDerivAt (fun h : ℝ => PsiV v (n - h)) (-psiV v (n - h)) h :=
      HasDerivAt.comp_const_sub n h (hasDerivAt_PsiV hv (by linarith [hh.2]))
    have h3 : HasDerivAt (fun h : ℝ => 2 * h * psiV v n) (2 * psiV v n) h := by
      have h4 : HasDerivAt (fun h : ℝ => 2 * h) (2 * 1) h := (hasDerivAt_id' h).const_mul 2
      have h5 : HasDerivAt (fun h : ℝ => 2 * h * psiV v n) (2 * 1 * psiV v n) h := h4.mul_const (psiV v n)
      rw [mul_one] at h5
      exact h5
    have h6 := (h1.fun_sub h2).fun_sub h3
    have e : psiV v (n + h) + psiV v (n - h) - 2 * psiV v n = psiV v (n + h) - -psiV v (n - h) - 2 * psiV v n := by ring
    rw [e]
    exact h6
  have anti : AntitoneOn (fun h : ℝ => PsiV v (n + h) - PsiV v (n - h) - 2 * h * psiV v n) (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun h : ℝ => psiV v (n + h) + psiV v (n - h) - 2 * psiV v n)
      (convex_Icc _ _) ?_ ?_ ?_
    · intro h hh
      exact (hd h hh).continuousAt.continuousWithinAt
    · intro h hh
      exact (hd h (interior_subset hh)).hasDerivWithinAt
    · intro h hh
      have hm := interior_subset hh
      have := psi_mid hv hn hm.1 hm.2
      show psiV v (n + h) + psiV v (n - h) - 2 * psiV v n ≤ 0
      linarith
  have h7 := anti (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [add_zero, sub_zero, mul_zero, zero_mul] at h7
  linarith

/-- the sequence T -/
def TV (v : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, psiV v ((k : ℝ) + 1) + (((M : ℝ) + 1 / 2) ^ (-v) - 1) / v + Real.log ((M : ℝ) + 1 / 2)

theorem TV_step {v : ℝ} (hv : 0 < v) (M : ℕ) (hM : 4 ≤ M) : TV v M ≤ TV v (M + 1) := by
  have hM' : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h := Psi_step hv (n := (M : ℝ) + 1) (by linarith)
  have e1 : (M : ℝ) + 1 + 1 / 2 = ((M + 1 : ℕ) : ℝ) + 1 / 2 := by
    push_cast
    ring
  have e2 : (M : ℝ) + 1 - 1 / 2 = (M : ℝ) + 1 / 2 := by ring
  rw [e1, e2] at h
  unfold PsiV at h
  unfold TV
  rw [Finset.sum_range_succ]
  have e3 : ∀ y : ℝ, (y - 1) / v = -((-1 / v) * y) - 1 / v := by
    intro y
    ring
  rw [e3, e3]
  linarith

theorem TV_mono {v : ℝ} (hv : 0 < v) (M : ℕ) (hM : 4 ≤ M) : TV v 4 ≤ TV v M := by
  induction M, hM using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (TV_step hv k hk)

/-- the Dirichlet series at 1 + v, on the reals -/
def Zr (v : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + v)

theorem Zr_summable {v : ℝ} (hv : 0 < v) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + v)) := by
  have hs : 1 < 1 + v := by linarith
  exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)

theorem psiV_eq (v : ℝ) {x : ℝ} (hx : 0 < x) : psiV v x = 1 / x ^ (1 + v) - x⁻¹ := by
  unfold psiV
  rw [Real.rpow_neg_one, show -v - 1 = -(1 + v) by ring, Real.rpow_neg hx.le, one_div]

theorem harmonic_cast (M : ℕ) : ((harmonic M : ℚ) : ℝ) = ∑ k ∈ Finset.range M, ((k : ℝ) + 1)⁻¹ := by
  first
    | (simp [harmonic]; done)
    | (unfold harmonic; push_cast; rfl)

theorem harmonic_sub_log_half :
    Tendsto (fun M : ℕ => ((harmonic M : ℚ) : ℝ) - Real.log ((M : ℝ) + 1 / 2)) atTop (𝓝 Real.eulerMascheroniConstant) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' Real.tendsto_harmonic_sub_log_add_one Real.tendsto_harmonic_sub_log ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have := Real.log_le_log (x := (M : ℝ) + 1 / 2) (y := (M : ℝ) + 1) (by linarith) (by linarith)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have := Real.log_le_log (x := (M : ℝ)) (y := (M : ℝ) + 1 / 2) (by linarith) (by linarith)
    linarith

theorem TV_tendsto {v : ℝ} (hv : 0 < v) : Tendsto (TV v) atTop (𝓝 (Zr v - 1 / v - Real.eulerMascheroniConstant)) := by
  have hP : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) ^ (1 + v)) atTop (𝓝 (Zr v)) :=
    (Zr_summable hv).hasSum.tendsto_sum_nat
  have hf : Tendsto (fun M : ℕ => (M : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun M : ℕ => ((M : ℝ) + 1 / 2) ^ (-v)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hv).comp hf
  have hR1 : Tendsto (fun M : ℕ => (((M : ℝ) + 1 / 2) ^ (-v) - 1) / v) atTop (𝓝 ((0 - 1) / v)) :=
    (hR.sub tendsto_const_nhds).div_const v
  have h := (hP.add hR1).sub harmonic_sub_log_half
  have e : Zr v - 1 / v - Real.eulerMascheroniConstant = Zr v + (0 - 1) / v - Real.eulerMascheroniConstant := by ring
  rw [e]
  refine h.congr ?_
  intro M
  beta_reduce
  unfold TV
  rw [harmonic_cast M]
  have e2 : ∑ k ∈ Finset.range M, psiV v ((k : ℝ) + 1) =
      ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) ^ (1 + v) - ∑ k ∈ Finset.range M, ((k : ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact psiV_eq v (by positivity)
  rw [e2]
  ring

theorem zeta0_re {v : ℝ} (hv : 0 < v) : (riemannZeta₀ (((1 + v : ℝ)) : ℂ)).re = Zr v - 1 / v := by
  have hs : (((1 + v : ℝ)) : ℂ) ≠ 1 := by
    intro h
    have h' : (1 + v : ℝ) = 1 := by exact_mod_cast h
    linarith
  have hre : 1 < ((((1 + v : ℝ)) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have h1 := riemannZeta_eq_inv_sub_add hs
  have h2 : ((Zr v : ℝ) : ℂ) = riemannZeta (((1 + v : ℝ)) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
    unfold Zr
    rw [Complex.ofReal_tsum]
    refine tsum_congr ?_
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow hn]
    first
      | (norm_cast; done)
      | (push_cast; done)
      | (push_cast; rfl)
      | simp
  have h3 : (((1 + v : ℝ)) : ℂ) - 1 = (v : ℂ) := by
    push_cast
    ring
  rw [h3] at h1
  have h4 : riemannZeta₀ (((1 + v : ℝ)) : ℂ) = ((Zr v : ℝ) : ℂ) - ((v : ℂ))⁻¹ := by
    linear_combination (-1 : ℂ) * h2 - h1
  rw [h4, Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

theorem psiV_ge (v : ℝ) {x : ℝ} (hx : 0 < x) : -v * Real.log x / x ≤ psiV v x := by
  have h1 : x ^ (-v - 1) = x ^ (-v) * x⁻¹ := by
    rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
  have h2 : 1 - v * Real.log x ≤ x ^ (-v) := by
    rw [Real.rpow_def_of_pos hx]
    have := Real.add_one_le_exp (Real.log x * (-v))
    nlinarith
  have hi : 0 < x⁻¹ := inv_pos.mpr hx
  have h3 := mul_nonneg (sub_nonneg.mpr h2) hi.le
  unfold psiV
  rw [h1, Real.rpow_neg_one, div_eq_mul_inv]
  nlinarith

theorem last_ge {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 4) :
    -Real.log (9 / 2) + v * Real.log (9 / 2) ^ 2 / 2 - 2 / 9 * (v ^ 2 * Real.log (9 / 2) ^ 3) ≤ ((9 / 2 : ℝ) ^ (-v) - 1) / v := by
  have hL0 := log_nine_half_ge
  have hL2 := log_nine_half_le
  generalize hL : Real.log (9 / 2) = L at hL0 hL2 ⊢
  have hu : 0 ≤ v * L := mul_nonneg hv.le (by linarith)
  have hu1 : |-(v * L)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hu]
    have h8 : v * L ≤ 1 / 4 * 2 := mul_le_mul hv1 hL2 (by linarith) (by norm_num)
    linarith
  have hb := Real.exp_bound hu1 (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (-(v * L)) ^ m / (m.factorial : ℝ) = 1 - v * L + (v * L) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial] <;> ring
  have hb' : |Real.exp (-(v * L)) - (1 - v * L + (v * L) ^ 2 / 2)| ≤ (v * L) ^ 3 * (2 / 9) := by
    rw [← hs]
    refine hb.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg hu]
    congr 1
    norm_num [Nat.factorial]
  have hl := (abs_le.mp hb').1
  have hR : (9 / 2 : ℝ) ^ (-v) = Real.exp (-(v * L)) := by
    rw [Real.rpow_def_of_pos (by norm_num), hL]
    congr 1
    ring
  rw [hR, le_div_iff₀ hv]
  nlinarith

/-- THE HAND BOUND ON T(4) -/
theorem TV_four_ge {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 4) :
    -v * (Real.log 2 + Real.log 3 / 3) + v * Real.log (9 / 2) ^ 2 / 2 - 2 * v ^ 2 ≤ TV v 4 := by
  have hL0 := log_nine_half_ge
  have hL2 := log_nine_half_le
  have e : TV v 4 = psiV v 1 + psiV v 2 + psiV v 3 + psiV v 4 + ((9 / 2 : ℝ) ^ (-v) - 1) / v + Real.log (9 / 2) := by
    have e0 : ((4 : ℕ) : ℝ) + 1 / 2 = 9 / 2 := by norm_num
    unfold TV
    rw [e0]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [e]
  have p1 : psiV v 1 = 0 := by simp [psiV]
  have p2 := psiV_ge v (x := 2) (by norm_num)
  have p3 := psiV_ge v (x := 3) (by norm_num)
  have p4 := psiV_ge v (x := 4) (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hl4] at p4
  have hl := last_ge hv hv1
  have hL3 : Real.log (9 / 2) ^ 3 ≤ 8 :=
    calc Real.log (9 / 2) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) hL2 3
      _ = 8 := by norm_num
  have hq : v ^ 2 * Real.log (9 / 2) ^ 3 ≤ v ^ 2 * 8 := mul_le_mul_of_nonneg_left hL3 (sq_nonneg v)
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  rw [p1]
  nlinarith

/-- THE CONSTANT: log(9/2)²/2 - log 2 - log 3 / 3 ≥ 33/500 -/
theorem constant_ge : (33 / 500 : ℝ) ≤ Real.log (9 / 2) ^ 2 / 2 - Real.log 2 - Real.log 3 / 3 := by
  have hL0 := log_nine_half_ge
  have ha := Real.log_two_lt_d9
  have e : Real.log (9 / 2) = 2 * Real.log 3 - Real.log 2 := by
    rw [show (9 / 2 : ℝ) = 3 ^ 2 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hb : Real.log 3 = (Real.log (9 / 2) + Real.log 2) / 2 := by
    rw [e]
    ring
  rw [hb]
  generalize Real.log (9 / 2) = t at hL0 ⊢
  generalize Real.log 2 = a at ha ⊢
  have ha' : a < 0.6931471808 := ha
  nlinarith [mul_nonneg (sub_nonneg.mpr hL0) (by linarith : (0 : ℝ) ≤ t + 7 / 6)]

/-- ζ₀(1 + v) - γ ≥ T(4), and T(4) is bounded by hand -/
theorem zeta0_sub_ge {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 4) :
    -v * (Real.log 2 + Real.log 3 / 3) + v * Real.log (9 / 2) ^ 2 / 2 - 2 * v ^ 2 ≤
      (riemannZeta₀ (((1 + v : ℝ)) : ℂ)).re - Real.eulerMascheroniConstant := by
  have h1 : TV v 4 ≤ Zr v - 1 / v - Real.eulerMascheroniConstant := by
    refine ge_of_tendsto (TV_tendsto hv) ?_
    filter_upwards [eventually_ge_atTop 4] with M hM
    exact TV_mono hv M hM
  have h2 := TV_four_ge hv hv1
  rw [zeta0_re hv]
  linarith

/-- Re ζ₀'(1) ≥ 3/50 -/
theorem deriv_bound : (3 / 50 : ℝ) ≤ (deriv riemannZeta₀ 1).re := by
  have hd0 : HasDerivAt riemannZeta₀ (deriv riemannZeta₀ 1) (1 : ℂ) := (differentiable_riemannZeta₀ 1).hasDerivAt
  have hd : HasDerivAt riemannZeta₀ (deriv riemannZeta₀ 1) ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]
    exact hd0
  have hr := hd.real_of_complex
  have hs := hr.tendsto_slope_zero_right
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 500 by norm_num)] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 / 500 := ht.2
  have h1 := zeta0_sub_ge ht0 (by linarith)
  have hc := constant_ge
  have h0 : (riemannZeta₀ ((1 : ℝ) : ℂ)).re = Real.eulerMascheroniConstant := by
    rw [Complex.ofReal_one, riemannZeta₀_one]
    exact Complex.ofReal_re _
  show (3 / 50 : ℝ) ≤ t⁻¹ • ((riemannZeta₀ (((1 + t : ℝ)) : ℂ)).re - (riemannZeta₀ ((1 : ℝ) : ℂ)).re)
  rw [h0, smul_eq_mul, inv_mul_eq_div, le_div_iff₀ ht0]
  generalize (riemannZeta₀ (((1 + t : ℝ)) : ℂ)).re - Real.eulerMascheroniConstant = X at h1 ⊢
  have h2 : t * (33 / 500) ≤ t * (Real.log (9 / 2) ^ 2 / 2 - Real.log 2 - Real.log 3 / 3) := mul_le_mul_of_nonneg_left hc ht0.le
  have h3 : t ^ 2 ≤ t * (1 / 500) := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  nlinarith

/-- **THE BOUND ON γ_1** -/
theorem stieltjes_one_lt : (stieltjes 1).re < -1 / 20 := by
  have h := deriv_bound
  have e : stieltjes 1 = -deriv riemannZeta₀ 1 := by
    unfold stieltjes
    rw [iteratedDeriv_one]
    simp
  rw [e, Complex.neg_re]
  linarith

/-- **λ_2 > 0, THE STANDARD AXIOMS ONLY.** A single rung; not Li's criterion. -/
theorem liCoeff_two_pos : 0 < LiWeil.LiCoeff 2 :=
  liCoeff_two_pos_of_stieltjes_one stieltjes_one_lt

end KeiperTwo
end SIDEExplicitFormula
