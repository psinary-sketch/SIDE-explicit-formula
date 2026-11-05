/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Strip.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (4) G3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G3, THE FAR CIRCLE'S BOUND. For `t ≥ 1`, `0 ≤ θ(t) − 1 ≤ 10 e^(λ/2) e^(−λ t)` (FEPair.lean :62 at `v = cc/2`, Tail.lean :83), so for `Re w ≤ 4`
`‖lamM w‖ ≤ 10 e^(λ/2) ∫_0^∞ t^3 e^(−λ t) dt = 10 e^(λ/2) · 6/λ^4 ≤ 58`, a closed form (Mathlib `Real.integral_rpow_mul_exp_neg_mul_Ioi`);
on the sphere `|w − cI| = 3` both `w` and `1 − w` have real part at most `7/2` and `|w|, |1 − w| ≥ 13`, so `‖lamF w‖ ≤ 120`. Cruder than the plan's
`B_3 = 7.8004` (data/b742_s6_plan.txt (3)(1)); the remainder it gives is printed at the bank. And `lamM (conj w) = conj (lamM w)`.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Frame
import SIDEExplicitFormula.Schema.ZQ.OffZero.Elem
import SIDEExplicitFormula.Schema.ZQ.OffZero.Tail
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set MeasureTheory Metric ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- `0 ≤ θ(t) − 1 ≤ 10 e^(λ/2) e^(−λ t)` for `t ≥ 1`. -/
theorem theta_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ thetaU (cc * t) - 1 ∧ thetaU (cc * t) - 1 ≤ 10 * Real.exp (lam / 2) * Real.exp (-(lam * t)) := by
  have hcc := cc_pos
  obtain ⟨h0, h1⟩ := thetaU_sub_one (u := cc * t) (v := cc / 2) (by positivity) (by nlinarith)
  refine ⟨h0, h1.trans ?_⟩
  have e : Real.exp (-Real.pi * (cc * t - cc / 2)) = Real.exp (lam / 2) * Real.exp (-(lam * t)) := by
    rw [← Real.exp_add, ← pi_mul_cc]
    congr 1
    ring
  rw [e]
  have hp : 0 ≤ Real.exp (lam / 2) * Real.exp (-(lam * t)) := by positivity
  calc Real.exp (lam / 2) * Real.exp (-(lam * t)) * thetaU (cc / 2) ≤ Real.exp (lam / 2) * Real.exp (-(lam * t)) * 10 :=
        mul_le_mul_of_nonneg_left thetaU_half_le hp
    _ = 10 * Real.exp (lam / 2) * Real.exp (-(lam * t)) := by ring

theorem norm_thetaC_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    ‖thetaC t - 1‖ ≤ 10 * Real.exp (lam / 2) * Real.exp (-(lam * t)) := by
  obtain ⟨h0, h1⟩ := theta_sub_one_le ht
  have e : thetaC t - 1 = ((thetaU (cc * t) - 1 : ℝ) : ℂ) := by
    unfold thetaC
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg h0]
  exact h1

theorem norm_lamM_integrand_le {w : ℂ} (hw : w.re ≤ 4) {t : ℝ} (ht : 1 < t) :
    ‖(t : ℂ) ^ (w - 1) * (thetaC t - 1)‖ ≤ 10 * Real.exp (lam / 2) * (t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t))) := by
  have ht0 : 0 < t := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have h1 : t ^ (w.re - 1) ≤ t ^ ((4 : ℝ) - 1) := Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
  have h2 := norm_thetaC_sub_one_le ht.le
  calc t ^ (w.re - 1) * ‖thetaC t - 1‖ ≤ t ^ ((4 : ℝ) - 1) * (10 * Real.exp (lam / 2) * Real.exp (-(lam * t))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
    _ = 10 * Real.exp (lam / 2) * (t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t))) := by ring

theorem gamma4_integrableOn : IntegrableOn (fun t : ℝ => t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t))) (Ioi 0) := by
  have hk : IntegrableOn (fun t : ℝ => t ^ (3 : ℝ) * Real.exp (-lam * t ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos lam_pos
  refine hk.congr_fun (fun t _ => ?_) measurableSet_Ioi
  norm_num [Real.rpow_one, neg_mul]

theorem gamma4_integral : ∫ t in Ioi (0 : ℝ), t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t)) = 6 / lam ^ 4 := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) lam_pos]
  have hG : Real.Gamma 4 = 6 := by
    have h := Real.Gamma_nat_eq_factorial 3
    norm_num [Nat.factorial] at h
    exact h
  rw [hG, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, one_pow]
  ring

/-- `‖lamM w‖ ≤ 10 e^(λ/2) · 6/λ^4` for `Re w ≤ 4`. -/
theorem norm_lamM_le {w : ℂ} (hw : w.re ≤ 4) : ‖lamM w‖ ≤ 10 * Real.exp (lam / 2) * (6 / lam ^ 4) := by
  have hI := gamma4_integrableOn
  have hI1 : IntegrableOn (fun t : ℝ => 10 * Real.exp (lam / 2) * (t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t)))) (Ioi 1) :=
    (hI.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
  rw [lamM_eq]
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (thetaC t - 1)‖
      ≤ ∫ t in Ioi (1 : ℝ), 10 * Real.exp (lam / 2) * (t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t))) :=
        norm_integral_le_of_norm_le hI1 (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => norm_lamM_integrand_le hw ht)
    _ ≤ ∫ t in Ioi (0 : ℝ), 10 * Real.exp (lam / 2) * (t ^ ((4 : ℝ) - 1) * Real.exp (-(lam * t))) := by
        refine setIntegral_mono_set (hI.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
          (Ioi_subset_Ioi zero_le_one).eventuallyLE
        have ht0 : (0 : ℝ) < t := ht
        exact mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
    _ = 10 * Real.exp (lam / 2) * (6 / lam ^ 4) := by
        rw [integral_const_mul, gamma4_integral]

theorem lamM_bound_numeric : 10 * Real.exp (lam / 2) * (6 / lam ^ 4) ≤ 58 := by
  have he : Real.exp (lam / 2) ≤ 2.7182818286 :=
    (Real.exp_le_exp.2 (by linarith [lam_le])).trans Real.exp_one_lt_d9.le
  have hl4 : (13 / 10 : ℝ) ^ 4 ≤ lam ^ 4 := pow_le_pow_left₀ (by norm_num) lam_gt.le 4
  have h6 : 6 / lam ^ 4 ≤ 6 / (13 / 10 : ℝ) ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl4
  calc 10 * Real.exp (lam / 2) * (6 / lam ^ 4) ≤ 10 * 2.7182818286 * (6 / (13 / 10 : ℝ) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) h6 (by positivity) (by norm_num)
    _ ≤ 58 := by norm_num

theorem norm_lamM_le_58 {w : ℂ} (hw : w.re ≤ 4) : ‖lamM w‖ ≤ 58 :=
  (norm_lamM_le hw).trans lamM_bound_numeric

/-- **G3**: `‖lamF w‖ ≤ 120` on the far circle `|w − cI| = 3`. -/
theorem lamF_sphere_le : ∀ w ∈ sphere cI 3, ‖lamF w‖ ≤ 120 := by
  intro w hw
  have him := im_ge_of_mem_closedBall_cI (sphere_subset_closedBall hw)
  have hre : |w.re - 1 / 2| ≤ 3 := by
    rw [mem_sphere, dist_eq_norm] at hw
    have h := Complex.abs_re_le_norm (w - cI)
    rw [hw, Complex.sub_re] at h
    exact h
  have hre' := abs_le.1 hre
  have h1 : ‖lamM w‖ ≤ 58 := norm_lamM_le_58 (by linarith)
  have h2 : ‖lamM (1 - w)‖ ≤ 58 := norm_lamM_le_58 (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hw1 : 13 ≤ ‖w‖ := him.trans ((le_abs_self _).trans (Complex.abs_im_le_norm w))
  have hw2 : 13 ≤ ‖1 - w‖ := by
    have h := Complex.abs_im_le_norm (1 - w)
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    linarith [le_abs_self w.im]
  have h3 : ‖1 / (w * (1 - w))‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, div_le_one (mul_pos (by linarith) (by linarith))]
    nlinarith [mul_le_mul hw1 hw2 (by norm_num) (by linarith)]
  rw [lamF_eq_split]
  have h4 := norm_sub_le (lamM w + lamM (1 - w)) (1 / (w * (1 - w)))
  have h5 := norm_add_le (lamM w) (lamM (1 - w))
  linarith

/-- `lamM (conj w) = conj (lamM w)`: the theta is real on the half-line. -/
theorem lamM_conj (w : ℂ) : lamM (conj w) = conj (lamM w) := by
  rw [lamM_eq, lamM_eq, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_pos.ne
  have hth : conj (thetaC t - 1) = thetaC t - 1 := by
    unfold thetaC
    rw [map_sub, Complex.conj_ofReal, map_one]
  simp only [map_mul]
  rw [hth, show conj w - 1 = conj (w - 1) by rw [map_sub, map_one], Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
