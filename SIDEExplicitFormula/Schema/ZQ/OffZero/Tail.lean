/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Tail.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3)(b), relay data/b737_offlinezero_plan.txt (d) S5b) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S5b, THE LATTICE TRUNCATION OF `θ − 1` AND ITS TAIL. The theta of `Q0` (Theta.lean :20) cut to the box `|m|, |n| ≤ 14`, which holds `0`, so
`thetaTr − 1` is the truncation of `θ − 1`. Off the box `qR ≥ 225/2` (`half_le_qR`), so on `t ≥ 1` the tail is at most
`e^{−π(u − cc/2)·225/2} · θ(cc/2)`, and `θ(cc/2) ≤ 10` from the functional equation at `x = 2` and `thetaU_sub_one` alone: no one-dimensional
sum is bounded. The tail is below `1e-14` for every `t ≥ 1`. No value of `zqFn` is computed here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.FEPair
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- The truncation box `|m|, |n| ≤ 14`. -/
def trBox : Finset (ℤ × ℤ) := Finset.Icc (-14 : ℤ) 14 ×ˢ Finset.Icc (-14 : ℤ) 14

/-- The theta truncated to the box; `thetaTr u − 1` is the truncation of `θ − 1`. -/
def thetaTr (u : ℝ) : ℝ := ∑ p ∈ trBox, Real.exp (-(Real.pi * u) * qR p)

theorem zero_mem_trBox : (0 : ℤ × ℤ) ∈ trBox := by
  simp only [trBox, Finset.mem_product, Finset.mem_Icc]
  norm_num

/-- Off the box, `qR ≥ 225/2`. -/
theorem tail_qR {p : ℤ × ℤ} (hp : p ∉ trBox) : 225 / 2 ≤ qR p := by
  have hsq : (225 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    by_contra hlt
    push_neg at hlt
    have hz : p.1 ^ 2 + p.2 ^ 2 < 225 := by exact_mod_cast hlt
    apply hp
    simp only [trBox, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  linarith [half_le_qR p]

theorem thetaU_anti {u v : ℝ} (hv : 0 < v) (h : v ≤ u) : thetaU u ≤ thetaU v := by
  have hπ := Real.pi_pos
  unfold thetaU
  refine Summable.tsum_le_tsum (fun p => ?_) (lattice_summable (mul_pos hπ (hv.trans_le h))) (lattice_summable (mul_pos hπ hv))
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr h)) (qR_nonneg p)]

/-- The functional equation at `x = 2`: `θ(cc/2) = 2 θ(2cc)`. -/
theorem thetaU_half : thetaU (cc / 2) = 2 * thetaU (cc * 2) := by
  have h := thetaC_feq (show (0 : ℝ) < 2 by norm_num)
  rw [Real.rpow_one, one_mul, smul_eq_mul] at h
  unfold thetaC at h
  rw [← Complex.ofReal_mul] at h
  have h2 := Complex.ofReal_injective h
  rw [← h2]
  congr 1
  ring

theorem cc_gt : 2 / 5 < cc := by
  have h5 : Real.sqrt 23 < 5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hm : cc * Real.sqrt 23 = 2 := by
    unfold cc
    field_simp
  nlinarith [cc_pos]

theorem q_le : Real.exp (-Real.pi * cc) ≤ 2 / 5 := by
  have hpc : 6 / 5 < Real.pi * cc := by
    nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_three) (sub_pos.mpr cc_gt), cc_gt, Real.pi_gt_three]
  have he : (8 / 5 : ℝ) ≤ Real.exp (3 / 5) := by linarith [Real.add_one_le_exp (3 / 5 : ℝ)]
  have he2 : (5 / 2 : ℝ) ≤ Real.exp (Real.pi * cc) := by
    have e : Real.exp (6 / 5) = Real.exp (3 / 5) * Real.exp (3 / 5) := by
      rw [← Real.exp_add]
      norm_num
    have h1 : Real.exp (6 / 5) ≤ Real.exp (Real.pi * cc) := Real.exp_le_exp.mpr hpc.le
    have h2 : (8 / 5 : ℝ) * (8 / 5) ≤ Real.exp (3 / 5) * Real.exp (3 / 5) := mul_le_mul he he (by norm_num) (Real.exp_pos _).le
    linarith
  have hm : Real.exp (-Real.pi * cc) * Real.exp (Real.pi * cc) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-Real.pi * cc), mul_nonneg (Real.exp_pos (-Real.pi * cc)).le (sub_nonneg.mpr he2)]

/-- `θ(cc/2) ≤ 10`. -/
theorem thetaU_half_le : thetaU (cc / 2) ≤ 10 := by
  have hcc := cc_pos
  have hv : 0 < cc / 2 := by positivity
  have h1 := (thetaU_sub_one hcc (show cc ≤ cc * 2 by linarith)).2
  have e : Real.exp (-Real.pi * (cc * 2 - cc)) = Real.exp (-Real.pi * cc) := by
    congr 1
    ring
  rw [e] at h1
  have h2 := thetaU_anti hv (show cc / 2 ≤ cc by linarith)
  have hθ0 : 0 ≤ thetaU (cc / 2) := by linarith [(thetaU_sub_one hv le_rfl).1]
  have hq0 := Real.exp_pos (-Real.pi * cc)
  have h3 := mul_le_mul_of_nonneg_left h2 hq0.le
  have h4 := mul_le_mul_of_nonneg_right q_le hθ0
  linarith [thetaU_half]

/-- The tail off the box, for `u ≥ cc`. -/
theorem tail_le {u : ℝ} (hu : cc ≤ u) :
    0 ≤ thetaU u - thetaTr u ∧
      thetaU u - thetaTr u ≤ Real.exp (-Real.pi * (u - cc / 2) * (225 / 2)) * thetaU (cc / 2) := by
  have hπ := Real.pi_pos
  have hcc := cc_pos
  have hv : 0 < cc / 2 := by positivity
  have hu0 : 0 < u := hcc.trans_le hu
  set f : ℤ × ℤ → ℝ := fun p => Real.exp (-(Real.pi * u) * qR p) with hf
  have hfs : Summable f := lattice_summable (mul_pos hπ hu0)
  have hin : Summable (fun p : ℤ × ℤ => if p ∈ trBox then f p else 0) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hfs
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
  have hd0 : ∀ p : ℤ × ℤ, 0 ≤ (if p ∈ trBox then 0 else f p) := by
    intro p
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hds : Summable (fun p : ℤ × ℤ => if p ∈ trBox then 0 else f p) := by
    refine Summable.of_nonneg_of_le hd0 (fun p => ?_) hfs
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hsplit : thetaU u - thetaTr u = ∑' p : ℤ × ℤ, (if p ∈ trBox then 0 else f p) := by
    have e1 : thetaU u = ∑' p : ℤ × ℤ, ((if p ∈ trBox then f p else 0) + (if p ∈ trBox then 0 else f p)) := by
      show ∑' p, f p = _
      congr 1
      funext p
      split_ifs <;> simp
    have e2 : ∑' p : ℤ × ℤ, (if p ∈ trBox then f p else 0) = thetaTr u := by
      rw [tsum_eq_sum (s := trBox) (fun p hp => if_neg hp)]
      exact Finset.sum_congr rfl (fun p hp => if_pos hp)
    rw [e1, hin.tsum_add hds, e2]
    ring
  have hgs : Summable (fun p : ℤ × ℤ =>
      Real.exp (-Real.pi * (u - cc / 2) * (225 / 2)) * Real.exp (-(Real.pi * (cc / 2)) * qR p)) :=
    (lattice_summable (mul_pos hπ hv)).mul_left _
  have hle : ∀ p : ℤ × ℤ, (if p ∈ trBox then 0 else f p)
      ≤ Real.exp (-Real.pi * (u - cc / 2) * (225 / 2)) * Real.exp (-(Real.pi * (cc / 2)) * qR p) := by
    intro p
    split_ifs with hp
    · positivity
    · have hQ := tail_qR hp
      show Real.exp (-(Real.pi * u) * qR p) ≤ _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg hπ.le (show (0 : ℝ) ≤ u - cc / 2 by linarith)) (sub_nonneg.mpr hQ)]
  constructor
  · rw [hsplit]
    exact tsum_nonneg hd0
  · rw [hsplit]
    calc ∑' p : ℤ × ℤ, (if p ∈ trBox then 0 else f p)
        ≤ ∑' p : ℤ × ℤ, Real.exp (-Real.pi * (u - cc / 2) * (225 / 2)) * Real.exp (-(Real.pi * (cc / 2)) * qR p) :=
          Summable.tsum_le_tsum hle hds hgs
      _ = Real.exp (-Real.pi * (u - cc / 2) * (225 / 2)) * thetaU (cc / 2) := tsum_mul_left

/-- **S5b**: on `t ≥ 1` the truncation misses `θ` by less than `1e-14`. -/
theorem zq_theta_tail {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ thetaU (cc * t) - thetaTr (cc * t) ∧ thetaU (cc * t) - thetaTr (cc * t) < 1e-14 := by
  have hcc := cc_pos
  have hu : cc ≤ cc * t := by nlinarith
  obtain ⟨h0, h1⟩ := tail_le hu
  refine ⟨h0, lt_of_le_of_lt h1 ?_⟩
  have hw : 1 / 5 < cc * t - cc / 2 := by linarith [cc_gt]
  have hE : Real.exp (-Real.pi * (cc * t - cc / 2) * (225 / 2)) ≤ Real.exp (-67) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_three) (sub_pos.mpr hw), Real.pi_gt_three]
  have hE67 : (2 : ℝ) ^ 67 ≤ Real.exp 67 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h := pow_le_pow_left₀ (by norm_num) h2 67
    rw [← Real.exp_nat_mul] at h
    have e : ((67 : ℕ) : ℝ) * 1 = 67 := by norm_num
    rwa [e] at h
  have hx : Real.exp (-67) * Real.exp 67 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hx0 := Real.exp_pos (-67)
  have hθ0 : 0 ≤ thetaU (cc / 2) := by linarith [(thetaU_sub_one (show 0 < cc / 2 by positivity) le_rfl).1]
  calc Real.exp (-Real.pi * (cc * t - cc / 2) * (225 / 2)) * thetaU (cc / 2)
      ≤ Real.exp (-67) * 10 := mul_le_mul hE thetaU_half_le hθ0 hx0.le
    _ < 1e-14 := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hE67)]

/-- **S5b** on the theta of `zqPair`: `θ − 1` against its truncation `thetaTr − 1`, within `1e-14` on `t ≥ 1`. -/
theorem zq_thetaC_tail {t : ℝ} (ht : 1 ≤ t) :
    ‖(thetaC t - 1) - ((thetaTr (cc * t) - 1 : ℝ) : ℂ)‖ < 1e-14 := by
  obtain ⟨h0, h1⟩ := zq_theta_tail ht
  have e : (thetaC t - 1) - ((thetaTr (cc * t) - 1 : ℝ) : ℂ) = ((thetaU (cc * t) - thetaTr (cc * t) : ℝ) : ℂ) := by
    unfold thetaC
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg h0]
  exact h1

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
