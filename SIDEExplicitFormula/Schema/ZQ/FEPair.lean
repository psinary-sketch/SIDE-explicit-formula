/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/FEPair.lean
THIS PROGRAMME'S WORK (act b730, ruling (R340)(4), group C of relay data/b730_continuation_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FE-PAIR. With `cc = 2/√23` and `thetaC t = thetaU (cc t)`, `thetaC (1/t) = t · thetaC t`; `thetaC` is continuous on `(0, ∞)` and tends to `1`
faster than any power: Mathlib's `WeakFEPair` with `f = g = thetaC`, `k = 1`, `ε = 1`, `f₀ = g₀ = 1`. Nothing here proves RH or GRH or locates
any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Theta
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

noncomputable section

open Filter Topology Asymptotics

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- `2/√23`. -/
def cc : ℝ := 2 / Real.sqrt 23

theorem sqrt23_pos : 0 < Real.sqrt 23 := Real.sqrt_pos.mpr (by norm_num)

theorem cc_pos : 0 < cc := div_pos two_pos sqrt23_pos

theorem cc_sq : cc * cc * 23 = 4 := by
  unfold cc
  have h : Real.sqrt 23 * Real.sqrt 23 = 23 := Real.mul_self_sqrt (by norm_num)
  have h1 : 2 / Real.sqrt 23 * (2 / Real.sqrt 23) * 23 = 4 * 23 / (Real.sqrt 23 * Real.sqrt 23) := by
    ring
  rw [h1, h]
  norm_num

/-- The theta in the variable of the functional equation, as a complex number. -/
def thetaC (t : ℝ) : ℂ := ((thetaU (cc * t) : ℝ) : ℂ)

theorem thetaU_continuousOn : ContinuousOn thetaU (Set.Ioi 0) := by
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  have hx0 : 0 < x := hx
  have hπ := Real.pi_pos
  have hc : ContinuousOn thetaU (Set.Ioi (x / 2)) := by
    show ContinuousOn (fun u : ℝ => ∑' p : ℤ × ℤ, Real.exp (-(Real.pi * u) * qR p)) _
    refine continuousOn_tsum (u := fun p : ℤ × ℤ => Real.exp (-(Real.pi * (x / 2)) * qR p)) (fun p => ?_)
      (lattice_summable (mul_pos hπ (by linarith))) (fun p u hu => ?_)
    · exact Continuous.continuousOn (by fun_prop)
    · have hu' : x / 2 < u := hu
      have hQ := qR_nonneg p
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr hu'.le)) hQ]
  exact hc.continuousAt (Ioi_mem_nhds (by linarith))

theorem thetaC_continuousOn : ContinuousOn thetaC (Set.Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => thetaU (cc * t)) (Set.Ioi 0) :=
    thetaU_continuousOn.comp (by fun_prop : Continuous fun t : ℝ => cc * t).continuousOn
      (fun t ht => mul_pos cc_pos ht)
  exact Complex.continuous_ofReal.comp_continuousOn h

/-- `thetaU` less its constant term, on both sides. -/
theorem thetaU_sub_one {u v : ℝ} (hv : 0 < v) (h : v ≤ u) :
    0 ≤ thetaU u - 1 ∧ thetaU u - 1 ≤ Real.exp (-Real.pi * (u - v)) * thetaU v := by
  have hπ := Real.pi_pos
  have hu : 0 < u := lt_of_lt_of_le hv h
  set f : ℤ × ℤ → ℝ := fun p => Real.exp (-(Real.pi * u) * qR p) with hf
  have hfs : Summable f := lattice_summable (mul_pos hπ hu)
  have hgs : Summable (fun p : ℤ × ℤ => Real.exp (-Real.pi * (u - v)) * Real.exp (-(Real.pi * v) * qR p)) :=
    (lattice_summable (mul_pos hπ hv)).mul_left _
  have hsplit := hfs.tsum_eq_add_tsum_ite (0 : ℤ × ℤ)
  have hf0 : f 0 = 1 := by simp [hf, qR_zero]
  have hd0 : ∀ p : ℤ × ℤ, 0 ≤ (if p = 0 then 0 else f p) := by
    intro p
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hds : Summable (fun p : ℤ × ℤ => if p = 0 then 0 else f p) := by
    refine Summable.of_nonneg_of_le hd0 (fun p => ?_) hfs
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hle : ∀ p : ℤ × ℤ, (if p = 0 then 0 else f p)
      ≤ Real.exp (-Real.pi * (u - v)) * Real.exp (-(Real.pi * v) * qR p) := by
    intro p
    split_ifs with hp
    · positivity
    · have hQ := one_le_qR hp
      show Real.exp (-(Real.pi * u) * qR p) ≤ _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr h)) (sub_nonneg.mpr hQ)]
  have heq : thetaU u - 1 = ∑' p : ℤ × ℤ, if p = 0 then 0 else f p := by
    have : thetaU u = ∑' p, f p := rfl
    rw [this, hsplit, hf0]
    ring
  constructor
  · rw [heq]
    exact tsum_nonneg hd0
  · rw [heq]
    calc ∑' p : ℤ × ℤ, (if p = 0 then 0 else f p)
        ≤ ∑' p : ℤ × ℤ, Real.exp (-Real.pi * (u - v)) * Real.exp (-(Real.pi * v) * qR p) :=
          Summable.tsum_le_tsum hle hds hgs
      _ = Real.exp (-Real.pi * (u - v)) * thetaU v := tsum_mul_left

theorem thetaC_decay (r : ℝ) : (fun x : ℝ => thetaC x - 1) =O[atTop] (fun x : ℝ => x ^ r) := by
  have hπ := Real.pi_pos
  have hcc := cc_pos
  have hlo := (isLittleO_exp_neg_mul_rpow_atTop (a := Real.pi * cc) (mul_pos hπ hcc) r).isBigO
  refine IsBigO.trans ?_ hlo
  refine IsBigO.of_bound (thetaU cc * Real.exp (Real.pi * cc)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hle : cc ≤ cc * x := by nlinarith
  obtain ⟨h0, h1⟩ := thetaU_sub_one hcc hle
  have e : thetaC x - 1 = ((thetaU (cc * x) - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    rfl
  rw [e, Complex.norm_real, Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (-Real.pi * (cc * x - cc)) = Real.exp (Real.pi * cc) * Real.exp (-(Real.pi * cc) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at h1
  calc thetaU (cc * x) - 1 ≤ Real.exp (Real.pi * cc) * Real.exp (-(Real.pi * cc) * x) * thetaU cc := h1
    _ = thetaU cc * Real.exp (Real.pi * cc) * Real.exp (-(Real.pi * cc) * x) := by ring

/-- **The functional equation of the theta.** -/
theorem thetaC_feq {x : ℝ} (hx : 0 < x) : thetaC (1 / x) = (1 * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • thetaC x := by
  have hcc := cc_pos
  have ha : 0 < cc * x := mul_pos hcc hx
  have hb : 0 < cc * (1 / x) := mul_pos hcc (one_div_pos.mpr hx)
  have e : 4 / (23 * (cc * x)) = cc * (1 / x) := by
    have hx0 := hx.ne'
    rw [div_eq_iff (mul_ne_zero (by norm_num) ha.ne')]
    have h6 : cc * (1 / x) * (23 * (cc * x)) = cc * cc * 23 := by
      field_simp
      try ring
    rw [h6, cc_sq]
  have hinv := thetaU_inversion ha
  rw [e] at hinv
  have e3 : (cc * x) ^ (1 / 2 : ℝ) = (cc * (1 / x)) ^ (1 / 2 : ℝ) * x := by
    have h5 : cc * x = (cc * (1 / x)) * x ^ 2 := by
      have hx0 := hx.ne'
      field_simp
      try ring
    rw [h5, Real.mul_rpow hb.le (sq_nonneg x)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  rw [e3] at hinv
  have hB : (cc * (1 / x)) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have hθ : thetaU (cc * (1 / x)) = x * thetaU (cc * x) := by
    apply mul_left_cancel₀ hB
    rw [← hinv]
    ring
  unfold thetaC
  rw [Real.rpow_one, one_mul, smul_eq_mul, hθ, Complex.ofReal_mul]

/-- **The FE-pair of `Q0`.** -/
def zqPair : WeakFEPair ℂ where
  f := thetaC
  g := thetaC
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := thetaC_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := thetaC_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun _ hx => thetaC_feq hx
  hf_top := thetaC_decay
  hg_top := thetaC_decay

/-- The pair is its own dual, so `Λ(1 − s) = Λ(s)`. -/
theorem zqPair_symm_f_modif : zqPair.symm.f_modif = zqPair.f_modif := by
  funext x
  have key : ∀ e : ℂ, e = 1 →
      (Set.Ioi (1 : ℝ)).indicator (fun y => thetaC y - 1) x
          + (Set.Ioo (0 : ℝ) 1).indicator (fun y => thetaC y - (e * ((y ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)) x
        = (Set.Ioi (1 : ℝ)).indicator (fun y => thetaC y - 1) x
          + (Set.Ioo (0 : ℝ) 1).indicator (fun y => thetaC y - ((1 : ℂ) * ((y ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)) x := by
    rintro e rfl
    rfl
  exact key ((1 : ℂ)⁻¹) inv_one

theorem zqPair_symm_Λ (s : ℂ) : zqPair.symm.Λ s = zqPair.Λ s := by
  have h0 : zqPair.symm.Λ₀ s = zqPair.Λ₀ s := by
    show mellin zqPair.symm.f_modif s = mellin zqPair.f_modif s
    rw [zqPair_symm_f_modif]
  show zqPair.symm.Λ₀ s - (1 / s) • (1 : ℂ) - (((1 : ℂ)⁻¹) / (((1 : ℝ) : ℂ) - s)) • (1 : ℂ)
    = zqPair.Λ₀ s - (1 / s) • (1 : ℂ) - ((1 : ℂ) / (((1 : ℝ) : ℂ) - s)) • (1 : ℂ)
  rw [h0, inv_one]

theorem zqPair_Λ_one_sub (s : ℂ) : zqPair.Λ (1 - s) = zqPair.Λ s := by
  have h := zqPair.functional_equation s
  rw [zqPair_symm_Λ] at h
  have hk : ((zqPair.k : ℝ) : ℂ) = 1 := Complex.ofReal_one
  have he : zqPair.ε = 1 := rfl
  rw [hk, he, one_smul] at h
  exact h

end ZQ
end Schema
end SIDEExplicitFormula
