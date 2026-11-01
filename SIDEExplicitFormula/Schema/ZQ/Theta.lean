/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Theta.lean
THIS PROGRAMME'S WORK (act b730, ruling (R340)(4), group B of relay data/b730_continuation_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE THETA OF `Q0` AND ITS INVERSION. `thetaU a = Σ exp(−π a Q0)`. Summing in `m` first and applying Mathlib's even kernel equation (itself
`jacobiTheta₂_functional_equation`) gives `thetaU a = a^{−1/2} D(23a/4, 1/a)` with `D(x, y)` a double sum symmetric in `x, y` by one exchange, so
the same `D` appears at `a` and at `b = 4/(23a)`: `a^{1/2} thetaU a = b^{1/2} thetaU b`. Numerically read before any Lean at relay
data/b730_theta_check.txt. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Lattice

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- **The theta of the form.** -/
def thetaU (u : ℝ) : ℝ := ∑' p : ℤ × ℤ, Real.exp (-(Real.pi * u) * qR p)

/-- The character `exp(2πi (n/2) k) = (−1)^{nk}`. -/
def cTerm (n k : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) / 2 : ℝ) : ℂ) * (k : ℂ))

theorem cTerm_comm (n k : ℤ) : cTerm n k = cTerm k n := by
  unfold cTerm
  congr 1
  push_cast
  ring

theorem norm_cTerm (n k : ℤ) : ‖cTerm n k‖ = 1 := by
  unfold cTerm
  have h : 2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) / 2 : ℝ) : ℂ) * (k : ℂ)
      = ((2 * Real.pi * ((n : ℝ) / 2) * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Gaussian in the kernels' shape. -/
def eG (x : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * (n : ℝ) ^ 2 * x)

theorem eG_nonneg (x : ℝ) (n : ℤ) : 0 ≤ eG x n := (Real.exp_pos _).le

theorem eG_summable {x : ℝ} (hx : 0 < x) : Summable (eG x) := by
  have hπ := Real.pi_pos
  have h := gauss_summable (c := Real.pi * x) (mul_pos hπ hx)
  refine h.congr (fun n => ?_)
  unfold eG
  congr 1
  ring

/-- **The double sum.** -/
def dblTerm (x y : ℝ) (n k : ℤ) : ℂ := ((eG x n : ℝ) : ℂ) * (cTerm n k * ((eG y k : ℝ) : ℂ))

def dbl (x y : ℝ) : ℂ := ∑' n : ℤ, ∑' k : ℤ, dblTerm x y n k

theorem dbl_summable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Summable (Function.uncurry (dblTerm x y)) := by
  refine Summable.of_norm ?_
  have h := (eG_summable hx).mul_of_nonneg (eG_summable hy) (fun n => eG_nonneg x n) (fun k => eG_nonneg y k)
  refine h.congr (fun p => ?_)
  obtain ⟨n, k⟩ := p
  show eG x n * eG y k = ‖dblTerm x y n k‖
  unfold dblTerm
  rw [norm_mul, norm_mul, norm_cTerm, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (eG_nonneg x n), Real.norm_of_nonneg (eG_nonneg y k)]

/-- **The exchange**: `D(x, y) = D(y, x)`. -/
theorem dbl_comm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : dbl x y = dbl y x := by
  unfold dbl
  calc ∑' n : ℤ, ∑' k : ℤ, dblTerm x y n k
      = ∑' k : ℤ, ∑' n : ℤ, dblTerm x y n k := ((dbl_summable hx hy).tsum_comm).symm
    _ = ∑' n : ℤ, ∑' k : ℤ, dblTerm y x n k := by
        refine tsum_congr (fun k => tsum_congr (fun n => ?_))
        unfold dblTerm
        rw [cTerm_comm n k]
        ring

/-- **The step**: `thetaU a = a^{−1/2} D(23a/4, 1/a)`. -/
theorem thetaU_eq {a : ℝ} (ha : 0 < a) :
    ((thetaU a : ℝ) : ℂ) = ((1 / a ^ (1 / 2 : ℝ) : ℝ) : ℂ) * dbl (a * (23 / 4)) (1 / a) := by
  have hπ := Real.pi_pos
  have hs := lattice_summable (c := Real.pi * a) (mul_pos hπ ha)
  have h1 : thetaU a = ∑' n : ℤ, eG (a * (23 / 4)) n *
      HurwitzZeta.evenKernel (((n : ℝ) / 2 : ℝ) : UnitAddCircle) a := by
    unfold thetaU
    have h0 := ((Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => Real.exp (-(Real.pi * a) * qR p))).symm
    rw [h0]
    have hs' : Summable (fun p : ℤ × ℤ => Real.exp (-(Real.pi * a) * qR ((Equiv.prodComm ℤ ℤ) p))) :=
      (Equiv.prodComm ℤ ℤ).summable_iff.mpr hs
    rw [hs'.tsum_prod]
    refine tsum_congr (fun n => ?_)
    have hk := (HurwitzZeta.hasSum_int_evenKernel ((n : ℝ) / 2) ha).tsum_eq
    rw [← hk, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    show Real.exp (-(Real.pi * a) * qR (m, n))
      = eG (a * (23 / 4)) n * Real.exp (-Real.pi * ((m : ℝ) + (n : ℝ) / 2) ^ 2 * a)
    rw [qR_eq]
    unfold eG
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : ∀ n : ℤ, ((HurwitzZeta.evenKernel (((n : ℝ) / 2 : ℝ) : UnitAddCircle) a : ℝ) : ℂ)
      = ((1 / a ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑' k : ℤ, cTerm n k * ((eG (1 / a) k : ℝ) : ℂ) := by
    intro n
    have hk : ∑' k : ℤ, cTerm n k * ((eG (1 / a) k : ℝ) : ℂ)
        = ((HurwitzZeta.cosKernel (((n : ℝ) / 2 : ℝ) : UnitAddCircle) (1 / a) : ℝ) : ℂ) :=
      (HurwitzZeta.hasSum_int_cosKernel ((n : ℝ) / 2) (t := 1 / a) (one_div_pos.mpr ha)).tsum_eq
    rw [hk, HurwitzZeta.evenKernel_functional_equation, Complex.ofReal_mul]
  rw [h1, Complex.ofReal_tsum]
  unfold dbl
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [Complex.ofReal_mul, hc n]
  have he : ∑' k : ℤ, dblTerm (a * (23 / 4)) (1 / a) n k
      = ((eG (a * (23 / 4)) n : ℝ) : ℂ) * ∑' k : ℤ, cTerm n k * ((eG (1 / a) k : ℝ) : ℂ) := by
    rw [← tsum_mul_left]
    rfl
  rw [he]
  ring

/-- **The inversion of the theta of `Q0`.** -/
theorem thetaU_inversion {a : ℝ} (ha : 0 < a) :
    a ^ (1 / 2 : ℝ) * thetaU a = (4 / (23 * a)) ^ (1 / 2 : ℝ) * thetaU (4 / (23 * a)) := by
  have hb : 0 < 4 / (23 * a) := by positivity
  have e1 : 4 / (23 * a) * (23 / 4) = 1 / a := by
    field_simp
    try ring
  have e2 : 1 / (4 / (23 * a)) = a * (23 / 4) := by
    field_simp
    try ring
  have hx : 0 < a * (23 / 4) := by positivity
  have hy : 0 < 1 / a := by positivity
  have h1 := thetaU_eq ha
  have h2 := thetaU_eq hb
  rw [e1, e2, dbl_comm hy hx] at h2
  have hA : 0 < a ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have hB : 0 < (4 / (23 * a)) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hb _
  have hA1 : a ^ (1 / 2 : ℝ) * (1 / a ^ (1 / 2 : ℝ)) = 1 := mul_one_div_cancel hA.ne'
  have hB1 : (4 / (23 * a)) ^ (1 / 2 : ℝ) * (1 / (4 / (23 * a)) ^ (1 / 2 : ℝ)) = 1 := mul_one_div_cancel hB.ne'
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_mul, h1, h2, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, hA1, hB1]

end ZQ
end Schema
end SIDEExplicitFormula
