/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZetaBox/Line.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(b), W-ORD-ZETA-BOX Z3 and SPZ1; the plan relay data/b744_zetabox_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z3, THE REALITY ON THE LINE. `M (conj w) = conj (M w)` (the kernel real, `integral_conj`); at `s = 1/2 + it`, `1/2 − s/2 = conj (s/2)`, so
`completedRiemannZeta₀ s = Re M (s/2)` and `completedRiemannZeta s = Re M (s/2) − 1/(1/4 + t²)`, real: `zeta_line_real`. SPZ1, THE CONDITIONAL
THEOREM: the two signs give the zero, by the intermediate value theorem on `t ↦ Re Λ (1/2 + it)` over `[12, 16]` (continuous by
`differentiableAt_completedZeta`), a zero of `Λ` a zero of `ζ` by `riemannZeta_def_of_ne_zero`. No sign is certified here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZetaBox.Split

open Set Filter MeasureTheory HurwitzZeta

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZetaBox

/-! ## Z3 -- the reality on the line -/

/-- The point `1/2 + it` of the critical line. -/
def lp (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * Complex.I

theorem lp_re (t : ℝ) : (lp t).re = 1 / 2 := by
  norm_num [lp]

theorem lp_im (t : ℝ) : (lp t).im = t := by
  simp [lp]

theorem lp_ne_zero (t : ℝ) : lp t ≠ 0 := fun h => by
  have h1 := lp_re t
  rw [h, Complex.zero_re] at h1
  norm_num at h1

theorem lp_ne_one (t : ℝ) : lp t ≠ 1 := fun h => by
  have h1 := lp_re t
  rw [h, Complex.one_re] at h1
  norm_num at h1

theorem one_sub_lp_ne_zero (t : ℝ) : 1 - lp t ≠ 0 := fun h => lp_ne_one t (sub_eq_zero.mp h).symm

/-- On the line, `1/2 − s/2 = conj (s/2)`. -/
theorem lp_conj (t : ℝ) : 1 / 2 - lp t / 2 = starRingEnd ℂ (lp t / 2) := by
  apply Complex.ext
  · rw [Complex.conj_re]
    norm_num [lp]
  · rw [Complex.conj_im]
    norm_num [lp]

/-- The kernel is real: `M (conj w) = conj (M w)`. -/
theorem zM_conj (w : ℂ) : zM (starRingEnd ℂ w) = starRingEnd ℂ (zM w) := by
  rw [zM_eq, zM_eq, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_ne_zero.symm
  simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
  rw [show starRingEnd ℂ w - 1 = starRingEnd ℂ (w - 1) by rw [map_sub, map_one], Complex.cpow_conj _ _ harg,
    Complex.conj_ofReal]

/-- **Z3 at `Λ₀`**: `completedRiemannZeta₀ (1/2 + it) = Re M (1/4 + it/2)`. -/
theorem zeta0_line (t : ℝ) : completedRiemannZeta₀ (lp t) = (((zM (lp t / 2)).re : ℝ) : ℂ) := by
  rw [zeta0_split, lp_conj, zM_conj, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The completed function on the line, as a real number. -/
def zLam (t : ℝ) : ℝ := (zM (lp t / 2)).re - 1 / (1 / 4 + t ^ 2)

theorem lp_mul_one_sub (t : ℝ) : lp t * (1 - lp t) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold lp
  push_cast
  linear_combination (-(t : ℂ) ^ 2) * Complex.I_mul_I

/-- **Z3**: `completedRiemannZeta (1/2 + it) = zLam t`, a real number. -/
theorem zeta_line (t : ℝ) : completedRiemannZeta (lp t) = ((zLam t : ℝ) : ℂ) := by
  have h0 := lp_ne_zero t
  have h1 := one_sub_lp_ne_zero t
  have e : 1 / lp t + 1 / (1 - lp t) = 1 / (lp t * (1 - lp t)) := by
    rw [div_add_div _ _ h0 h1, one_mul, mul_one, sub_add_cancel]
  rw [completedRiemannZeta_eq, zeta0_line, sub_sub, e, lp_mul_one_sub]
  unfold zLam
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]

/-- **zeta_line_real** (the plan's (a)): the completed function is real on the critical line. -/
theorem zeta_line_real : ∀ t : ℝ, (completedRiemannZeta (1 / 2 + t * Complex.I)).im = 0 := fun t => by
  show (completedRiemannZeta (lp t)).im = 0
  rw [zeta_line, Complex.ofReal_im]

/-! ## SPZ1 -- the conditional theorem -/

/-- The real part of the completed function on the line. -/
def zf (t : ℝ) : ℝ := (completedRiemannZeta (lp t)).re

theorem zf_eq (t : ℝ) : zf t = zLam t := by
  unfold zf
  rw [zeta_line, Complex.ofReal_re]

theorem zf_cont : ContinuousOn zf (Icc 12 16) := by
  intro t _
  have hc : ContinuousAt (fun u : ℝ => completedRiemannZeta (lp u)) t :=
    (differentiableAt_completedZeta (lp_ne_zero t) (lp_ne_one t)).continuousAt.comp (f := lp)
      (show ContinuousAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * Complex.I) t by fun_prop)
  exact (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt

/-- **SPZ1, the conditional theorem**: the two signs give a zero of `ζ` on the line with ordinate in `(12, 16)`. -/
theorem zeta_box_of_signs (h12 : (completedRiemannZeta (1 / 2 + 12 * Complex.I)).re < 0)
    (h16 : 0 < (completedRiemannZeta (1 / 2 + 16 * Complex.I)).re) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ (12 : ℝ) < ρ.im ∧ ρ.im < 16 := by
  have e12 : lp 12 = 1 / 2 + 12 * Complex.I := by
    unfold lp
    norm_num
  have e16 : lp 16 = 1 / 2 + 16 * Complex.I := by
    unfold lp
    norm_num
  have a12 : zf 12 < 0 := by
    unfold zf
    rw [e12]
    exact h12
  have a16 : 0 < zf 16 := by
    unfold zf
    rw [e16]
    exact h16
  obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo (by norm_num : (12 : ℝ) ≤ 16) zf_cont ⟨a12, a16⟩
  refine ⟨lp t, ?_, lp_re t, by rw [lp_im]; exact ht.1, by rw [lp_im]; exact ht.2⟩
  rw [riemannZeta_def_of_ne_zero (lp_ne_zero t), zeta_line, ← zf_eq, h0, Complex.ofReal_zero, zero_div]

end ZetaBox
end Schema
end SIDEExplicitFormula
