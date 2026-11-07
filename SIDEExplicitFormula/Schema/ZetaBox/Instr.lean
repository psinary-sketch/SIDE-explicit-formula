/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZetaBox/Instr.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(b), W-ORD-ZETA-BOX Z4; the plan relay data/b744_zetabox_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z4, THE INSTRUMENT AT ZETA. b741's carry (OffZero/GammaVal.lean :248 `inD_transfer`) read at `π`: a disc of `incGamma1 w ρ` at a rational
`ρ` within `d` of `π` (by `pi_gt_d20`, `pi_lt_d20`) is a disc of `incGamma1 w π` widened by `d · 10/3`. The sign of `zLam T` at a rational
`T` from a disc of the first shell, Z2's `11/10^7` and the exact pole part `1/(1/4 + T²)`, the side condition one `ℚ` inequality. No value is
certified here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZetaBox.Tail
import SIDEExplicitFormula.Schema.ZetaBox.Line
import SIDEExplicitFormula.Schema.ZQ.OffZero.GammaVal

open Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZetaBox

open ZQ.OffZero

/-! ## Z4 -- the instrument at zeta -/

/-- The carry from a rational `ρ` to `π`: `|π − ρ| ≤ d` by `pi_gt_d20`, `pi_lt_d20`; the Lipschitz bound at `m = 13/10` costs `d · 10/3`. -/
theorem inD_transfer_pi {w : ℂ} (hw : w.re ≤ 1) {ρ d : ℚ} (h13 : 13 / 10 ≤ ρ)
    (hlo : ρ - d ≤ 314159265358979323846 / 10 ^ 20) (hhi : 314159265358979323847 / 10 ^ 20 ≤ ρ + d) {c : ℚ × ℚ} {r r' : ℚ}
    (h : inD (incGamma1 w ρ) c r) (hr : r + d * (10 / 3) ≤ r') : inD (incGamma1 w Real.pi) c r' := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hlo' : (ρ : ℝ) - d ≤ 314159265358979323846 / 10 ^ 20 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hlo
    push_cast at h'
    linarith
  have hhi' : (314159265358979323847 / 10 ^ 20 : ℝ) ≤ ρ + d := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hhi
    push_cast at h'
    linarith
  have h13' : (13 / 10 : ℝ) ≤ ρ := by
    have h' := (Rat.cast_le (K := ℝ)).mpr h13
    push_cast at h'
    linarith
  have hr' : (r : ℝ) + d * (10 / 3) ≤ r' := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hr
    push_cast at h'
    linarith
  have hab : |Real.pi - ρ| ≤ d := by
    rw [abs_le]
    constructor <;> linarith
  have hm : (13 / 10 : ℝ) ≤ Real.pi := by linarith
  have hL := incGamma1_sub_le hw (m := 13 / 10) (by norm_num) hm h13'
  rw [show (13 / 10 : ℝ) - 1 = 3 / 10 by norm_num] at hL
  have he : Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10)) ≤ 10 / 3 := by
    have a1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have a2 : Real.exp (-(3 / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    calc Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10)) ≤ 1 * (1 / (3 / 10)) :=
          mul_le_mul a1 (by gcongr) (by positivity) (by norm_num)
      _ = 10 / 3 := by norm_num
  have hd0 : (0 : ℝ) ≤ d := (abs_nonneg _).trans hab
  unfold inD at *
  have e : incGamma1 w Real.pi - qc c = (incGamma1 w Real.pi - incGamma1 w ρ) + (incGamma1 w ρ - qc c) := by ring
  rw [e]
  have hT : ‖incGamma1 w Real.pi - incGamma1 w ρ‖ ≤ d * (10 / 3) := by
    refine hL.trans ?_
    calc |Real.pi - ρ| * Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10))
        = |Real.pi - ρ| * (Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10))) := by ring
      _ ≤ d * (10 / 3) := mul_le_mul hab he (by positivity) hd0
  linarith [norm_add_le (incGamma1 w Real.pi - incGamma1 w ρ) (incGamma1 w ρ - qc c)]

/-- At a rational ordinate `T`, `s/2 = 1/4 + (T/2) i` as a rational complex number. -/
theorem lp_half (T : ℚ) : lp T / 2 = qc ((1 / 4 : ℚ), T / 2) := by
  apply Complex.ext
  · rw [qc_re]
    norm_num [lp]
  · rw [qc_im]
    norm_num [lp]

/-- `M`'s real part from a disc of the first shell, within Z2's `11/10^7`. -/
theorem zM_re_bounds {T : ℚ} {c : ℚ × ℚ} {r : ℚ} (hI : inD (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi) c r) :
    2 * (c.1 : ℝ) - 2 * r - 11 / 10 ^ 7 ≤ (zM (qc ((1 / 4 : ℚ), T / 2))).re ∧
      (zM (qc ((1 / 4 : ℚ), T / 2))).re ≤ 2 * (c.1 : ℝ) + 2 * r + 11 / 10 ^ 7 := by
  have hR := zM_sub_le (w := qc ((1 / 4 : ℚ), T / 2)) (by rw [qc_re]; norm_num)
  unfold inD at hI
  have a1 := abs_le.mp ((Complex.abs_re_le_norm _).trans hR)
  have a2 := abs_le.mp ((Complex.abs_re_le_norm _).trans hI)
  have e1 : (zM (qc ((1 / 4 : ℚ), T / 2)) - 2 * incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi).re
      = (zM (qc ((1 / 4 : ℚ), T / 2))).re - 2 * (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi).re := by
    simp
  have e2 : (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi - qc c).re
      = (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi).re - c.1 := by
    rw [Complex.sub_re, qc_re]
  rw [e1] at a1
  rw [e2] at a2
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- **The negative sign** at a rational `T`: the side condition `(2 c + 2 r + 11/10^7)(1 + 4 T²) < 4`. -/
theorem zLam_neg_of {T : ℚ} {c : ℚ × ℚ} {r : ℚ} (hI : inD (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi) c r)
    (hc : (2 * c.1 + 2 * r + 11 / 10 ^ 7) * (1 + 4 * T ^ 2) < 4) : zLam T < 0 := by
  have hb := (zM_re_bounds hI).2
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast at hc'
  have hq : (0 : ℝ) < 1 / 4 + (T : ℝ) ^ 2 := by positivity
  unfold zLam
  rw [lp_half, sub_neg, lt_div_iff₀ hq]
  nlinarith [mul_le_mul_of_nonneg_right hb hq.le]

/-- **The positive sign** at a rational `T`: the side condition `4 < (2 c − 2 r − 11/10^7)(1 + 4 T²)`. -/
theorem zLam_pos_of {T : ℚ} {c : ℚ × ℚ} {r : ℚ} (hI : inD (incGamma1 (qc ((1 / 4 : ℚ), T / 2)) Real.pi) c r)
    (hc : 4 < (2 * c.1 - 2 * r - 11 / 10 ^ 7) * (1 + 4 * T ^ 2)) : 0 < zLam T := by
  have hb := (zM_re_bounds hI).1
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast at hc'
  have hq : (0 : ℝ) < 1 / 4 + (T : ℝ) ^ 2 := by positivity
  unfold zLam
  rw [lp_half, sub_pos, div_lt_iff₀ hq]
  nlinarith [mul_le_mul_of_nonneg_right hb hq.le]

end ZetaBox
end Schema
end SIDEExplicitFormula
