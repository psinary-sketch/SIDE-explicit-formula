import SIDEExplicitFormula.Window.FarClosed

/-!
# L9c2: the closed forms` coefficients `lA`, `lB` and `lG` as integer polynomials over one denominator

Written by relay tools/b768_far_data.py from the kernel`s own files (ArchLam.lean`s blob b4f3cbd71bde5a08 and Coeffs.lean`s);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The common denominator of the coefficients of `lA`, `lB` and `lG`. -/
def farDEN : ℕ := 352800

/-- `farDEN * lA k c` as a polynomial in `c` with integer coefficients. -/
def pA : ℕ → ℤ → ℤ
  | 0, x => ((((((((-420)) * x + 0) * x + 0) * x + 0) * x + 14700) * x + 35280) * x + 29400) * x + 8400
  | 1, x => (((((((1260) * x + 2940) * x + (-8820)) * x + 14700) * x + 161700) * x + 291060) * x + 208740) * x + 54180
  | 2, x => ((((((((-1260)) * x + (-5880)) * x + 0) * x + 58800) * x + 161700) * x + 194040) * x + 111720) * x + 25200
  | 3, x => (((((((420) * x + 2940) * x + 8820) * x + 14700) * x + 14700) * x + 8820) * x + 2940) * x + 420
  | _, _ => 0

/-- `farDEN * lB k c` as a polynomial in `c` with integer coefficients. -/
def pB : ℕ → ℤ → ℤ
  | 0, x => (((((((420) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0
  | 1, x => ((((((((-1260)) * x + (-2940)) * x + 8820) * x + (-14700)) * x + 0) * x + 0) * x + 0) * x + 0
  | 2, x => (((((((1260) * x + 5880) * x + 0) * x + (-58800)) * x + 0) * x + 0) * x + 0) * x + 0
  | 3, x => ((((((((-420)) * x + (-2940)) * x + (-8820)) * x + (-14700)) * x + 0) * x + 0) * x + 0) * x + 0
  | _, _ => 0

/-- `farDEN * lG k c` as a polynomial in `c` with integer coefficients. -/
def pG : ℕ → ℤ → ℤ
  | 0, x => ((((((420) * x + (-210)) * x + 140) * x + (-105)) * x + (-2856)) * x + (-3500)) * x + (-1200)
  | 1, x => (((((((-1260)) * x + (-2310)) * x + 9870) * x + (-19775)) * x + (-53907)) * x + (-43743)) * x + (-12031)
  | 2, x => ((((((1260) * x + 5250) * x + (-2520)) * x + (-57155)) * x + (-68838)) * x + (-38724)) * x + (-8500)
  | 3, x => (((((((-420)) * x + (-2730)) * x + (-7490)) * x + (-11165)) * x + (-6699)) * x + (-2233)) * x + (-319)
  | _, _ => 0

theorem lA_poly (k : ℕ) (hk : k ≤ 3) (c : ℕ) : lA k (c : ℝ) = (pA k (c : ℤ) : ℝ) / (farDEN : ℝ) := by
  interval_cases k <;>
    simp only [lA, lamW, fA, pA, farDEN, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

theorem lB_poly (k : ℕ) (hk : k ≤ 3) (c : ℕ) : lB k (c : ℝ) = (pB k (c : ℤ) : ℝ) / (farDEN : ℝ) := by
  interval_cases k <;>
    simp only [lB, lamW, fB, pB, farDEN, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

theorem lG_poly (k : ℕ) (hk : k ≤ 3) (c : ℕ) : lG k (c : ℝ) = (pG k (c : ℤ) : ℝ) / (farDEN : ℝ) := by
  interval_cases k <;>
    simp only [lG, lamW, fG, pG, farDEN, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

end Window
end SIDEExplicitFormula
