import SIDEExplicitFormula.Window.ArchLam

/-!
# L9b whole: Gauss's integral at the window in the B-spline basis

`archJ_eq_split` gives Gauss's integral at the window as `(11/6) K 1 + ∫_(u > 1) H(u)^2 log 16 u` less the far sum;
`integral_windowH_sq_log` writes the band term over the pairs of splines (`archJ_basis`). At integer differences `λ` is its
closed form `lamI_closed` (`lamI_natSub`), so the far sum is written in the terms `lamT` (`archJ_basis_closed`).
-/

namespace SIDEExplicitFormula.Window

open MeasureTheory

/-- **L9b, `archJ_basis`**: Gauss's integral at the window as `(11/6) K 1`, the band sum over the pairs of splines, and
the far sum. -/
theorem archJ_basis :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((11 / 6 * windowKx 1 +
        1 / 16 * (∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ Finset.Icc 16 16380, coeff i * coeff j * lgI i ((i : ℝ) - j)) -
        1 / 16 * ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i * lamI ((i : ℝ) - j) : ℝ) : ℂ) := by
  rw [archJ_eq_split, integral_windowH_sq_log]

/-- `λ` at the difference of two naturals, in closed form. -/
theorem lamI_natSub (i j : ℕ) :
    lamI ((i : ℝ) - j) =
      ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + ((i : ℤ) - j) - m) := by
  have h : ((i : ℝ) - j) = (((i : ℤ) - j : ℤ) : ℝ) := by norm_num
  rw [h, lamI_closed]

/-- **`archJ_basis` with the far sum in closed form**: each `λ(i - j)` as its combination of the `lamT`. -/
theorem archJ_basis_closed :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((11 / 6 * windowKx 1 +
        1 / 16 * (∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ Finset.Icc 16 16380, coeff i * coeff j * lgI i ((i : ℝ) - j)) -
        1 / 16 * ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i *
          ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + ((i : ℤ) - j) - m) : ℝ) : ℂ) := by
  rw [archJ_basis]
  simp only [lamI_natSub]

end SIDEExplicitFormula.Window
