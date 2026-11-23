import SIDEExplicitFormula.Window.ArchBasis

/-!
# L9b, the band sum restricted to the pairs of splines that meet

The supports of `B(16 u - i)` and `B(16 u - j)` meet only where `|i - j| ≤ 3` (`lgI_eq_zero_of_ge`, `lgI_eq_zero_of_le`),
so each row of the band sum runs over those `j` alone (`band_row_local`), and Gauss's integral at the window is written
with the band so restricted and the far sum in closed form (`archJ_basis_local`), the form of the plan's `archJ_basis`.
-/

namespace SIDEExplicitFormula.Window

/-- One row of the band sum: the pairs with `|i - j| ≥ 4` give `0`. -/
theorem band_row_local (i : ℕ) :
    ∑ j ∈ Finset.Icc 16 16380, coeff i * coeff j * lgI i ((i : ℝ) - j) =
      ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3),
        coeff i * coeff j * lgI i ((i : ℝ) - j) := by
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun j hj hnot => ?_)
  have hn : ¬ (j ≤ i + 3 ∧ i ≤ j + 3) := fun h => hnot (Finset.mem_filter.mpr ⟨hj, h⟩)
  rw [not_and_or, not_le, not_le] at hn
  rcases hn with h | h
  · have h' : (i : ℝ) + 4 ≤ j := by exact_mod_cast (show i + 4 ≤ j by omega)
    rw [lgI_eq_zero_of_le (by linarith : (i : ℝ) - j ≤ -4), mul_zero]
  · have h' : (j : ℝ) + 4 ≤ i := by exact_mod_cast (show j + 4 ≤ i by omega)
    rw [lgI_eq_zero_of_ge (by linarith : (4 : ℝ) ≤ (i : ℝ) - j), mul_zero]

/-- **L9b in the plan's form**: Gauss's integral at the window as `(11/6) K 1`, the band over the pairs within three
knots, and the far sum in closed form. -/
theorem archJ_basis_local :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((11 / 6 * windowKx 1 +
        1 / 16 * (∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3),
          coeff i * coeff j * lgI i ((i : ℝ) - j)) -
        1 / 16 * ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i *
          ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + ((i : ℤ) - j) - m) : ℝ) : ℂ) := by
  rw [archJ_basis_closed]
  simp only [band_row_local]

end SIDEExplicitFormula.Window
