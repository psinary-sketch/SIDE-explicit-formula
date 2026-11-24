import SIDEExplicitFormula.Window.BandComb
import SIDEExplicitFormula.Window.FarComb

/-!
# L9c: the archimedean sums of L9b as a constant and a coefficient of each `log m`, `m < 16390`

`archJ_basis_local` with the band by `band_final` (L9c3) and the far sum by `far_final` (L9c2), the two lists of
coefficients padded to `16390` places by their lengths, so that the place `m` of each enters `archCoef m`.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The coefficient of `log m` in the archimedean sums of L9b. -/
noncomputable def archCoef (m : ℕ) : ℝ :=
  (1 / 16 * ((bandNumL.getD m 0 : ℝ) / (bandDEN : ℝ)) - 1 / 16 * ((farNumL.getD m 0 : ℝ) / (6 * (farDEN : ℝ)))) *
    ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹)

/-- The constant of the archimedean sums of L9b beside `11 / 6 * windowKx 1`. -/
noncomputable def archC0 : ℝ :=
  (1 / 16 * ∑ c ∈ Finset.range 16384, (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ) -
    1 / 16 * ∑ c ∈ Finset.range 16369, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ))) *
    ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹)

/-- **L9c**: Gauss's integral at the window as `(11/6) K 1`, a constant and a coefficient of each `log m`, `m < 16390`. -/
theorem archJ_comb :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) /
        (1 - (Real.exp (-t) : ℂ))) =
      ((11 / 6 * windowKx 1 + archC0 + ∑ m ∈ Finset.range 16390, archCoef m * Real.log (m : ℝ) : ℝ) : ℂ) := by
  rw [archJ_basis_local, band_final, far_final]
  congr 1
  have hb : ∑ n ∈ Finset.range (16384 + 1), (bandNumL.getD n 0 : ℝ) / (bandDEN : ℝ) * Real.log (n : ℝ) =
      ∑ n ∈ Finset.range 16390, (bandNumL.getD n 0 : ℝ) / (bandDEN : ℝ) * Real.log (n : ℝ) := by
    refine sum_range_pad (16384 + 1) 16390 (by norm_num) _ (fun n hn => ?_)
    show (bandNumL.getD n 0 : ℝ) / (bandDEN : ℝ) * Real.log (n : ℝ) = 0
    have hl : bandNumL.length ≤ n := by
      rw [bandNumL_len]
      omega
    rw [List.getD_eq_default bandNumL 0 hl, Int.cast_zero, zero_div, zero_mul]
  have hf : ∑ n ∈ Finset.range (16369 + 1), (farNumL.getD n 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (n : ℝ) =
      ∑ n ∈ Finset.range 16390, (farNumL.getD n 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (n : ℝ) := by
    refine sum_range_pad (16369 + 1) 16390 (by norm_num) _ (fun n hn => ?_)
    show (farNumL.getD n 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (n : ℝ) = 0
    have hl : farNumL.length ≤ n := by
      rw [farNumL_len]
      omega
    rw [List.getD_eq_default farNumL 0 hl, Int.cast_zero, zero_div, zero_mul]
  have hs : ∑ m ∈ Finset.range 16390, archCoef m * Real.log (m : ℝ) =
      1 / 16 * (∑ m ∈ Finset.range 16390, (bandNumL.getD m 0 : ℝ) / (bandDEN : ℝ) * Real.log (m : ℝ)) *
          ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) -
        1 / 16 * (∑ m ∈ Finset.range 16390, (farNumL.getD m 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (m : ℝ)) *
          ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold archCoef
    ring
  rw [hb, hf, hs]
  unfold archC0
  ring

end Window
end SIDEExplicitFormula
