import SIDEExplicitFormula.Window.PoleSum

/-!
# L11a: the pole term's data half as a coefficient for each `log m`

The pole term at the window reads `∑_{16 ≤ j ≤ 16380} c_j rhoLog j` (`poleTerm_windowK_intH`), and `rhoLog j` is a sum over the
five knots of `bw k (k + j) ^ 3 log (k + j) / 6`. Gathered by `m = j + k`, the sum is `∑_{m < 16385} poleCoef m log m`, with
`poleCoef m = m ^ 3 / 6 ∑_k bw k c_(m - k)` (`poleSum_comb`), and each `poleCoef m` is the integer `poleNum m` over
`6 * 10 ^ coeffScale` (`poleCoef_eq`). Nothing here is evaluated.
-/

namespace SIDEExplicitFormula.Window

/-- One knot's part of `rhoLog` at `m`. -/
noncomputable def poleF (k m : ℕ) : ℝ := (bw k : ℝ) * (m : ℝ) ^ 3 * Real.log m / 6

/-- The coefficient of `log m` in the pole term's data half. -/
noncomputable def poleCoef (m : ℕ) : ℝ := (m : ℝ) ^ 3 / 6 * ∑ k ∈ Finset.range 5, (bw k : ℝ) * coeff (m - k)

/-- The integer numerator of `poleCoef m` over `6 * 10 ^ coeffScale`. -/
def poleNum (m : ℕ) : ℤ := (m : ℤ) ^ 3 * ∑ k ∈ Finset.range 5, bw k * coeffInt (m - k)

theorem coeff_eq_zero_of_not (j : ℕ) (h : ¬(16 ≤ j ∧ j ≤ 16380)) : coeff j = 0 := by
  unfold coeff
  rw [coeffInt_eq_zero j h, Int.cast_zero, zero_div]

theorem poleCoef_eq (m : ℕ) : poleCoef m = ((poleNum m : ℤ) : ℝ) / (6 * 10 ^ coeffScale) := by
  simp only [poleCoef, poleNum, coeff]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem poleSum_shift (k M : ℕ) (G : ℕ → ℝ) (h0 : coeff 0 = 0) :
    ∑ m ∈ Finset.range (k + M), coeff (m - k) * G m = ∑ x ∈ Finset.range M, coeff x * G (x + k) := by
  rw [Finset.sum_range_add]
  have hz : ∑ m ∈ Finset.range k, coeff (m - k) * G m = 0 :=
    Finset.sum_eq_zero (fun m hm => by
      rw [Finset.mem_range] at hm
      rw [show m - k = 0 by omega, h0, zero_mul])
  rw [hz, zero_add]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [show k + x - k = x by omega, add_comm k x]

theorem poleSum_tail (k M : ℕ) (G : ℕ → ℝ) (hz : ∀ x, x < k → coeff (M + x) = 0) :
    ∑ j ∈ Finset.range (M + k), coeff j * G (j + k) = ∑ x ∈ Finset.range M, coeff x * G (x + k) := by
  rw [Finset.sum_range_add]
  have h : ∑ x ∈ Finset.range k, coeff (M + x) * G (M + x + k) = 0 :=
    Finset.sum_eq_zero (fun x hx => by
      rw [Finset.mem_range] at hx
      rw [hz x hx, zero_mul])
  rw [h, add_zero]

/-- **L11a: the pole term's data half, gathered at each `log m`.** -/
theorem poleSum_comb :
    ∑ j ∈ Finset.Icc 16 16380, coeff j * rhoLog j = ∑ m ∈ Finset.range 16385, poleCoef m * Real.log m := by
  have h1 : ∑ j ∈ Finset.Icc 16 16380, coeff j * rhoLog j = ∑ j ∈ Finset.range 16385, coeff j * rhoLog j := by
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
      omega
    · intro j _ hj
      rw [coeff_eq_zero_of_not j (fun h => hj (Finset.mem_Icc.mpr h)), zero_mul]
  have h2 : ∀ j : ℕ, coeff j * rhoLog j = ∑ k ∈ Finset.range 5, coeff j * poleF k (j + k) := by
    intro j
    rw [rhoLog, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [poleF, Nat.cast_add]
    rw [add_comm (k : ℝ) (j : ℝ)]
  have h3 : ∀ m : ℕ, poleCoef m * Real.log m = ∑ k ∈ Finset.range 5, coeff (m - k) * poleF k m := by
    intro m
    simp only [poleCoef, poleF]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_congr rfl (fun m _ => h3 m)]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  calc ∑ j ∈ Finset.range 16385, coeff j * poleF k (j + k)
      = ∑ j ∈ Finset.range ((16385 - k) + k), coeff j * poleF k (j + k) := by
        rw [show 16385 - k + k = 16385 by omega]
    _ = ∑ x ∈ Finset.range (16385 - k), coeff x * poleF k (x + k) :=
        poleSum_tail k (16385 - k) (poleF k) (fun x hx => coeff_eq_zero_of_not _ (by omega))
    _ = ∑ m ∈ Finset.range (k + (16385 - k)), coeff (m - k) * poleF k m :=
        (poleSum_shift k (16385 - k) (poleF k) (coeff_eq_zero_of_not 0 (by omega))).symm
    _ = ∑ m ∈ Finset.range 16385, coeff (m - k) * poleF k m := by
        rw [show k + (16385 - k) = 16385 by omega]

end SIDEExplicitFormula.Window
