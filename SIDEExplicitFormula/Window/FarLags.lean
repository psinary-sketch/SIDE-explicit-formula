import SIDEExplicitFormula.Window.AutoConv
import SIDEExplicitFormula.Window.ArchBandLocal
import SIDEExplicitFormula.Window.FarKernel

/-!
# L9c2, its first part: the far sum over the lags

The far sum of `archJ_basis_local` runs over the pairs `i, j` with a kernel `farK` that reads `i - j` alone. Shifted to
the indices from `0`, with the numerators over `10 ^ coeffScale` (`uR`), it is a double sum of the kind `lag_sum` reads,
so it is the sum over the places `k < 2 * 16365` of the convolution sums of the numerators and their turn times
`farK (k - 16364)`, and those sums are the data `autoD` (`auto_conv`). Nothing here is evaluated.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The window`s coefficient at the index `16 + a`, read from the list of numerators. -/
noncomputable def uR (a : ℕ) : ℝ := (coeffList.getD a 0 : ℝ) * (10 ^ coeffScale)⁻¹

theorem convR_congr {R : Type*} [CommRing R] (n : ℕ) {u u' v v' : ℕ → R} (hu : ∀ i < n, u i = u' i)
    (hv : ∀ j < n, v j = v' j) (k : ℕ) : convR n u v k = convR n u' v' k := by
  unfold convR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  split_ifs with h
  · rw [hu i hi', hv (k - i) h.2]
  · rfl

theorem convR_intCast (n : ℕ) (x y : ℕ → ℤ) (k : ℕ) :
    ((convR n x y k : ℤ) : ℝ) = convR n (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) k := by
  unfold convR
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · first
    | exact Int.cast_mul _ _
    | (push_cast; ring)
  · first
    | exact Int.cast_zero
    | simp

theorem convR_mul_const (n : ℕ) (u v : ℕ → ℝ) (s : ℝ) (k : ℕ) :
    convR n (fun i => u i * s) (fun j => v j * s) k = convR n u v k * (s * s) := by
  unfold convR
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · ring
  · ring

theorem Icc_sum_shift (f : ℕ → ℝ) : ∑ j ∈ Finset.Icc 16 16380, f j = ∑ b ∈ Finset.range 16365, f (16 + b) := by
  have e : Finset.Icc 16 16380 = Finset.Ico 16 (16 + 16365) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem coeff_shift (b : ℕ) (hb : b < 16365) : coeff (16 + b) = uR b := by
  unfold coeff coeffInt uR
  rw [if_pos (show 16 ≤ 16 + b ∧ 16 + b ≤ 16380 by omega), Nat.add_sub_cancel_left, div_eq_mul_inv]

theorem coeffList_rev_getD (j : ℕ) (hj : j < 16365) :
    coeffList.reverse.getD j 0 = coeffList.getD (16365 - 1 - j) 0 := by
  have h : j < coeffList.length := by rw [coeffList_len]; exact hj
  rw [List.getD_reverse j h, coeffList_len]

/-- **L9c2, the far sum over the lags**: the far sum of `archJ_basis_local` is the sum over the places of the data `autoD`
times the far kernel at the place`s lag, over `10 ^ (2 coeffScale)`. -/
theorem far_lags :
    ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i *
        ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + ((i : ℤ) - j) - m) =
      (∑ k ∈ Finset.range (2 * 16365), (autoD.getD k 0 : ℝ) * farK ((k : ℤ) - ((16365 : ℕ) - 1))) *
        ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  show ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i * farK ((i : ℤ) - j) = _
  rw [Icc_sum_shift]
  have step1 : ∀ b ∈ Finset.range 16365,
      coeff (16 + b) * ∑ i ∈ Finset.Icc 16 16380, coeff i * farK ((i : ℤ) - ((16 + b : ℕ) : ℤ)) =
        ∑ a ∈ Finset.range 16365, uR b * (uR a * farK ((a : ℤ) - b)) := by
    intro b hb
    have hb' : b < 16365 := Finset.mem_range.mp hb
    rw [Icc_sum_shift, coeff_shift b hb', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a < 16365 := Finset.mem_range.mp ha
    have e : (((16 + a : ℕ) : ℤ) - ((16 + b : ℕ) : ℤ)) = (a : ℤ) - b := by push_cast; ring
    rw [coeff_shift a ha', e]
  rw [Finset.sum_congr rfl step1]
  have step2 : ∑ b ∈ Finset.range 16365, ∑ a ∈ Finset.range 16365, uR b * (uR a * farK ((a : ℤ) - b)) =
      ∑ a ∈ Finset.range 16365, ∑ b ∈ Finset.range 16365, uR a * uR b * farK ((a : ℤ) - b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [step2, lag_sum 16365 uR farK, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < 2 * coeffList.length := by rw [coeffList_len]; exact Finset.mem_range.mp hk
  have hc : convR 16365 uR (fun j => uR (16365 - 1 - j)) k =
      convR 16365 (fun i => (coeffList.getD i 0 : ℝ) * (10 ^ coeffScale)⁻¹)
        (fun j => (coeffList.reverse.getD j 0 : ℝ) * (10 ^ coeffScale)⁻¹) k := by
    refine convR_congr 16365 (fun i _ => rfl) (fun j hj => ?_) k
    show (coeffList.getD (16365 - 1 - j) 0 : ℝ) * (10 ^ coeffScale)⁻¹ = (coeffList.reverse.getD j 0 : ℝ) * (10 ^ coeffScale)⁻¹
    rw [coeffList_rev_getD j hj]
  have hd : convR 16365 (fun i => (coeffList.getD i 0 : ℝ)) (fun j => (coeffList.reverse.getD j 0 : ℝ)) k =
      (autoD.getD k 0 : ℝ) := by
    rw [← convR_intCast]
    have h := auto_conv k hk'
    rw [coeffList_len] at h
    rw [h]
  rw [hc, convR_mul_const 16365 (fun i => (coeffList.getD i 0 : ℝ)) (fun j => (coeffList.reverse.getD j 0 : ℝ))
    ((10 ^ coeffScale)⁻¹) k, hd]
  ring

end Window
end SIDEExplicitFormula
