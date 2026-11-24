import SIDEExplicitFormula.Window.ArchLam
import SIDEExplicitFormula.Window.ArchClosed

/-!
# L9c2, its second part: each term of the far kernel in closed form at every shift `c ≥ 0`

`fPiece l c` is `fA l c * log (1 + c) + fB l c * log c + fG l c` where `c > 0` (`fPiece_closed`), and at `c = 0` for
`l ≥ 1` (`fPiece_zero_succ`, the two logarithms `log 1` and `log 0` being `0`). Since `lamW k 0 0 = 0`, `lamT k c` is
the sum over `l` of `lamW k c l` times that closed form at every integer `c ≥ 0` (`lamT_form`). Nothing here is evaluated.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The coefficient of `log (1 + c)` in `fPiece l c`. -/
noncomputable def fA (l : ℕ) (c : ℝ) : ℝ := (1 - (-c) ^ (l + 1)) / ((l : ℝ) + 1)

/-- The coefficient of `log c` in `fPiece l c`. -/
noncomputable def fB (l : ℕ) (c : ℝ) : ℝ := (-c) ^ (l + 1) / ((l : ℝ) + 1)

/-- The part of `fPiece l c` with no logarithm. -/
noncomputable def fG (l : ℕ) (c : ℝ) : ℝ :=
  -(∑ m ∈ Finset.range (l + 1), (-c) ^ m / (((l + 1 : ℕ) : ℝ) - m)) / ((l : ℝ) + 1)

theorem fPiece_form_pos (l : ℕ) {c : ℝ} (hc : 0 < c) :
    fPiece l c = fA l c * Real.log (1 + c) + fB l c * Real.log c + fG l c := by
  rw [fPiece_closed l hc]
  unfold fA fB fG
  ring

theorem fG_zero (l : ℕ) : fG l 0 = -1 / ((l : ℝ) + 1) ^ 2 := by
  unfold fG
  rw [Finset.sum_range_succ']
  have h : ∀ m ∈ Finset.range l, (-(0 : ℝ)) ^ (m + 1) / (((l + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) = 0 := by
    intro m _
    rw [neg_zero, zero_pow (by omega : m + 1 ≠ 0), zero_div]
  rw [Finset.sum_congr rfl h, Finset.sum_const_zero, zero_add, pow_zero, Nat.cast_zero, sub_zero]
  push_cast
  first
  | ring
  | (field_simp
     ring)

theorem fPiece_form_zero (l : ℕ) (hl : 0 < l) :
    fPiece l 0 = fA l 0 * Real.log (1 + 0) + fB l 0 * Real.log 0 + fG l 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  rw [fPiece_zero_succ j, fG_zero, add_zero, Real.log_one, Real.log_zero, mul_zero, mul_zero, zero_add, zero_add]
  push_cast
  ring

theorem lamW_zero_zero (k : ℕ) : lamW k 0 0 = 0 := by
  rcases k with _ | _ | _ | _ | k
  all_goals first
    | rfl
    | simp [lamW]
    | (simp only [lamW]
       norm_num)

/-- **`lamT k c` in closed form** at each integer shift `c ≥ 0`. -/
theorem lamT_form (k : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    lamT k c = ∑ l : Fin 7, lamW k (c : ℝ) l *
      (fA l (c : ℝ) * Real.log (1 + (c : ℝ)) + fB l (c : ℝ) * Real.log (c : ℝ) + fG l (c : ℝ)) := by
  unfold lamT
  rw [if_pos hc]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rcases hc.lt_or_eq with hpos | hzero
  · rw [fPiece_form_pos (l : ℕ) (show (0 : ℝ) < (c : ℝ) by exact_mod_cast hpos)]
  · subst hzero
    simp only [Int.cast_zero]
    rcases Nat.eq_zero_or_pos (l : ℕ) with h0 | h1
    · have hl : l = 0 := Fin.ext h0
      subst hl
      rw [lamW_zero_zero, zero_mul, zero_mul]
    · rw [fPiece_form_zero (l : ℕ) h1]

/-- The coefficient of `log (1 + c)` in `lamT k c`. -/
noncomputable def lA (k : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, lamW k c l * fA l c

/-- The coefficient of `log c` in `lamT k c`. -/
noncomputable def lB (k : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, lamW k c l * fB l c

/-- The part of `lamT k c` with no logarithm. -/
noncomputable def lG (k : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, lamW k c l * fG l c

theorem lamT_split (k : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    lamT k c = lA k (c : ℝ) * Real.log (1 + (c : ℝ)) + lB k (c : ℝ) * Real.log (c : ℝ) + lG k (c : ℝ) := by
  rw [lamT_form k hc]
  unfold lA lB lG
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- The first index of the convolution sums that the pair `k, m` reads at a shift `c ≥ 0`. -/
def aKM (k m : ℕ) : ℕ := 16364 + m - k

/-- `lamT` at the shift of the lag `t - 16364` and the pair `k, m`, as the place `t - aKM k m` where it is not `0`. -/
theorem lamT_at (k m t : ℕ) (hk : k ≤ 3) :
    lamT k ((k : ℤ) + ((t : ℤ) - ((16365 : ℕ) - 1)) - m) =
      if aKM k m ≤ t then
        lA k ((t - aKM k m : ℕ) : ℝ) * Real.log (1 + ((t - aKM k m : ℕ) : ℝ)) +
          lB k ((t - aKM k m : ℕ) : ℝ) * Real.log ((t - aKM k m : ℕ) : ℝ) + lG k ((t - aKM k m : ℕ) : ℝ)
      else 0 := by
  have ha : aKM k m = 16364 + m - k := rfl
  split_ifs with h
  · have hc : (k : ℤ) + ((t : ℤ) - ((16365 : ℕ) - 1)) - m = ((t - aKM k m : ℕ) : ℤ) := by omega
    rw [hc, lamT_split k (by omega)]
    first
    | simp only [Int.cast_natCast]
    | (push_cast
       ring_nf)
    | norm_cast
  · unfold lamT
    rw [if_neg (by omega)]

/-- A sum over `t < T` of the terms with `a ≤ t`, written over `c < T - a` at `t = a + c`. -/
theorem shift_ge_sum (T a : ℕ) (ha : a ≤ T) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if a ≤ t then f t else 0) = ∑ c ∈ Finset.range (T - a), f (a + c) := by
  rw [← Finset.sum_range_add_sum_Ico _ ha]
  have h1 : ∑ t ∈ Finset.range a, (if a ≤ t then f t else 0) = 0 := by
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have ht' : t < a := Finset.mem_range.mp ht
    rw [if_neg (by omega)]
  have h2 : ∑ t ∈ Finset.Ico a T, (if a ≤ t then f t else 0) = ∑ t ∈ Finset.Ico a T, f t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht' : a ≤ t := (Finset.mem_Ico.mp ht).1
    rw [if_pos ht']
  rw [h1, h2, zero_add, Finset.sum_Ico_eq_sum_range]

/-- A sum over `c < M` whose terms vanish from `M` on, read over `c < N` for any `N ≥ M`. -/
theorem sum_range_pad (M N : ℕ) (hMN : M ≤ N) (g : ℕ → ℝ) (hg : ∀ c, M ≤ c → g c = 0) :
    ∑ c ∈ Finset.range M, g c = ∑ c ∈ Finset.range N, g c := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hMN) (fun c _ hc => hg c ?_)
  have := Finset.mem_range.not.mp hc
  omega

/-- A sum of `g c * log (1 + c)` over `c < N`, written over `n < N + 1` as `g (n - 1) * log n`, the term `n = 0` being
`0` since `log 0 = 0`. -/
theorem sum_log_succ (N : ℕ) (g : ℕ → ℝ) :
    ∑ c ∈ Finset.range N, g c * Real.log (1 + (c : ℝ)) = ∑ n ∈ Finset.range (N + 1), g (n - 1) * Real.log (n : ℝ) := by
  rw [Finset.sum_range_succ']
  have h0 : g (0 - 1) * Real.log ((0 : ℕ) : ℝ) = 0 := by
    rw [Nat.cast_zero, Real.log_zero, mul_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Nat.add_sub_cancel, Nat.cast_succ, add_comm (c : ℝ) 1]

/-- Three sums regrouped: the pairs `k, m` inside and the index `n` outside. -/
theorem regroup3 (w : ℕ → ℝ) (F : ℕ → ℕ → ℕ → ℝ) (G : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (K M N : ℕ) :
    ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range M, w m * (∑ n ∈ Finset.range N, F k m n * L n + G k m) =
      ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range M, w m * G k m +
        ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range K, ∑ m ∈ Finset.range M, w m * F k m n) * L n := by
  have h : ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range K, ∑ m ∈ Finset.range M, w m * F k m n) * L n =
      ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range N, w m * (F k m n * L n) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    ring
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_add, Finset.mul_sum, add_comm]

end Window
end SIDEExplicitFormula
