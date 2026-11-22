import SIDEExplicitFormula.Window.KData
import SIDEExplicitFormula.Window.KappaClosed
import SIDEExplicitFormula.Window.KBasis
import SIDEExplicitFormula.Window.Coeffs
import Mathlib.Tactic.IntervalCases

/-!
# The values `K(n)` of the certificate, proved

At each `n` of the table of KData.lean the window`s autocorrelation at `log n` is `√n · Kt n / (80640 n^4 10^34)`, `Kt n` the
integer the table gives (`windowK_log_kt`). The route: `5040 n^4 κ_n(e)` is `kapTilde n e` (KappaClosed.lean); `kapTilde` is a
fourth difference of `D(x) = ∑_l w_l max(x + l, 0)^7`, so the double sum over the coefficients is a strided sum of
`F(T) = ∑_j a_j D(j - T)`; `F` obeys a local recurrence, `E` the fourth difference of `D` being `0` off `-3 .. 3`; the F tree
of KData.lean obeys the same recurrence, checked by the kernel`s evaluation in sixteen chunks, and so equals `F` from `16384`
down; the coefficient tree equals Coeffs.lean`s list, checked by a walk; and the strided sums at the table`s `n` are evaluated
by halving, in seven groups.
-/

namespace SIDEExplicitFormula
namespace Window

/-! ## The truncated seventh powers and their fourth difference -/

/-- `D(x) = ∑_l w_l max(x + l, 0)^7`. -/
def kD (x : ℤ) : ℤ := ∑ l ∈ Finset.range 5, bw l * (max (x + (l : ℤ)) 0) ^ 7

/-- The fourth difference of `D`. -/
def kE (x : ℤ) : ℤ := kD x - 4 * kD (x - 1) + 6 * kD (x - 2) - 4 * kD (x - 3) + kD (x - 4)

/-- `F(T) = ∑_j a_j D(j - T)`, `a_j` the integer numerators of the window`s coefficients. -/
def kF (T : ℕ) : ℤ := ∑ j ∈ Finset.Icc 16 16380, coeffInt j * kD ((j : ℤ) - (T : ℤ))

/-- The values of `E` on `-3 .. 3`, at `i = x + 3`. -/
def evv : ℕ → ℤ
  | 0 => 1
  | 1 => 120
  | 2 => 1191
  | 3 => 2416
  | 4 => 1191
  | 5 => 120
  | 6 => 1
  | _ => 0

/-- `kapTilde` as a fourth difference of `D`. -/
theorem kapTilde_eq_kD (n : ℕ) (e : ℤ) :
    kapTilde n e = ∑ k ∈ Finset.range 5, bw k * kD (e - (k : ℤ) * (n : ℤ)) := by
  unfold kapTilde kD
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show e + (l : ℤ) - (k : ℤ) * (n : ℤ) = e - (k : ℤ) * (n : ℤ) + (l : ℤ) by ring]
  ring

theorem kD_eq_zero (x : ℤ) (hx : x ≤ -4) : kD x = 0 := by
  unfold kD
  refine Finset.sum_eq_zero (fun l hl => ?_)
  have hl' : l < 5 := Finset.mem_range.1 hl
  rw [max_eq_right (show x + (l : ℤ) ≤ 0 by omega)]
  ring

theorem kD_pos (x : ℤ) (hx : 0 ≤ x) : kD x = ∑ l ∈ Finset.range 5, bw l * (x + (l : ℤ)) ^ 7 := by
  unfold kD
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [max_eq_left (show (0 : ℤ) ≤ x + (l : ℤ) by omega)]

/-- `E` is `0` off `-3 .. 3`: below, every `D` is `0`; above, `E` is a fourth difference of a cubic. -/
theorem kE_eq_zero (x : ℤ) (h : x ≤ -4 ∨ 4 ≤ x) : kE x = 0 := by
  rcases h with h | h
  · unfold kE
    rw [kD_eq_zero x h, kD_eq_zero (x - 1) (by omega), kD_eq_zero (x - 2) (by omega),
      kD_eq_zero (x - 3) (by omega), kD_eq_zero (x - 4) (by omega)]
    all_goals norm_num
  · unfold kE
    rw [kD_pos x (by omega), kD_pos (x - 1) (by omega), kD_pos (x - 2) (by omega),
      kD_pos (x - 3) (by omega), kD_pos (x - 4) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    ring

theorem kE_vals : ∀ i : ℕ, i < 7 → kE ((i : ℤ) - 3) = evv i := by
  first
  | decide +kernel
  | (intro i hi
     interval_cases i <;> simp [kE, kD, evv, bw, Finset.sum_range_succ] <;> norm_num)

/-! ## The recurrence of `F` -/

theorem kF_rec (T : ℕ) :
    kF T = 4 * kF (T + 1) - 6 * kF (T + 2) + 4 * kF (T + 3) - kF (T + 4)
      + ∑ j ∈ Finset.Icc 16 16380, coeffInt j * kE ((j : ℤ) - (T : ℤ)) := by
  have h : ∀ j : ℕ, coeffInt j * kD ((j : ℤ) - (T : ℤ))
      = 4 * (coeffInt j * kD ((j : ℤ) - ((T + 1 : ℕ) : ℤ)))
        - 6 * (coeffInt j * kD ((j : ℤ) - ((T + 2 : ℕ) : ℤ)))
        + 4 * (coeffInt j * kD ((j : ℤ) - ((T + 3 : ℕ) : ℤ)))
        - coeffInt j * kD ((j : ℤ) - ((T + 4 : ℕ) : ℤ))
        + coeffInt j * kE ((j : ℤ) - (T : ℤ)) := by
    intro j
    have e1 : (j : ℤ) - ((T + 1 : ℕ) : ℤ) = (j : ℤ) - (T : ℤ) - 1 := by omega
    have e2 : (j : ℤ) - ((T + 2 : ℕ) : ℤ) = (j : ℤ) - (T : ℤ) - 2 := by omega
    have e3 : (j : ℤ) - ((T + 3 : ℕ) : ℤ) = (j : ℤ) - (T : ℤ) - 3 := by omega
    have e4 : (j : ℤ) - ((T + 4 : ℕ) : ℤ) = (j : ℤ) - (T : ℤ) - 4 := by omega
    rw [e1, e2, e3, e4]
    unfold kE
    ring
  unfold kF
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem kF_zero (T : ℕ) (hT : 16384 ≤ T) : kF T = 0 := by
  unfold kF
  refine Finset.sum_eq_zero (fun j hj => ?_)
  have hj' : j ≤ 16380 := (Finset.mem_Icc.1 hj).2
  rw [kD_eq_zero ((j : ℤ) - (T : ℤ)) (by omega), mul_zero]

theorem coeffInt_eq_zero (j : ℕ) (h : ¬ (16 ≤ j ∧ j ≤ 16380)) : coeffInt j = 0 := by
  unfold coeffInt
  rw [if_neg h]

/-! ## The coefficient tree against Coeffs.lean`s list -/

/-- The coefficient tree read where `coeffInt` reads its list, `0` elsewhere. -/
def aGet (m : ℕ) : ℤ := if 16 ≤ m ∧ m ≤ 16380 then aTree.get m else 0

/-- The walk of the coefficient tree against a list from the index `m`. -/
def chkA : ℕ → List ℤ → Bool
  | m, [] => m == 16381
  | m, x :: xs => (aTree.get m == x) && chkA (m + 1) xs

theorem chkA_spec (l : List ℤ) : ∀ m : ℕ, chkA m l = true →
    m + l.length = 16381 ∧ ∀ i, i < l.length → aTree.get (m + i) = l.getD i 0 := by
  induction l with
  | nil =>
    intro m h
    simp only [chkA, beq_iff_eq] at h
    refine ⟨by simpa using h, fun i hi => ?_⟩
    simp at hi
  | cons x xs ih =>
    intro m h
    simp only [chkA, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := ih (m + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
      have h3 := h2 i hi'
      rw [show m + 1 + i = m + (i + 1) by omega] at h3
      simpa using h3

set_option maxHeartbeats 0 in
theorem a_ok : chkA 16 coeffList = true := by decide +kernel

theorem aGet_eq (m : ℕ) : aGet m = coeffInt m := by
  obtain ⟨hlen, hget⟩ := chkA_spec coeffList 16 a_ok
  unfold aGet coeffInt
  by_cases h : 16 ≤ m ∧ m ≤ 16380
  · rw [if_pos h, if_pos h]
    have h3 := hget (m - 16) (by omega)
    rw [show 16 + (m - 16) = m by omega] at h3
    exact h3
  · rw [if_neg h, if_neg h]

/-! ## Halving: a conjunction and a sum read in depth at most `d` -/

/-- `p (lo + i)` for every `i < len`, by halving. -/
def allDC (p : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | lo, len, 0 => if len = 0 then true else p lo
  | lo, len, d + 1 =>
    if len ≤ 1 then (if len = 0 then true else p lo)
    else allDC p lo (len / 2) d && allDC p (lo + len / 2) (len - len / 2) d

theorem allDC_spec (p : ℕ → Bool) : ∀ d lo len, len ≤ 2 ^ d → allDC p lo len d = true →
    ∀ i, i < len → p (lo + i) = true := by
  intro d
  induction d with
  | zero =>
    intro lo len hlen h i hi
    simp only [pow_zero] at hlen
    simp only [allDC] at h
    have hl : len = 1 := by omega
    have hi0 : i = 0 := by omega
    subst hl hi0
    simpa using h
  | succ d ih =>
    intro lo len hlen h i hi
    simp only [allDC] at h
    split_ifs at h with h1 h0
    · omega
    · have hl : len = 1 := by omega
      have hi0 : i = 0 := by omega
      subst hl hi0
      simpa using h
    · rw [pow_succ] at hlen
      rw [Bool.and_eq_true] at h
      by_cases hc : i < len / 2
      · exact ih lo (len / 2) (by omega) h.1 i hc
      · have h3 := ih (lo + len / 2) (len - len / 2) (by omega) h.2 (i - len / 2) (by omega)
        rw [show lo + len / 2 + (i - len / 2) = lo + i by omega] at h3
        exact h3

/-- `∑_{i < len} f (lo + i)`, by halving. -/
def sumDC (f : ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | lo, len, 0 => if len = 0 then 0 else f lo
  | lo, len, d + 1 =>
    if len ≤ 1 then (if len = 0 then 0 else f lo)
    else sumDC f lo (len / 2) d + sumDC f (lo + len / 2) (len - len / 2) d

theorem sumDC_eq (f : ℕ → ℤ) : ∀ d lo len, len ≤ 2 ^ d →
    sumDC f lo len d = ∑ i ∈ Finset.range len, f (lo + i) := by
  intro d
  induction d with
  | zero =>
    intro lo len hlen
    simp only [pow_zero] at hlen
    interval_cases len
    · simp [sumDC]
    · simp [sumDC]
  | succ d ih =>
    intro lo len hlen
    simp only [sumDC]
    split_ifs with h1 h0
    · subst h0
      simp
    · have hl : len = 1 := by omega
      subst hl
      simp
    · rw [pow_succ] at hlen
      rw [ih lo (len / 2) (by omega), ih (lo + len / 2) (len - len / 2) (by omega)]
      have e : len = len / 2 + (len - len / 2) := by omega
      conv_rhs => rw [e]
      rw [Finset.sum_range_add]
      simp only [add_assoc]

/-! ## The F tree against `F` -/

/-- The F tree read at `T < 16384`, `0` beyond. -/
def Ffast (T : ℕ) : ℤ := if T < 16384 then fTree.get T else 0

/-- The local term of the recurrence, read from the coefficient tree. -/
def locA (T : ℕ) : ℤ :=
  aGet (T - 3) * 1 + aGet (T - 3 + 1) * 120 + aGet (T - 3 + 2) * 1191 + aGet (T - 3 + 3) * 2416
    + aGet (T - 3 + 4) * 1191 + aGet (T - 3 + 5) * 120 + aGet (T - 3 + 6) * 1

/-- The recurrence at `T`, read from the two trees. -/
def recOK (T : ℕ) : Bool :=
  Ffast T == 4 * Ffast (T + 1) - 6 * Ffast (T + 2) + 4 * Ffast (T + 3) - Ffast (T + 4) + locA T

/-- The recurrence on the chunk of `1024` indices from `16 + 1024 c`. -/
def fChunkOK (c : ℕ) : Bool := allDC recOK (16 + 1024 * c) 1024 10

set_option maxHeartbeats 0 in
theorem f_ok_0 : fChunkOK 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_1 : fChunkOK 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_2 : fChunkOK 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_3 : fChunkOK 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_4 : fChunkOK 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_5 : fChunkOK 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_6 : fChunkOK 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_7 : fChunkOK 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_8 : fChunkOK 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_9 : fChunkOK 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_10 : fChunkOK 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_11 : fChunkOK 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_12 : fChunkOK 12 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_13 : fChunkOK 13 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_14 : fChunkOK 14 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem f_ok_15 : fChunkOK 15 = true := by decide +kernel

theorem f_ok (c : ℕ) (hc : c < 16) : fChunkOK c = true := by
  interval_cases c
  · exact f_ok_0
  · exact f_ok_1
  · exact f_ok_2
  · exact f_ok_3
  · exact f_ok_4
  · exact f_ok_5
  · exact f_ok_6
  · exact f_ok_7
  · exact f_ok_8
  · exact f_ok_9
  · exact f_ok_10
  · exact f_ok_11
  · exact f_ok_12
  · exact f_ok_13
  · exact f_ok_14
  · exact f_ok_15

theorem rec_holds (T : ℕ) (h1 : 16 ≤ T) (h2 : T < 16384) :
    Ffast T = 4 * Ffast (T + 1) - 6 * Ffast (T + 2) + 4 * Ffast (T + 3) - Ffast (T + 4) + locA T := by
  have hc : (T - 16) / 1024 < 16 := by omega
  have hok : allDC recOK (16 + 1024 * ((T - 16) / 1024)) 1024 10 = true := f_ok _ hc
  have h := allDC_spec recOK 10 (16 + 1024 * ((T - 16) / 1024)) 1024 (by norm_num) hok
    ((T - 16) % 1024) (Nat.mod_lt _ (by norm_num))
  rw [show 16 + 1024 * ((T - 16) / 1024) + (T - 16) % 1024 = T by omega] at h
  unfold recOK at h
  exact beq_iff_eq.1 h

theorem locA_eq (T : ℕ) : locA T = ∑ i ∈ Finset.range 7, aGet (T - 3 + i) * evv i := by
  simp only [locA, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero, evv]
  all_goals ring

/-- The local term of `F`'s recurrence is the coefficient tree`s, `T ≥ 3`. -/
theorem loc_eq (T : ℕ) (hT : 3 ≤ T) :
    ∑ j ∈ Finset.Icc 16 16380, coeffInt j * kE ((j : ℤ) - (T : ℤ)) = locA T := by
  have hU1 : ∑ j ∈ Finset.Icc 16 16380, coeffInt j * kE ((j : ℤ) - (T : ℤ))
      = ∑ j ∈ Finset.range (T + 16384), coeffInt j * kE ((j : ℤ) - (T : ℤ)) := by
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j _ hj
      rw [Finset.mem_Icc] at hj
      rw [coeffInt_eq_zero j hj, zero_mul]
  have hU2 : ∑ j ∈ Finset.Ico (T - 3) (T + 4), coeffInt j * kE ((j : ℤ) - (T : ℤ))
      = ∑ j ∈ Finset.range (T + 16384), coeffInt j * kE ((j : ℤ) - (T : ℤ)) := by
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_range]
      omega
    · intro j _ hj
      rw [Finset.mem_Ico] at hj
      rw [kE_eq_zero ((j : ℤ) - (T : ℤ)) (by omega), mul_zero]
  rw [hU1, ← hU2, Finset.sum_Ico_eq_sum_range, show T + 4 - (T - 3) = 7 by omega, locA_eq]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 7 := Finset.mem_range.1 hi
  show coeffInt (T - 3 + i) * kE (((T - 3 + i : ℕ) : ℤ) - (T : ℤ)) = aGet (T - 3 + i) * evv i
  rw [aGet_eq, show ((T - 3 + i : ℕ) : ℤ) - (T : ℤ) = (i : ℤ) - 3 by omega, kE_vals i hi']

theorem Ffast_eq_aux : ∀ d T, 16384 ≤ T + d → 16 ≤ T → Ffast T = kF T := by
  intro d
  induction d with
  | zero =>
    intro T h _
    have h1 : ¬ (T < 16384) := by omega
    rw [Ffast, if_neg h1, kF_zero T (by omega)]
  | succ d ih =>
    intro T h hT
    by_cases hb : 16384 ≤ T
    · have h1 : ¬ (T < 16384) := by omega
      rw [Ffast, if_neg h1, kF_zero T hb]
    · rw [rec_holds T hT (by omega), ih (T + 1) (by omega) (by omega), ih (T + 2) (by omega) (by omega),
        ih (T + 3) (by omega) (by omega), ih (T + 4) (by omega) (by omega), kF_rec T, loc_eq T (by omega)]

/-- **The F tree is `F`** at every `T ≥ 16`. -/
theorem Ffast_eq (T : ℕ) (h : 16 ≤ T) : Ffast T = kF T := Ffast_eq_aux 16384 T (by omega) h

/-! ## The double sum as a strided sum of `F` -/

/-- `Kt n = ∑_j ∑_m a_j a_m kapTilde n (j - n m)`, so that `K(n) = Kt n / (80640 n^4 10^34)`. -/
def Kt (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 16 16380, ∑ m ∈ Finset.Icc 16 16380, coeffInt j * coeffInt m * kapTilde n ((j : ℤ) - n * m)

theorem Kt_eq (n : ℕ) :
    Kt n = ∑ m ∈ Finset.Icc 16 16380, coeffInt m * ∑ k ∈ Finset.range 5, bw k * kF (n * (m + k)) := by
  unfold Kt
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [kF, kapTilde_eq_kD, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e : (j : ℤ) - (n : ℤ) * (m : ℤ) - (k : ℤ) * (n : ℤ) = (j : ℤ) - ((n * (m + k) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e]
  ring

/-- The last index `m` at which `n m < 16384`, at most `16380`. -/
def mtop (n : ℕ) : ℕ := min 16380 (16383 / n)

theorem Kt_eq_trunc (n : ℕ) (hn : 0 < n) :
    Kt n = ∑ m ∈ Finset.Icc 16 (mtop n), coeffInt m * ∑ k ∈ Finset.range 5, bw k * kF (n * (m + k)) := by
  have hmt : mtop n ≤ 16380 := min_le_left _ _
  rw [Kt_eq n]
  symm
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 hmt⟩
  · intro m hm hm'
    rw [Finset.mem_Icc] at hm hm'
    have h1 : 16383 / n < m := by
      by_contra hc
      exact hm' ⟨hm.1, le_min hm.2 (by omega)⟩
    rw [Nat.div_lt_iff_lt_mul hn] at h1
    have h2 : ∀ k, kF (n * (m + k)) = 0 := by
      intro k
      apply kF_zero
      have h4 := Nat.mul_le_mul (le_refl n) (Nat.le_add_right m k)
      rw [Nat.mul_comm] at h1
      omega
    simp only [h2, mul_zero, Finset.sum_const_zero]

/-- The fourth difference of the F tree along the stride `n`. -/
def gk (n m : ℕ) : ℤ :=
  Ffast (n * m) - 4 * Ffast (n * (m + 1)) + 6 * Ffast (n * (m + 2)) - 4 * Ffast (n * (m + 3)) + Ffast (n * (m + 4))

/-- The strided sum at `n`, by halving. -/
def KtFast (n : ℕ) : ℤ := sumDC (fun m => aGet m * gk n m) 16 (mtop n + 1 - 16) 14

theorem sum_bw_kF (n m : ℕ) (hn : 0 < n) (hm : 16 ≤ m) :
    ∑ k ∈ Finset.range 5, bw k * kF (n * (m + k)) = gk n m := by
  have hF : ∀ k, kF (n * (m + k)) = Ffast (n * (m + k)) := by
    intro k
    symm
    apply Ffast_eq
    have h4 := Nat.mul_le_mul (show 1 ≤ n by omega) (show 16 ≤ m + k by omega)
    omega
  simp only [hF]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bw, gk, zero_add, add_zero]
  ring

theorem Kt_eq_fast (n : ℕ) (hn : 0 < n) : Kt n = KtFast n := by
  have hmt : mtop n ≤ 16380 := min_le_left _ _
  have hlen : mtop n + 1 - 16 ≤ 2 ^ 14 := by
    have h14 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    omega
  rw [Kt_eq_trunc n hn, KtFast, sumDC_eq (fun m => aGet m * gk n m) 14 16 (mtop n + 1 - 16) hlen]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show coeffInt (16 + i) * ∑ k ∈ Finset.range 5, bw k * kF (n * (16 + i + k)) = aGet (16 + i) * gk n (16 + i)
  rw [aGet_eq, sum_bw_kF n (16 + i) hn (by omega)]

/-! ## The values -/

/-- **The window`s autocorrelation at `log n` through `Kt n`**, `n ≥ 1`. -/
theorem windowK_log_eq_Kt (n : ℕ) (hn : 0 < n) :
    windowK (Real.log n) = ((Real.sqrt n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) : ℝ) : ℂ) := by
  rw [windowK_log_eq_basis hn]
  congr 2
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [kappaB_eq_kapTilde n hn, coeff, coeffScale, Kt]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  first
  | ring
  | (field_simp
     ring)

/-- An entry of the table: `n ≥ 1` and the strided sum equal to its `Kt`. -/
def ktOK (p : ℕ × ℤ) : Bool := decide (0 < p.1) && (KtFast p.1 == p.2)

set_option maxHeartbeats 0 in
theorem kt_ok_0 : ktTab0.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_1 : ktTab1.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_2 : ktTab2.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_3 : ktTab3.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_4 : ktTab4.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_5 : ktTab5.all ktOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kt_ok_6 : ktTab6.all ktOK = true := by decide +kernel

theorem all_append_kt (l₁ l₂ : List (ℕ × ℤ)) (f : ℕ × ℤ → Bool) :
    (l₁ ++ l₂).all f = (l₁.all f && l₂.all f) := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
    show (f x && (xs ++ l₂).all f) = ((f x && xs.all f) && l₂.all f)
    rw [ih, Bool.and_assoc]

theorem kt_all : ktTable.all ktOK = true := by
  simp only [ktTable, all_append_kt, kt_ok_0, kt_ok_1, kt_ok_2, kt_ok_3, kt_ok_4, kt_ok_5, kt_ok_6,
    Bool.true_and]

/-- **The values `K(n)` of the certificate**: at each `(n, v)` of the table, the window`s autocorrelation at `log n` is
`√n · v / (80640 n^4 10^34)`. -/
theorem windowK_log_kt : ∀ p ∈ ktTable,
    windowK (Real.log p.1) = ((Real.sqrt p.1 * ((p.2 : ℝ) / (80640 * (p.1 : ℝ) ^ 4 * 10 ^ 34)) : ℝ) : ℂ) := by
  intro p hp
  have h := List.all_eq_true.1 kt_all p hp
  simp only [ktOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [windowK_log_eq_Kt p.1 h.1, Kt_eq_fast p.1 h.1, h.2]

end Window
end SIDEExplicitFormula
