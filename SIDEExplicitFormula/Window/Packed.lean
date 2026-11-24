import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Packed integers and convolution sums, reading no datum

The general lemmas of the route for the far sum of L9c: a list packed as the digits of one integer in a base `b` (`packL`),
its sum form (`packL_eq_sum`) and the packing of a list of chunks (`packL_flatten`); the convolution sum of two sequences over
`n` places (`convR`); a double sum whose kernel reads the sum of its indices, written over those sums (`sum_sq_conv`), and one
whose kernel reads the difference of its indices, written over the lags (`lag_sum`); the product of two packings as the
packing of their convolution sums (`packed_mul`); a bound on each convolution sum (`convR_bound`); two balanced packings equal
exactly where their digits are (`packed_inj`); and so a checked product of packed lists gives each convolution sum as a digit
of the product (`conv_of_packed`, `conv_of_packedL`). Each statement holds of any lists; no list of the window is read here.
-/

namespace SIDEExplicitFormula
namespace Window

/-! ## Packing a list -/

/-- A list packed as the digits of one integer in the base `b`, its head the lowest digit. -/
def packL (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + b * packL b xs

/-- Chunk values joined in the base `B`, the head the lowest. -/
def joinV (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | v :: vs => v + B * joinV B vs

theorem packL_nil (b : ℤ) : packL b [] = 0 := rfl

theorem packL_cons (b x : ℤ) (xs : List ℤ) : packL b (x :: xs) = x + b * packL b xs := rfl

theorem joinV_nil (B : ℤ) : joinV B [] = 0 := rfl

theorem joinV_cons (B v : ℤ) (vs : List ℤ) : joinV B (v :: vs) = v + B * joinV B vs := rfl

theorem packL_append (b : ℤ) (l₁ l₂ : List ℤ) :
    packL b (l₁ ++ l₂) = packL b l₁ + b ^ l₁.length * packL b l₂ := by
  induction l₁ with
  | nil =>
    rw [List.nil_append, packL_nil, List.length_nil, pow_zero]
    ring
  | cons x xs ih =>
    rw [List.cons_append, packL_cons, ih, packL_cons, List.length_cons, pow_succ]
    ring

theorem getD_cons_zero' (x : ℤ) (xs : List ℤ) : (x :: xs).getD 0 0 = x := by
  first
  | rfl
  | simp

theorem getD_cons_succ' (x : ℤ) (xs : List ℤ) (k : ℕ) : (x :: xs).getD (k + 1) 0 = xs.getD k 0 := by
  first
  | rfl
  | simp

theorem packL_eq_sum (b : ℤ) (l : List ℤ) :
    packL b l = ∑ k ∈ Finset.range l.length, l.getD k 0 * b ^ k := by
  induction l with
  | nil =>
    rw [packL_nil, List.length_nil, Finset.sum_range_zero]
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', packL_cons, ih, getD_cons_zero', pow_zero, mul_one, Finset.mul_sum]
    have e : ∀ k ∈ Finset.range xs.length,
        (x :: xs).getD (k + 1) 0 * b ^ (k + 1) = b * (xs.getD k 0 * b ^ k) := by
      intro k _
      rw [getD_cons_succ', pow_succ]
      ring
    rw [Finset.sum_congr rfl e]
    ring

/-- A list of chunks, each of `m` places, packed: the packed values of the chunks joined in the base `b ^ m`. -/
theorem packL_flatten (b : ℤ) (m : ℕ) :
    ∀ cs : List (List ℤ), (∀ c ∈ cs, c.length = m) → packL b cs.flatten = joinV (b ^ m) (cs.map (packL b))
  | [], _ => by
    rw [List.flatten_nil, List.map_nil, packL_nil, joinV_nil]
  | c :: cs, h => by
    have hc : c.length = m := h c (List.mem_cons.mpr (Or.inl rfl))
    have hs : ∀ c' ∈ cs, c'.length = m := fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc'))
    rw [List.flatten_cons, packL_append, List.map_cons, joinV_cons, hc, packL_flatten b m cs hs]

/-- Each entry of a list read at its index, below its length. -/
theorem getD_of_forall {P : ℤ → Prop} :
    ∀ (l : List ℤ), (∀ x ∈ l, P x) → ∀ i < l.length, P (l.getD i 0)
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: xs, h, 0, _ => by
    rw [getD_cons_zero']
    exact h x (List.mem_cons.mpr (Or.inl rfl))
  | x :: xs, h, i + 1, hi => by
    rw [getD_cons_succ']
    have hi' : i < xs.length := by
      rw [List.length_cons] at hi
      omega
    exact getD_of_forall xs (fun y hy => h y (List.mem_cons.mpr (Or.inr hy))) i hi'

/-- A check by the kernel over a list, read as a statement of each entry. -/
theorem forall_of_all {P : ℤ → Prop} [DecidablePred P] (l : List ℤ)
    (h : (l.all fun x => decide (P x)) = true) : ∀ x ∈ l, P x := by
  intro x hx
  first
  | exact of_decide_eq_true (List.all_eq_true.mp h x hx)
  | (simp only [List.all_eq_true, decide_eq_true_eq] at h
     exact h x hx)

/-! ## Convolution sums -/

/-- The convolution sum at `k` of two sequences over `n` places: the sum of `u i * v j` over `i, j < n` with `i + j = k`. -/
def convR {R : Type*} [CommRing R] (n : ℕ) (u v : ℕ → R) (k : ℕ) : R :=
  ∑ i ∈ Finset.range n, if i ≤ k ∧ k - i < n then u i * v (k - i) else 0

/-- A sum over `k < 2 n` of the terms with `i ≤ k < i + n`, written over `j < n`. -/
theorem shift_sum {R : Type*} [AddCommMonoid R] (n i : ℕ) (hi : i < n) (h : ℕ → R) :
    ∑ k ∈ Finset.range (2 * n), (if i ≤ k ∧ k - i < n then h k else 0) = ∑ j ∈ Finset.range n, h (i + j) := by
  have e : (Finset.range (2 * n)).filter (fun k => i ≤ k ∧ k - i < n) = Finset.Ico i (i + n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro hk
      omega
    · intro hk
      omega
  have e2 : ∑ k ∈ Finset.range (2 * n), (if i ≤ k ∧ k - i < n then h k else 0) = ∑ k ∈ Finset.Ico i (i + n), h k := by
    rw [← e, Finset.sum_filter]
  rw [e2, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- **The double sum by the sums of its indices**: a double sum over `i, j < n` whose kernel reads `i + j` is the sum over
`k < 2 n` of the convolution sum at `k` times the kernel at `k`. -/
theorem sum_sq_conv {R : Type*} [CommRing R] (n : ℕ) (u v G : ℕ → R) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, u i * v j * G (i + j) =
      ∑ k ∈ Finset.range (2 * n), convR n u v k * G k := by
  unfold convR
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  rw [shift_sum n i hi']
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

/-- **`lag_sum`**: a double sum over `i, j < n` whose kernel reads the difference `i - j` is the sum over the lags, the
convolution of `u` with `u` turned, at `k`, times the kernel at `k - (n - 1)`. -/
theorem lag_sum {R : Type*} [CommRing R] (n : ℕ) (u : ℕ → R) (K : ℤ → R) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, u i * u j * K ((i : ℤ) - j) =
      ∑ k ∈ Finset.range (2 * n), convR n u (fun j => u (n - 1 - j)) k * K ((k : ℤ) - ((n : ℤ) - 1)) := by
  rw [← sum_sq_conv n u (fun j => u (n - 1 - j)) (fun k => K ((k : ℤ) - ((n : ℤ) - 1)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hr := Finset.sum_range_reflect (fun j => u i * u j * K ((i : ℤ) - j)) n
  rw [← hr]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have e : ((i : ℤ) - ((n - 1 - j : ℕ) : ℤ)) = (((i + j : ℕ) : ℤ) - ((n : ℤ) - 1)) := by
    omega
  rw [e]

/-- **`packed_mul`**: the product of two packings over `n` places is the packing over `2 n` places of the convolution sums. -/
theorem packed_mul (b : ℤ) (n : ℕ) (u v : ℕ → ℤ) :
    (∑ i ∈ Finset.range n, u i * b ^ i) * (∑ j ∈ Finset.range n, v j * b ^ j) =
      ∑ k ∈ Finset.range (2 * n), convR n u v k * b ^ k := by
  rw [Finset.sum_mul_sum, ← sum_sq_conv n u v (fun k => b ^ k)]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **`convR_bound`**: where each entry over `n` places is at most `M` in absolute value, each convolution sum is at most
`n M ^ 2`. -/
theorem convR_bound {n : ℕ} {u v : ℕ → ℤ} {M : ℤ} (hu : ∀ i < n, |u i| ≤ M) (hv : ∀ j < n, |v j| ≤ M) (k : ℕ) :
    |convR n u v k| ≤ n * (M * M) := by
  unfold convR
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have key : ∀ i ∈ Finset.range n, |(if i ≤ k ∧ k - i < n then u i * v (k - i) else 0)| ≤ M * M := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hu i hi')
    split_ifs with hc
    · rw [abs_mul]
      exact mul_le_mul (hu i hi') (hv (k - i) hc.2) (abs_nonneg _) hM0
    · rw [abs_zero]
      exact mul_nonneg hM0 hM0
  calc _ ≤ ∑ i ∈ Finset.range n, M * M := Finset.sum_le_sum key
    _ = n * (M * M) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`packed_inj`**: two packings over `n` places in a base `b ≥ 2`, each digit strictly within `b / 2` of `0`, are equal
exactly where their digits are. -/
theorem packed_inj {b : ℤ} (hb : 2 ≤ b) :
    ∀ (n : ℕ) (u v : ℕ → ℤ), (∀ k < n, -b < 2 * u k ∧ 2 * u k < b) → (∀ k < n, -b < 2 * v k ∧ 2 * v k < b) →
      ∑ k ∈ Finset.range n, u k * b ^ k = ∑ k ∈ Finset.range n, v k * b ^ k → ∀ k < n, u k = v k := by
  intro n
  induction n with
  | zero =>
    intro u v _ _ _ k hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro u v hu hv h
    have hsplit : ∀ w : ℕ → ℤ, ∑ k ∈ Finset.range (n + 1), w k * b ^ k =
        b * ∑ k ∈ Finset.range n, w (k + 1) * b ^ k + w 0 := by
      intro w
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one]
      have e : ∀ k ∈ Finset.range n, w (k + 1) * b ^ (k + 1) = b * (w (k + 1) * b ^ k) := by
        intro k _
        ring
      rw [Finset.sum_congr rfl e]
    rw [hsplit u, hsplit v] at h
    obtain ⟨hu1, hu2⟩ := hu 0 (Nat.succ_pos n)
    obtain ⟨hv1, hv2⟩ := hv 0 (Nat.succ_pos n)
    have hS : ∑ k ∈ Finset.range n, v (k + 1) * b ^ k - ∑ k ∈ Finset.range n, u (k + 1) * b ^ k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := Int.lt_iff_add_one_le.mp hlt
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ b - 2)
          (by linarith : (0 : ℤ) ≤ -(∑ k ∈ Finset.range n, v (k + 1) * b ^ k - ∑ k ∈ Finset.range n, u (k + 1) * b ^ k + 1))]
      · have h1 := Int.lt_iff_add_one_le.mp hgt
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ b - 2)
          (by linarith : (0 : ℤ) ≤ ∑ k ∈ Finset.range n, v (k + 1) * b ^ k - ∑ k ∈ Finset.range n, u (k + 1) * b ^ k - 1)]
    have hSuv : ∑ k ∈ Finset.range n, u (k + 1) * b ^ k = ∑ k ∈ Finset.range n, v (k + 1) * b ^ k := by
      linarith
    have h0 : u 0 = v 0 := by
      rw [hSuv] at h
      linarith
    have ih' := ih (fun k => u (k + 1)) (fun k => v (k + 1))
      (fun k hk => hu (k + 1) (by omega)) (fun k hk => hv (k + 1) (by omega)) hSuv
    intro k hk
    cases k with
    | zero => exact h0
    | succ k => exact ih' k (by omega)

/-- **`conv_of_packed`**: where the product of two packings over `n` places equals the packing over `2 n` places of `d`,
each digit of `d` within `b / 2` and `2 n M ^ 2 < b`, each convolution sum is the digit of `d` at its place. -/
theorem conv_of_packed {b M : ℤ} (hb : 2 ≤ b) (n : ℕ) (u v d : ℕ → ℤ)
    (hu : ∀ i < n, |u i| ≤ M) (hv : ∀ j < n, |v j| ≤ M) (hbM : 2 * (n * (M * M)) < b)
    (hd : ∀ k < 2 * n, -b < 2 * d k ∧ 2 * d k < b)
    (hprod : (∑ i ∈ Finset.range n, u i * b ^ i) * (∑ j ∈ Finset.range n, v j * b ^ j) =
      ∑ k ∈ Finset.range (2 * n), d k * b ^ k) :
    ∀ k < 2 * n, convR n u v k = d k := by
  rw [packed_mul] at hprod
  refine packed_inj hb (2 * n) (convR n u v) d (fun k _ => ?_) hd hprod
  have h1 := abs_le.mp (convR_bound hu hv k)
  constructor
  · linarith [h1.1]
  · linarith [h1.2]

/-- **`conv_of_packedL`**: `conv_of_packed` read on lists: lists `l` and `r` of one length `n` with entries within `M`, a
list `d` of `2 n` entries within `b / 2`, and the product of the packings of `l` and `r` equal to the packing of `d`. -/
theorem conv_of_packedL {b M : ℤ} (hb : 2 ≤ b) (l r d : List ℤ) (hr : r.length = l.length)
    (hd : d.length = 2 * l.length) (hu : ∀ x ∈ l, -M ≤ x ∧ x ≤ M) (hv : ∀ x ∈ r, -M ≤ x ∧ x ≤ M)
    (hbM : 2 * (l.length * (M * M)) < b) (hdb : ∀ x ∈ d, -b < 2 * x ∧ 2 * x < b)
    (hprod : packL b l * packL b r = packL b d) :
    ∀ k < 2 * l.length, convR l.length (fun i => l.getD i 0) (fun j => r.getD j 0) k = d.getD k 0 := by
  rw [packL_eq_sum b l, packL_eq_sum b r, packL_eq_sum b d, hr, hd] at hprod
  have hu' : ∀ i < l.length, |l.getD i 0| ≤ M := fun i hi =>
    abs_le.mpr (getD_of_forall (P := fun x => -M ≤ x ∧ x ≤ M) l hu i hi)
  have hv' : ∀ j < l.length, |r.getD j 0| ≤ M := fun j hj =>
    abs_le.mpr (getD_of_forall (P := fun x => -M ≤ x ∧ x ≤ M) r hv j (by rw [hr]; exact hj))
  have hd' : ∀ k < 2 * l.length, -b < 2 * d.getD k 0 ∧ 2 * d.getD k 0 < b :=
    fun k hk => getD_of_forall (P := fun x => -b < 2 * x ∧ 2 * x < b) d hdb k (by rw [hd]; exact hk)
  exact conv_of_packed hb l.length (fun i => l.getD i 0) (fun j => r.getD j 0) (fun k => d.getD k 0) hu' hv' hbM hd' hprod

end Window
end SIDEExplicitFormula
