/-
b729, (R339)(3), (L1): THE LATTICE SWEEP'S TABLE IS r_Q. For D ≤ -15 the sweep over the box [-s, s]², s the least with s² > 2N, counts the
representations of each n ≤ N, and so does rQ over its box [-n, n]²: every representation lies in both, since 2 Q(x, y) ≥ x² + y².
-/
import SIDEExplicitFormula.C2Tab
import Mathlib

namespace C2Walk

theorem sweepRow_succ (D : Int) (N : Nat) (x : Int) (k : Nat) (y : Int) (t : Tab) :
    sweepRow D N x (k + 1) y t = sweepRow D N x k (y + 1) (bump D N x y t) := by
  first
    | (rw [sweepRow]; cases bump D N x y t <;> rfl)
    | (unfold sweepRow; cases bump D N x y t <;> rfl)
    | (simp only [sweepRow]; split <;> rfl)

theorem get_bump (D : Int) (N : Nat) (x y : Int) (t : Tab) (n : Nat) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    Tab.get (bump D N x y t) n = Tab.get t n + (if pform D x y = (n : Int) then 1 else 0) := by
  unfold bump
  generalize pform D x y = Q
  by_cases hc : 0 ≤ Q ∧ Q ≤ (N : Int)
  · rw [if_pos hc, get_set 64 t Q.toNat n (Tab.get t Q.toNat + 1) (by omega)]
    by_cases he : Q = (n : Int)
    · have h1 : n = Q.toNat := by omega
      rw [if_pos h1, if_pos he, ← h1]
    · have h1 : ¬ n = Q.toNat := by omega
      rw [if_neg h1, if_neg he, add_zero]
  · rw [if_neg hc]
    have he : ¬ Q = (n : Int) := by
      intro h
      exact hc ⟨by omega, by omega⟩
    rw [if_neg he, add_zero]

theorem get_sweepRow (D : Int) (N : Nat) (x : Int) (n : Nat) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    ∀ (k : Nat) (y : Int) (t : Tab), Tab.get (sweepRow D N x k y t) n =
      Tab.get t n + ∑ j ∈ Finset.range k, (if pform D x (y + (j : Int)) = (n : Int) then (1 : Int) else 0) := by
  intro k
  induction k with
  | zero =>
    intro y t
    simp [sweepRow]
  | succ k ih =>
    intro y t
    have e : ∀ j : Nat, y + 1 + (j : Int) = y + ((j + 1 : Nat) : Int) := by
      intro j
      push_cast
      ring
    rw [sweepRow_succ, ih, get_bump D N x y t n hn hN, Finset.sum_range_succ' _ k]
    simp only [e, Nat.cast_zero, add_zero]
    ring

theorem get_sweepAll (D : Int) (N s : Nat) (n : Nat) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    ∀ (k : Nat) (x : Int) (t : Tab), Tab.get (sweepAll D N s k x t) n =
      Tab.get t n + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (2 * s + 1),
        (if pform D (x + (i : Int)) (-(s : Int) + (j : Int)) = (n : Int) then (1 : Int) else 0) := by
  intro k
  induction k with
  | zero =>
    intro x t
    simp [sweepAll]
  | succ k ih =>
    intro x t
    have e : ∀ i : Nat, x + 1 + (i : Int) = x + ((i + 1 : Nat) : Int) := by
      intro i
      push_cast
      ring
    rw [sweepAll_succ, ih, get_sweepRow D N x n hn hN, Finset.sum_range_succ' _ k]
    simp only [e, Nat.cast_zero, add_zero]
    ring

/-- the count over the box [-s, s]² -/
def BC (D : Int) (n s : Nat) : Int :=
  ∑ i ∈ Finset.range (2 * s + 1), ∑ j ∈ Finset.range (2 * s + 1),
    (if pform D (-(s : Int) + (i : Int)) (-(s : Int) + (j : Int)) = (n : Int) then (1 : Int) else 0)

theorem get_rTab (D : Int) (N n : Nat) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    Tab.get (rTab D N) n = BC D n (side N) := by
  unfold rTab BC
  rw [get_sweepAll D N (side N) n hn hN]
  have h0 : Tab.get Tab.leaf n = 0 := by
    first
      | rfl
      | simp [Tab.get]
  rw [h0, zero_add]

theorem cp_map {β : Type} (p : β → Bool) (h : Nat → β) (m : Nat) :
    (((List.range m).map h).countP p : Int) = ∑ j ∈ Finset.range m, (if p (h j) = true then (1 : Int) else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.countP_append, Nat.cast_add, ih, Finset.sum_range_succ]
    congr 1
    cases hp : p (h m) <;> simp [List.countP_cons, hp]

theorem cp_range {β : Type} (p : β → Bool) (g : Nat → List β) (m : Nat) :
    (((List.range m).flatMap g).countP p : Int) = ∑ i ∈ Finset.range m, ((g i).countP p : Int) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.countP_append, Nat.cast_add, ih, Finset.sum_range_succ]
    congr 1
    simp

theorem rQ_eq (D : Int) (n : Nat) : (rQ D n : Int) = BC D n n := by
  unfold rQ BC
  rw [cp_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [cp_map]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : (i : Int) - (n : Int) = -(n : Int) + (i : Int) := by ring
  have e2 : (j : Int) - (n : Int) = -(n : Int) + (j : Int) := by ring
  first
    | (simp only [decide_eq_true_eq, e1, e2]; done)
    | (simp only [decide_eq_true_eq, e1, e2]; split_ifs <;> rfl)
    | simp [e1, e2]

/-- the box as a Finset of Int -/
noncomputable def Ibox (s : Nat) : Finset Int := Finset.Icc (-(s : Int)) (s : Int)

theorem range_sum (s : Nat) (f : Int → Int) :
    ∑ i ∈ Finset.range (2 * s + 1), f (-(s : Int) + (i : Int)) = ∑ x ∈ Ibox s, f x := by
  have hI : Ibox s = (Finset.range (2 * s + 1)).image (fun i : Nat => -(s : Int) + (i : Int)) := by
    ext x
    simp only [Ibox, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x + s).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, hx⟩
      constructor <;> omega
  rw [hI]
  symm
  apply Finset.sum_image
  intro i _ j _ h
  have h' : -(s : Int) + (i : Int) = -(s : Int) + (j : Int) := h
  omega

theorem BC_box (D : Int) (n s : Nat) :
    BC D n s = ∑ p ∈ Ibox s ×ˢ Ibox s, (if pform D p.1 p.2 = (n : Int) then (1 : Int) else 0) := by
  unfold BC
  have h : ∑ p ∈ Ibox s ×ˢ Ibox s, (if pform D p.1 p.2 = (n : Int) then (1 : Int) else 0) =
      ∑ x ∈ Ibox s, ∑ y ∈ Ibox s, (if pform D x y = (n : Int) then (1 : Int) else 0) :=
    Finset.sum_product' _ _ (fun x y => if pform D x y = (n : Int) then (1 : Int) else 0)
  rw [h, ← range_sum s (fun x => ∑ y ∈ Ibox s, (if pform D x y = (n : Int) then (1 : Int) else 0))]
  apply Finset.sum_congr rfl
  intro i _
  exact range_sum s (fun y => if pform D (-(s : Int) + (i : Int)) y = (n : Int) then (1 : Int) else 0)

theorem BC_eq (D : Int) (n s t : Nat) (hst : s ≤ t)
    (hsol : ∀ x y : Int, pform D x y = (n : Int) → x ∈ Ibox s ∧ y ∈ Ibox s) : BC D n t = BC D n s := by
  rw [BC_box, BC_box]
  symm
  have hI : Ibox s ⊆ Ibox t := by
    unfold Ibox
    apply Finset.Icc_subset_Icc <;> omega
  apply Finset.sum_subset (Finset.product_subset_product hI hI)
  intro p _ hnot
  have hne : ¬ pform D p.1 p.2 = (n : Int) := fun he => hnot (Finset.mem_product.mpr (hsol p.1 p.2 he))
  exact if_neg hne

theorem pform_two (D x y : Int) (hD : D ≤ -15) : x * x + y * y ≤ 2 * pform D x y := by
  unfold pform
  split_ifs with h
  · have c : 1 ≤ -D / 4 := by omega
    have hy := mul_nonneg (sub_nonneg.mpr c) (mul_self_nonneg y)
    nlinarith [mul_self_nonneg x]
  · have c : 1 ≤ (1 - D) / 4 := by omega
    have hy := mul_nonneg (sub_nonneg.mpr c) (mul_self_nonneg y)
    nlinarith [mul_self_nonneg (x + y)]

theorem mem_Ibox (s : Nat) (x B : Int) (h : x * x ≤ B) (hs : B < ((s : Int) + 1) * ((s : Int) + 1)) : x ∈ Ibox s := by
  simp only [Ibox, Finset.mem_Icc]
  have hs0 : (0 : Int) ≤ (s : Int) + 1 := by omega
  constructor
  · by_contra hc
    have h1 : (s : Int) + 1 ≤ -x := by omega
    have h2 := mul_self_le_mul_self hs0 h1
    have h3 : (-x) * (-x) = x * x := by ring
    linarith
  · by_contra hc
    have h1 : (s : Int) + 1 ≤ x := by omega
    have h2 := mul_self_le_mul_self hs0 h1
    linarith

theorem sideAux_spec (N : Nat) : ∀ (f s : Nat), 2 * N < (s + f) * (s + f) → 2 * N < sideAux N f s * sideAux N f s := by
  intro f
  induction f with
  | zero =>
    intro s h
    have h0 : sideAux N 0 s = s := by
      first
        | rfl
        | simp [sideAux]
    rw [h0]
    simpa using h
  | succ f ih =>
    intro s h
    have h0 : sideAux N (f + 1) s = if 2 * N < s * s then s else sideAux N f (s + 1) := by
      first
        | rfl
        | simp [sideAux]
        | rw [sideAux]
    rw [h0]
    by_cases hc : 2 * N < s * s
    · rw [if_pos hc]
      exact hc
    · rw [if_neg hc]
      apply ih
      have e : s + 1 + f = s + (f + 1) := by omega
      rw [e]
      exact h

theorem side_spec (N : Nat) : 2 * N < side N * side N := by
  unfold side
  apply sideAux_spec
  nlinarith

/-- (L1) AT ANY N: the sweep's table reads r_Q at every n ≤ N -/
theorem get_rTab_eq (D : Int) (N n : Nat) (hD : D ≤ -15) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    Tab.get (rTab D N) n = (rQ D n : Int) := by
  rw [get_rTab D N n hn hN, rQ_eq]
  have hbound : ∀ x y : Int, pform D x y = (n : Int) → x * x ≤ 2 * (n : Int) ∧ y * y ≤ 2 * (n : Int) := by
    intro x y h
    have h2 := pform_two D x y hD
    rw [h] at h2
    constructor <;> nlinarith [mul_self_nonneg x, mul_self_nonneg y]
  have hn1 : 2 * (n : Int) < ((n : Int) + 1) * ((n : Int) + 1) := by nlinarith [mul_self_nonneg (n : Int)]
  have hs0 := side_spec N
  have hs1 : 2 * (n : Int) < ((side N : Int) + 1) * ((side N : Int) + 1) := by
    have h1 : (2 * n : Nat) < side N * side N := lt_of_le_of_lt (Nat.mul_le_mul_left 2 hn) hs0
    have h2 : ((2 * n : Nat) : Int) < ((side N * side N : Nat) : Int) := by exact_mod_cast h1
    push_cast at h2
    nlinarith [h2, (Nat.cast_nonneg (side N) : (0 : Int) ≤ (side N : Int))]
  have hsolN : ∀ x y : Int, pform D x y = (n : Int) → x ∈ Ibox n ∧ y ∈ Ibox n := by
    intro x y h
    obtain ⟨h1, h2⟩ := hbound x y h
    exact ⟨mem_Ibox n x _ h1 hn1, mem_Ibox n y _ h2 hn1⟩
  have hsolS : ∀ x y : Int, pform D x y = (n : Int) → x ∈ Ibox (side N) ∧ y ∈ Ibox (side N) := by
    intro x y h
    obtain ⟨h1, h2⟩ := hbound x y h
    exact ⟨mem_Ibox _ x _ h1 hs1, mem_Ibox _ y _ h2 hs1⟩
  rcases le_total (side N) n with hle | hle
  · exact (BC_eq D n (side N) n hle hsolS).symm
  · exact BC_eq D n n (side N) hle hsolN

end C2Walk
