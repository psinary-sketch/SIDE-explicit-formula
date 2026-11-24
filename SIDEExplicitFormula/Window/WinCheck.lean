import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.GetD

/-!
# A list of integers checked against a function read at a window that moves by one place

`winOK F w n xs` reads the places of `xs` against `F n w`, `F (n + 1) w.tail`, and so on; `winOK_spec` reads each place
`j` of `xs` as `F (n + j) (w.drop j)`, and `winOK_append` cuts a check at the join of two lists. It reads no datum.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The check of a list, place by place, against `F` at a window that moves by one place. -/
def winOK (F : ℕ → List ℤ → ℤ) : List ℤ → ℕ → List ℤ → Bool
  | _, _, [] => true
  | w, n, x :: xs => (x == F n w) && winOK F w.tail (n + 1) xs

theorem tail_drop_eq (w : List ℤ) (j : ℕ) : w.tail.drop j = w.drop (j + 1) := by
  cases w with
  | nil => simp
  | cons a t => rfl

theorem drop_drop_add (l : List ℤ) : ∀ (a b : ℕ), (l.drop a).drop b = l.drop (a + b) := by
  induction l with
  | nil => intro a b; simp
  | cons x t ih =>
    intro a b
    cases a with
    | zero => simp
    | succ a =>
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e]
      exact ih a b

theorem getD_drop_add (l : List ℤ) : ∀ (q i : ℕ), (l.drop q).getD i 0 = l.getD (q + i) 0 := by
  induction l with
  | nil => intro q i; simp
  | cons a t ih =>
    intro q i
    cases q with
    | zero => simp
    | succ q =>
      have e : q + 1 + i = (q + i) + 1 := by omega
      rw [e]
      first
      | exact ih q i
      | simpa using ih q i

theorem winOK_spec (F : ℕ → List ℤ → ℤ) : ∀ (xs w : List ℤ) (n : ℕ), winOK F w n xs = true →
    ∀ j, j < xs.length → xs.getD j 0 = F (n + j) (w.drop j) := by
  intro xs
  induction xs with
  | nil =>
    intro w n _ j hj
    simp at hj
  | cons x xs ih =>
    intro w n h j hj
    simp only [winOK, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have hj' : j < xs.length := by simp only [List.length_cons] at hj; omega
      have h3 := ih w.tail (n + 1) h.2 j hj'
      rw [tail_drop_eq, show n + 1 + j = n + (j + 1) by omega] at h3
      simpa using h3

theorem winOK_append (F : ℕ → List ℤ → ℤ) : ∀ (l1 l2 w : List ℤ) (n : ℕ),
    winOK F w n (l1 ++ l2) = (winOK F w n l1 && winOK F (w.drop l1.length) (n + l1.length) l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 w n; simp [winOK]
  | cons x xs ih =>
    intro l2 w n
    have e1 : w.tail.drop xs.length = w.drop (xs.length + 1) := tail_drop_eq w xs.length
    have e2 : n + 1 + xs.length = n + (xs.length + 1) := by omega
    simp only [List.cons_append, winOK, ih, List.length_cons, Bool.and_assoc, e1, e2]

end Window
end SIDEExplicitFormula
