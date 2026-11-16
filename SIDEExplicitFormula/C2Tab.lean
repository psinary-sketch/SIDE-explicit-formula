/-
b729, (R339)(3): THE TABLE'S GET AND SET. `Tab.get` after `Tab.set` reads what was set and leaves every other key, with the depth bound.
-/
import SIDEExplicitFormula.C2Chain
import Mathlib

namespace C2Walk

theorem get_node (l : Tab) (x : Int) (r : Tab) (n : Nat) :
    Tab.get (Tab.node l x r) n = if n = 0 then x else if n % 2 = 1 then Tab.get l (n / 2) else Tab.get r (n / 2 - 1) := by
  first
    | rfl
    | simp [Tab.get]
    | rw [Tab.get]

theorem get_leaf (n : Nat) : Tab.get Tab.leaf n = 0 := by
  first
    | rfl
    | simp [Tab.get]

theorem get_eta (t : Tab) (m : Nat) : Tab.get t m = Tab.get (Tab.node (Tab.lft t) (Tab.val t) (Tab.rgt t)) m := by
  cases t with
  | leaf => simp [Tab.lft, Tab.val, Tab.rgt, get_node, get_leaf]
  | node l x r => simp [Tab.lft, Tab.val, Tab.rgt]

theorem set_succ (k : Nat) (t : Tab) (n : Nat) (x : Int) :
    Tab.set (k + 1) t n x =
      if n = 0 then Tab.node (Tab.lft t) x (Tab.rgt t)
      else if n % 2 = 1 then Tab.node (Tab.set k (Tab.lft t) (n / 2) x) (Tab.val t) (Tab.rgt t)
      else Tab.node (Tab.lft t) (Tab.val t) (Tab.set k (Tab.rgt t) (n / 2 - 1) x) := by
  first
    | rfl
    | simp [Tab.set]
    | rw [Tab.set]

theorem get_set : ∀ (k : Nat) (t : Tab) (n m : Nat) (x : Int), n + 1 < 2 ^ k →
    Tab.get (Tab.set k t n x) m = if m = n then x else Tab.get t m := by
  intro k
  induction k with
  | zero =>
    intro t n m x h
    exfalso
    have h' : n + 1 < 1 := by simpa using h
    omega
  | succ k ih =>
    intro t n m x h
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    rw [hp] at h
    obtain ⟨P, hP⟩ : ∃ P : Nat, P = 2 ^ k := ⟨_, rfl⟩
    rw [← hP] at h
    rw [set_succ, get_eta t m]
    by_cases h0 : n = 0
    · rw [if_pos h0]
      simp only [get_node]
      split_ifs <;> first | rfl | omega
    · rw [if_neg h0]
      by_cases h1 : n % 2 = 1
      · rw [if_pos h1]
        have hk : n / 2 + 1 < 2 ^ k := by
          rw [← hP]
          omega
        have key := ih (Tab.lft t) (n / 2) (m / 2) x hk
        simp only [get_node]
        split_ifs at key ⊢ <;> first | exact key | rfl | omega
      · rw [if_neg h1]
        have hk : n / 2 - 1 + 1 < 2 ^ k := by
          rw [← hP]
          omega
        have key := ih (Tab.rgt t) (n / 2 - 1) (m / 2 - 1) x hk
        simp only [get_node]
        split_ifs at key ⊢ <;> first | exact key | rfl | omega

end C2Walk
