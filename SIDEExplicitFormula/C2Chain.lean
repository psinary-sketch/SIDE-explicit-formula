/-
b728, (R338)(4): THE CHAIN OF A CERTIFICATE SPLIT WITHIN ITS FIELD. Vanilla Lean 4, no Mathlib, no native_decide; by term and rewriting.

  * tabEq and its soundness: a table's value is checked against a literal by decide +kernel in one declaration.
  * sweepAll_add, wLoop_add: a loop of k1 + k2 steps is k1 steps then k2; sweep_chain, wLoop_chain: the same as a step of a module line.
  * rTab_of, cert_of_tabs: the literal tables conclude `cert D n0 v q = true`, C2Walk.lean's own statement, unedited.
-/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

/-- the short names of the literal tables -/
def nd : Tab → Int → Tab → Tab := Tab.node
def lf : Tab := Tab.leaf
def ip (n : Nat) : Int := Int.ofNat n
def im (n : Nat) : Int := Int.negSucc n

def tabEq : Tab → Tab → Bool
  | Tab.leaf, Tab.leaf => true
  | Tab.node l x r, Tab.node l' x' r' => decide (x = x') && (tabEq l l' && tabEq r r')
  | Tab.leaf, Tab.node _ _ _ => false
  | Tab.node _ _ _, Tab.leaf => false

theorem false_elim' {P : Prop} (h : false = true) : P := nomatch h

theorem and_left' : ∀ (a b : Bool), (a && b) = true → a = true
  | true, _, _ => rfl
  | false, _, h => false_elim' h

theorem and_right' : ∀ (a b : Bool), (a && b) = true → b = true
  | true, _, h => h
  | false, _, h => false_elim' h

theorem tabEq_sound : ∀ (s t : Tab), tabEq s t = true → s = t
  | Tab.leaf, Tab.leaf, _ => rfl
  | Tab.leaf, Tab.node _ _ _, h => false_elim' h
  | Tab.node _ _ _, Tab.leaf, h => false_elim' h
  | Tab.node l x r, Tab.node l' x' r', h => by
    have h0 : (decide (x = x') && (tabEq l l' && tabEq r r')) = true := h
    have hx : x = x' := of_decide_eq_true (and_left' _ _ h0)
    have hl : l = l' := tabEq_sound l l' (and_left' _ _ (and_right' _ _ h0))
    have hr : r = r' := tabEq_sound r r' (and_right' _ _ (and_right' _ _ h0))
    rw [hx, hl, hr]

/-- x after k rows -/
def shift : Nat → Int → Int
  | 0, x => x
  | k + 1, x => shift k (x + 1)

theorem sweepAll_succ (D : Int) (N s k : Nat) (x : Int) (t : Tab) :
    sweepAll D N s (k + 1) x t = sweepAll D N s k (x + 1) (sweepRow D N x (2 * s + 1) (-(s : Int)) t) := by
  first
    | (rw [sweepAll]; cases sweepRow D N x (2 * s + 1) (-(s : Int)) t <;> rfl)
    | (unfold sweepAll; cases sweepRow D N x (2 * s + 1) (-(s : Int)) t <;> rfl)
    | (simp only [sweepAll]; split <;> rfl)

theorem sweepAll_add (D : Int) (N s k2 : Nat) : ∀ (k1 : Nat) (x : Int) (t : Tab),
    sweepAll D N s (k1 + k2) x t = sweepAll D N s k2 (shift k1 x) (sweepAll D N s k1 x t) := by
  intro k1
  induction k1 with
  | zero =>
    intro x t
    show sweepAll D N s (0 + k2) x t = sweepAll D N s k2 x t
    rw [Nat.zero_add]
  | succ k ih =>
    intro x t
    have h : k + 1 + k2 = (k + k2) + 1 := Nat.succ_add k k2
    rw [h, sweepAll_succ, sweepAll_succ]
    exact ih (x + 1) _

theorem sweep_chain {D : Int} {N s K k K' : Nat} {x0 x : Int} {t0 t t' : Tab}
    (h0 : sweepAll D N s K x0 t0 = t) (h1 : sweepAll D N s k x t = t') (hK : K + k = K') (hx : shift K x0 = x) :
    sweepAll D N s K' x0 t0 = t' := by
  subst hK
  subst hx
  rw [sweepAll_add, h0]
  exact h1

theorem wLoop_succ (a : Nat → Int) (k n : Nat) (W : Tab) :
    wLoop a (k + 1) n W = wLoop a k (n + 1) (Tab.set 64 W n (wStep a W n)) := by
  first
    | (rw [wLoop]; cases Tab.set 64 W n (wStep a W n) <;> rfl)
    | (unfold wLoop; cases Tab.set 64 W n (wStep a W n) <;> rfl)
    | (simp only [wLoop]; split <;> rfl)

theorem wLoop_add (a : Nat → Int) (k2 : Nat) : ∀ (k1 n : Nat) (W : Tab),
    wLoop a (k1 + k2) n W = wLoop a k2 (n + k1) (wLoop a k1 n W) := by
  intro k1
  induction k1 with
  | zero =>
    intro n W
    show wLoop a (0 + k2) n W = wLoop a k2 n W
    rw [Nat.zero_add]
  | succ k ih =>
    intro n W
    have h : k + 1 + k2 = (k + k2) + 1 := Nat.succ_add k k2
    have h2 : n + 1 + k = n + (k + 1) := by
      first
        | exact Nat.add_right_comm n 1 k
        | omega
    rw [h, wLoop_succ, wLoop_succ, ← h2]
    exact ih (n + 1) _

theorem wLoop_chain {a : Nat → Int} {n0 K k K' n : Nat} {W0 W W' : Tab}
    (h0 : wLoop a K n0 W0 = W) (h1 : wLoop a k n W = W') (hK : K + k = K') (hn : n0 + K = n) :
    wLoop a K' n0 W0 = W' := by
  subst hK
  subst hn
  rw [wLoop_add, h0]
  exact h1

theorem rTab_of {D : Int} {N s : Nat} {R : Tab} (hs : side N = s)
    (hw : sweepAll D N s (2 * s + 1) (-(s : Int)) Tab.leaf = R) : rTab D N = R := by
  subst hs
  exact hw

theorem cert_of_tabs {D : Int} {n0 : Nat} {v : Int} {q : Nat} {R T : Tab}
    (hr : rTab D n0 = R) (hw : wLoop (aOf R) (n0 - 1) 2 Tab.leaf = T)
    (hf : (Tab.get T n0 % (bigOmega n0 : Int) == 0 &&
      (q : Int) * (Tab.get T n0 / (bigOmega n0 : Int)) == v * 360360 &&
      allNonneg T (n0 - 2) 2) = true) : cert D n0 v q = true := by
  subst hr
  subst hw
  exact hf

end C2Walk
