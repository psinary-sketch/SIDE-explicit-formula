/- b729, dispatch one's probe, removed at the next commit: the interface the join reads, so that the join reads even where a proof beneath it does not. -/
import SIDEExplicitFormula.C2Chain
import SIDEExplicitFormula.C2Spair
import Mathlib

namespace C2Walk

theorem get_set : ∀ (k : Nat) (t : Tab) (n m : Nat) (x : Int), n + 1 < 2 ^ k →
    Tab.get (Tab.set k t n x) m = if m = n then x else Tab.get t m := by
  sorry

theorem bigOmega_eq (n : Nat) (hn : 1 ≤ n) : bigOmega n = ArithmeticFunction.cardFactors n := by
  sorry

theorem cardFactors_pos (m : Nat) (hm : 2 ≤ m) : 0 < ArithmeticFunction.cardFactors m := by
  sorry

theorem divSum_full (a : Nat → Int) (W : Tab) (n : Nat) (hn : n ≠ 0) :
    divSum a W n n 2 0 = ∑ p ∈ Spair n 2, Tab.get W p.1 * a p.2 := by
  sorry

def Fa (a : Nat → Int) : Nat → Nat → Int
  | 0, n => if n = 1 then 1 else 0
  | k + 1, n => ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).foldl (fun s d => s + a d * Fa a k (n / d)) 0

def bLa (a : Nat → Int) (n : Nat) : Int :=
  360360 * Fa a 1 n - 180180 * Fa a 2 n + 120120 * Fa a 3 n - 90090 * Fa a 4 n + 72072 * Fa a 5 n - 60060 * Fa a 6 n + 51480 * Fa a 7 n
    - 45045 * Fa a 8 n + 40040 * Fa a 9 n - 36036 * Fa a 10 n + 32760 * Fa a 11 n - 30030 * Fa a 12 n + 27720 * Fa a 13 n - 25740 * Fa a 14 n
    + 24024 * Fa a 15 n

theorem bL_eq (D : Int) (n : Nat) : bL D n = bLa (aQ D) n := by
  sorry

def wf (a : Nat → Int) (n : Nat) : Int := (ArithmeticFunction.cardFactors n : ℤ) * bLa a n

theorem wf_rec (a : Nat → Int) (n : Nat) (h2 : 2 ≤ n) (hn : n < 65536) :
    wf a n = (ArithmeticFunction.cardFactors n : ℤ) * 360360 * a n - ∑ p ∈ Spair n 2, wf a p.1 * a p.2 := by
  sorry

theorem bLa_congr (a b : Nat → Int) (N n : Nat) (h : ∀ m, m ≤ N → a m = b m) (hn : n ≤ N) : bLa a n = bLa b n := by
  sorry

theorem bLa_low (a : Nat → Int) (n : Nat) (hn : n < 2) : bLa a n = 0 := by
  sorry

theorem get_rTab_eq (D : Int) (N n : Nat) (hD : D ≤ -15) (hn : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    Tab.get (rTab D N) n = (rQ D n : Int) := by
  sorry

end C2Walk
