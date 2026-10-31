/-
b729, (R339)(3): THE ORDERED FACTORIZATIONS WITH BOTH COFACTORS AT LEAST d.
-/
import SIDEExplicitFormula.C2Walk
import Mathlib

namespace C2Walk

/-- the ordered factorizations n = x y with x, y ≥ d -/
def Spair (n d : Nat) : Finset (Nat × Nat) :=
  (Nat.divisorsAntidiagonal n).filter (fun p => d ≤ p.1 ∧ d ≤ p.2)

theorem mem_Spair {n d : Nat} {p : Nat × Nat} :
    p ∈ Spair n d ↔ (p.1 * p.2 = n ∧ n ≠ 0) ∧ d ≤ p.1 ∧ d ≤ p.2 := by
  simp only [Spair, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]

end C2Walk
