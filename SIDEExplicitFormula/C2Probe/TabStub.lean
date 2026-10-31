/- b729, dispatch one's probe, removed at the next commit: the table's statement, so that the sweep reads even where the table's proof does not. -/
import SIDEExplicitFormula.C2Chain
import Mathlib

namespace C2Walk

theorem get_set : ∀ (k : Nat) (t : Tab) (n m : Nat) (x : Int), n + 1 < 2 ^ k →
    Tab.get (Tab.set k t n x) m = if m = n then x else Tab.get t m := by
  sorry

end C2Walk
