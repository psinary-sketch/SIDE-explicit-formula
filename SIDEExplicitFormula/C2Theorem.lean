/-
b729, (R339)(3): THE C2 THEOREM. The eighteen certificates of C2Field/ joined to (L1), (L2) and `law_of_cert` of C2Law.lean.

SCOPE: the list `walk` is the eighteen imaginary quadratic fields of class number 2; that the list is complete is Baker 1971 and Stark 1975, cited
and not compiled. Neither enters a binder of a theorem here: every statement below is about the rows of `walk` and only those.
-/
import SIDEExplicitFormula.C2Law
import SIDEExplicitFormula.C2Field.M15
import SIDEExplicitFormula.C2Field.M20
import SIDEExplicitFormula.C2Field.M24
import SIDEExplicitFormula.C2Field.M35
import SIDEExplicitFormula.C2Field.M40
import SIDEExplicitFormula.C2Field.M51
import SIDEExplicitFormula.C2Field.M52
import SIDEExplicitFormula.C2Field.M88
import SIDEExplicitFormula.C2Field.M91
import SIDEExplicitFormula.C2Field.M115
import SIDEExplicitFormula.C2Field.M123
import SIDEExplicitFormula.C2Field.M148
import SIDEExplicitFormula.C2Field.M187
import SIDEExplicitFormula.C2Field.M232
import SIDEExplicitFormula.C2Field.M235
import SIDEExplicitFormula.C2Field.M267
import SIDEExplicitFormula.C2Field.M403
import SIDEExplicitFormula.C2Field.M427

namespace C2Walk

/-- every row of the walk carries its certificate -/
theorem all_certs : ∀ p ∈ walk, cert p.1 p.2.1 p.2.2.1 p.2.2.2 = true := by
  intro p h
  unfold walk at h
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m15
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m20
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m24
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m35
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m40
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m51
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m52
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m88
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m91
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m115
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m123
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m148
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m187
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m232
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m235
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m267
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m403
  rcases List.mem_cons.mp h with rfl | h
  · exact cert_m427
  cases h

/-- THE C2 VALUE LAW, at the eighteen rows of the walk -/
theorem c2_value_law : C2ValueLaw :=
  value_law_of_certs (fun D n0 v q hw => all_certs (D, n0, v, q) hw)

/-- for each row (D, n0, v, q): n0 is the least n with b(n) < 0, and b(n0) = v / q is the walk's value -/
theorem c2_least_negative (D : Int) (n0 : Nat) (v : Int) (q : Nat) (hw : (D, n0, v, q) ∈ walk) :
    ((q : Int) * bL D n0 = v * 360360) ∧ bL D n0 < 0 ∧ ∀ n, n < n0 → 0 ≤ bL D n :=
  least_negative_of_law c2_value_law D n0 v q hw

end C2Walk
