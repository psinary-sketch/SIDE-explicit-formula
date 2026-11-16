/- b728, (R338)(4): the certificate at D = -267, split within the field, 7 sweep blocks and 8 step blocks, one module each. -/
import SIDEExplicitFormula.C2Field.P267.W008

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m267 : cert (-267) 4761 (-2) 1 = true := by
  (exact cert_of_tabs (rTab_of (s := 98) (by decide +kernel) F267.reachS7) F267.reachW8 (by decide +kernel); trace "CERT D=-267 KERNEL")

end C2Walk
