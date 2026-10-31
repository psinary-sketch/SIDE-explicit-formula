/- b728, (R338)(4): the certificate at D = -427, split within the field, 19 sweep blocks and 30 step blocks, one module each. -/
import SIDEExplicitFormula.C2Field.P427.W030

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m427 : cert (-427) 14161 (-2) 1 = true := by
  (exact cert_of_tabs (rTab_of (s := 169) (by decide +kernel) F427.reachS19) F427.reachW30 (by decide +kernel); trace "CERT D=-427 KERNEL")

end C2Walk
