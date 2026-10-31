/- b728, (R338)(4): the certificate at D = -403, split within the field, 25 sweep blocks and 40 step blocks, one module each. -/
import SIDEExplicitFormula.C2Field.P403.W040

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m403 : cert (-403) 17303 (-2) 1 = true := by
  (exact cert_of_tabs (rTab_of (s := 187) (by decide +kernel) F403.reachS25) F403.reachW40 (by decide +kernel); trace "CERT D=-403 KERNEL")

end C2Walk
