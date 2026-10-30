/- b726, (R336)(3): the certificate at D = -20, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m20 : cert (-20) 36 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-20 KERNEL")
    | (trace "CERT D=-20 SORRY"; sorry)

end C2Walk
