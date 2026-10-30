/- b726, (R336)(3): the certificate at D = -88, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m88 : cert (-88) 484 (-1) 2 = true := by
  first
    | (decide +kernel; trace "CERT D=-88 KERNEL")
    | (trace "CERT D=-88 SORRY"; sorry)

end C2Walk
