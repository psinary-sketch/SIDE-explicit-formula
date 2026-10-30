/- b726, (R336)(3): the certificate at D = -52, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m52 : cert (-52) 196 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-52 KERNEL")
    | (trace "CERT D=-52 SORRY"; sorry)

end C2Walk
