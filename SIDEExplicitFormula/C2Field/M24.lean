/- b726, (R336)(3): the certificate at D = -24, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m24 : cert (-24) 36 (-1) 2 = true := by
  first
    | (decide +kernel; trace "CERT D=-24 KERNEL")
    | (trace "CERT D=-24 SORRY"; sorry)

end C2Walk
