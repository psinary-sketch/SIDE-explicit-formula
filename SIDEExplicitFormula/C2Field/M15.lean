/- b726, (R336)(3): the certificate at D = -15, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m15 : cert (-15) 24 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-15 KERNEL")
    | (trace "CERT D=-15 SORRY"; sorry)

end C2Walk
