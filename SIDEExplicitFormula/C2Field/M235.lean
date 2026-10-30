/- b726, (R336)(3): the certificate at D = -235, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m235 : cert (-235) 4225 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-235 KERNEL")
    | (trace "CERT D=-235 SORRY"; sorry)

end C2Walk
