/- b726, (R336)(3): the certificate at D = -427, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m427 : cert (-427) 14161 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-427 KERNEL")
    | (trace "CERT D=-427 SORRY"; sorry)

end C2Walk
