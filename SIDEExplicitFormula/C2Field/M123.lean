/- b726, (R336)(3): the certificate at D = -123, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m123 : cert (-123) 1089 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-123 KERNEL")
    | (trace "CERT D=-123 SORRY"; sorry)

end C2Walk
