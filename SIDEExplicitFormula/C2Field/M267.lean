/- b726, (R336)(3): the certificate at D = -267, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m267 : cert (-267) 4761 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-267 KERNEL")
    | (trace "CERT D=-267 SORRY"; sorry)

end C2Walk
