/- b726, (R336)(3): the certificate at D = -115, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk
import SIDEExplicitFormula.C2Field.M91

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m115 : cert (-115) 1225 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-115 KERNEL")
    | (trace "CERT D=-115 SORRY"; sorry)

end C2Walk
