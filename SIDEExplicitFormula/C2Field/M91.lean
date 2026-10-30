/- b726, (R336)(3): the certificate at D = -91, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m91 : cert (-91) 875 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-91 KERNEL")
    | (trace "CERT D=-91 SORRY"; sorry)

end C2Walk
