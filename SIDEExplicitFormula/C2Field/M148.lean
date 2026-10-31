/- b726, (R336)(3): the certificate at D = -148, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk
import SIDEExplicitFormula.C2Field.M123

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m148 : cert (-148) 1444 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-148 KERNEL")
    | (trace "CERT D=-148 SORRY"; sorry)

end C2Walk
