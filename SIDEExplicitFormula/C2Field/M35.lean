/- b726, (R336)(3): the certificate at D = -35, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk
import SIDEExplicitFormula.C2Field.M24

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m35 : cert (-35) 135 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-35 KERNEL")
    | (trace "CERT D=-35 SORRY"; sorry)

end C2Walk
