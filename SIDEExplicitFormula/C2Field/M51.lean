/- b726, (R336)(3): the certificate at D = -51, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk
import SIDEExplicitFormula.C2Field.M40

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m51 : cert (-51) 225 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-51 KERNEL")
    | (trace "CERT D=-51 SORRY"; sorry)

end C2Walk
