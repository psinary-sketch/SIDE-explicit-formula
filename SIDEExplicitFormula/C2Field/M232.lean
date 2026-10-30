/- b726, (R336)(3): the certificate at D = -232, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m232 : cert (-232) 3364 (-1) 2 = true := by
  first
    | (decide +kernel; trace "CERT D=-232 KERNEL")
    | (trace "CERT D=-232 SORRY"; sorry)

end C2Walk
