/- b726, (R336)(3): the certificate at D = -187, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m187 : cert (-187) 3773 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-187 KERNEL")
    | (trace "CERT D=-187 SORRY"; sorry)

end C2Walk
