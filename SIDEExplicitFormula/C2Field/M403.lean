/- b726, (R336)(3): the certificate at D = -403, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m403 : cert (-403) 17303 (-2) 1 = true := by
  first
    | (decide +kernel; trace "CERT D=-403 KERNEL")
    | (trace "CERT D=-403 SORRY"; sorry)

end C2Walk
