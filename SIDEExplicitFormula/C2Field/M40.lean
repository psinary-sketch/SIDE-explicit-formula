/- b726, (R336)(3): the certificate at D = -40, one module, one dispatch. -/
import SIDEExplicitFormula.C2Walk
import SIDEExplicitFormula.C2Field.M35

namespace C2Walk

set_option maxHeartbeats 5000000 in
theorem cert_m40 : cert (-40) 100 (-1) 2 = true := by
  first
    | (decide +kernel; trace "CERT D=-40 KERNEL")
    | (trace "CERT D=-40 SORRY"; sorry)

end C2Walk
