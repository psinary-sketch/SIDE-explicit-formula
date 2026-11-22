import Mathlib.Data.Real.Basic

/-!
# The window`s autocorrelation at 0, as data

`k0Num` is the strided sum `Kt 1` of KFast.lean for the window banked at relay data/b765_window.json, so that the
autocorrelation at 0 is `k0Num / (80640 * 10 ^ 34)`, the certificate`s k0 (relay data/b766_certificate.json). Written by relay
tools/b766_k0data.py under (R376)(4)(d); edited by no hand.

The bank`s sha256, less its final line end: 4cbe7be1203883a6d2688b32ed3e1994760530a7acc8942560169267a37048f0
The bank`s sha256, the file whole: bd228144d213356c5c010ca969cfbbf0d88ab1438d7e25937b99bf6b2f645dea
The coefficients` sha256, as the bank`s own field coef_sha: 4702881bfa6f928f
-/

namespace SIDEExplicitFormula
namespace Window

/-- The strided sum of the window`s autocorrelation at `n = 1`. -/
def k0Num : ℤ := 103990834874197250192577655474414942335704

end Window
end SIDEExplicitFormula
