/-!
# The integral of the window`s spline, as data

`intHNum` is the sum of the integer numerators `coeffInt j`, `j` from 16 to 16380, of the window banked at relay
data/b765_window.json, so that the integral of its spline over `y > 1` is `intHNum / (16 * 10 ^ coeffScale)`, the
certificate`s intH (relay data/b766_certificate.json). Written by relay tools/b766_poledata.py under (R376)(4)(d); edited by no
hand.

The bank`s sha256, less its final line end: 4cbe7be1203883a6d2688b32ed3e1994760530a7acc8942560169267a37048f0
The bank`s sha256, the file whole: bd228144d213356c5c010ca969cfbbf0d88ab1438d7e25937b99bf6b2f645dea
The coefficients` sha256, as the bank`s own field coef_sha: 4702881bfa6f928f
-/

namespace SIDEExplicitFormula
namespace Window

/-- The sum of the integer numerators of the window`s coefficients, `j` from 16 to 16380. -/
def intHNum : ℤ := 1614754101931707

end Window
end SIDEExplicitFormula
