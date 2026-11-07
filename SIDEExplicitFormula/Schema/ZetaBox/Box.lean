/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZetaBox/Box.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(b), W-ORD-ZETA-BOX Z5 and SPZ3; the plan relay data/b744_zetabox_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z5, THE ZERO. The conditional theorem of SPZ1 (Line.lean `zeta_box_of_signs`) at the two signs of Z4 (Signs.lean `zeta_sign_12`,
`zeta_sign_16`).

A zero of ζ with real part 1/2 and imaginary part between 12 and 16, located in Lean with the standard three; an instrument control on a known
case; nothing new of ζ, nothing of RH.
-/
import SIDEExplicitFormula.Schema.ZetaBox.Signs

namespace SIDEExplicitFormula
namespace Schema
namespace ZetaBox

/-! ## Z5 -- the zero -/

/-- **zeta_box**: a zero of `riemannZeta` on the critical line with ordinate in `(12, 16)`. -/
theorem zeta_box : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ (12 : ℝ) < ρ.im ∧ ρ.im < 16 :=
  zeta_box_of_signs zeta_sign_12 zeta_sign_16

end ZetaBox
end Schema
end SIDEExplicitFormula
