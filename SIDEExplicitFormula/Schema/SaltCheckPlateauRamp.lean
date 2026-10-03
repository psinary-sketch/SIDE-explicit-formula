/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/SaltCheckPlateauRamp.lean
THIS PROGRAMME'S WORK (act b602, ruling (R212)(4), H36c) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF (E3)'S WINDOW, COMPILED. A closed form that any value satisfied, or a window property that held for any
function, would say nothing beyond its shape.

* **`box_transform_zero_at_pi`** -- the closed form at `p = 0` vanishes at `z = π` for the unit box (the zero factor the
  bench's window carries at `π / W`);
* **`box_transform_ne_zero_at_half_pi`** -- and does not vanish at `z = π/2`: the closed form decides values, it is not a
  shape any transform would meet;
* **`window_even_compact_at_seven`** -- the window at the bench's order `p = 7` (b522) is even and compactly supported,
  proved with no obligation.

These are statements about test functions; nothing here is a statement about any zero. 0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.Schema.PlateauRamp

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace PlateauRamp
namespace SaltCheck

open B321

/-- **H36c, THE CLOSED FORM VANISHES AT π** for the unit box. -/
theorem box_transform_zero_at_pi : Zeta23.paperFT (phiC (box 1)) (Real.pi : ℂ) = 0 := by
  have hz : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [box_paperFT zero_le_one hz]
  simp [Complex.sin_pi]

/-- **H36c, AND NOT AT π/2**: `2 sin(π/2)/(π/2) = 4/π ≠ 0`. -/
theorem box_transform_ne_zero_at_half_pi : Zeta23.paperFT (phiC (box 1)) ((Real.pi : ℂ) / 2) ≠ 0 := by
  have hz : (Real.pi : ℂ) / 2 ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    exact div_ne_zero this two_ne_zero
  rw [box_paperFT zero_le_one hz]
  simp only [Complex.ofReal_one, mul_one, Complex.sin_pi_div_two]
  exact div_ne_zero (by norm_num) hz

/-- **H36c, THE WINDOW AT THE BENCH'S ORDER**: at `p = 7` the window is even and compactly supported, with no obligation. -/
theorem window_even_compact_at_seven (W h : ℝ) :
    (∀ x, window W h 7 (-x) = window W h 7 x) ∧ HasCompactSupport (window W h 7) :=
  ⟨window_even W h 7, window_hasCompactSupport W h 7⟩

end SaltCheck
end PlateauRamp
end Schema
end SIDEExplicitFormula
