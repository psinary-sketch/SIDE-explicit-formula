import SIDEExplicitFormula.Window.FarNum0
import SIDEExplicitFormula.Window.FarNum1
import SIDEExplicitFormula.Window.FarNum2
import SIDEExplicitFormula.Window.FarNum3
import SIDEExplicitFormula.Window.FarG0
import SIDEExplicitFormula.Window.FarG1
import SIDEExplicitFormula.Window.FarG2
import SIDEExplicitFormula.Window.FarG3

/-!
# L9c2: the joined lists of the far sum`s data and their checks at the window of `autoD`

Written by relay tools/b768_far_data.py from the kernel`s own files (ArchLam.lean`s blob b4f3cbd71bde5a08 and Coeffs.lean`s);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The joined list, 16370 places. -/
def farNumL : List ℤ := farNG0 ++ (farNG1 ++ (farNG2 ++ farNG3))

theorem farNumL_len : farNumL.length = 16370 := by
  unfold farNumL
  simp only [List.length_append, farNG0_len, farNG1_len, farNG2_len, farNG3_len]

theorem farNumL_all : winOK farW (autoD.drop 16360) 0 farNumL = true := by
  unfold farNumL
  rw [winOK_append, winOK_append, winOK_append, farNG0_len, farNG1_len, farNG2_len, far_ok0, far_ok1, far_ok2, far_ok3]
  all_goals rfl

/-- The joined list, 16369 places. -/
def farGL : List ℤ := farGG0 ++ (farGG1 ++ (farGG2 ++ farGG3))

theorem farGL_len : farGL.length = 16369 := by
  unfold farGL
  simp only [List.length_append, farGG0_len, farGG1_len, farGG2_len, farGG3_len]

theorem farGL_all : winOK gW (autoD.drop 16360) 0 farGL = true := by
  unfold farGL
  rw [winOK_append, winOK_append, winOK_append, farGG0_len, farGG1_len, farGG2_len, gam_ok0, gam_ok1, gam_ok2, gam_ok3]
  all_goals rfl

end Window
end SIDEExplicitFormula
