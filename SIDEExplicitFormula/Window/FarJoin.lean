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
  simp only [List.length_append, farNG0_len, farNG1_len, farNG2_len, farNG3_len] <;> norm_num

theorem farNumL_all : winOK farW (autoD.drop 16360) 0 farNumL = true := by
  unfold farNumL
  refine winOK_chunk farW autoD farNG0 _ 16360 0 4096 20456 4096 farNG0_len (by norm_num) (by norm_num) far_ok0 ?_
  refine winOK_chunk farW autoD farNG1 _ 20456 4096 4096 24552 8192 farNG1_len (by norm_num) (by norm_num) far_ok1 ?_
  refine winOK_chunk farW autoD farNG2 _ 24552 8192 4096 28648 12288 farNG2_len (by norm_num) (by norm_num) far_ok2 ?_
  exact far_ok3

/-- The joined list, 16369 places. -/
def farGL : List ℤ := farGG0 ++ (farGG1 ++ (farGG2 ++ farGG3))

theorem farGL_len : farGL.length = 16369 := by
  unfold farGL
  simp only [List.length_append, farGG0_len, farGG1_len, farGG2_len, farGG3_len] <;> norm_num

theorem farGL_all : winOK gW (autoD.drop 16360) 0 farGL = true := by
  unfold farGL
  refine winOK_chunk gW autoD farGG0 _ 16360 0 4096 20456 4096 farGG0_len (by norm_num) (by norm_num) gam_ok0 ?_
  refine winOK_chunk gW autoD farGG1 _ 20456 4096 4096 24552 8192 farGG1_len (by norm_num) (by norm_num) gam_ok1 ?_
  refine winOK_chunk gW autoD farGG2 _ 24552 8192 4096 28648 12288 farGG2_len (by norm_num) (by norm_num) gam_ok2 ?_
  exact gam_ok3

end Window
end SIDEExplicitFormula
