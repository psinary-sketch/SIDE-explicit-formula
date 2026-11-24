import SIDEExplicitFormula.Window.BandNum0
import SIDEExplicitFormula.Window.BandNum1
import SIDEExplicitFormula.Window.BandNum2
import SIDEExplicitFormula.Window.BandNum3
import SIDEExplicitFormula.Window.BandG0
import SIDEExplicitFormula.Window.BandG1
import SIDEExplicitFormula.Window.BandG2
import SIDEExplicitFormula.Window.BandG3

/-!
# L9c3: the joined lists of the band`s data and their checks at the window of `coeffPad`

Written by relay tools/b768_band_data.py from the kernel`s own files (ArchClosed.lean`s blob 3ec80af752678d30 and Coeffs.lean`s);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The joined list, 16385 places. -/
def bandNumL : List ℤ := bandNG0 ++ (bandNG1 ++ (bandNG2 ++ bandNG3))

theorem bandNumL_len : bandNumL.length = 16385 := by
  unfold bandNumL
  simp only [List.length_append, bandNG0_len, bandNG1_len, bandNG2_len, bandNG3_len] <;> norm_num

theorem bandNumL_all : winOK bandW (coeffPad.drop 0) 0 bandNumL = true := by
  unfold bandNumL
  refine winOK_chunk bandW coeffPad bandNG0 _ 0 0 4096 4096 4096 bandNG0_len (by norm_num) (by norm_num) band_ok0 ?_
  refine winOK_chunk bandW coeffPad bandNG1 _ 4096 4096 4096 8192 8192 bandNG1_len (by norm_num) (by norm_num) band_ok1 ?_
  refine winOK_chunk bandW coeffPad bandNG2 _ 8192 8192 4096 12288 12288 bandNG2_len (by norm_num) (by norm_num) band_ok2 ?_
  exact band_ok3

/-- The joined list, 16384 places. -/
def bandGL : List ℤ := bandGG0 ++ (bandGG1 ++ (bandGG2 ++ bandGG3))

theorem bandGL_len : bandGL.length = 16384 := by
  unfold bandGL
  simp only [List.length_append, bandGG0_len, bandGG1_len, bandGG2_len, bandGG3_len] <;> norm_num

theorem bandGL_all : winOK gWb (coeffPad.drop 0) 0 bandGL = true := by
  unfold bandGL
  refine winOK_chunk gWb coeffPad bandGG0 _ 0 0 4096 4096 4096 bandGG0_len (by norm_num) (by norm_num) bgam_ok0 ?_
  refine winOK_chunk gWb coeffPad bandGG1 _ 4096 4096 4096 8192 8192 bandGG1_len (by norm_num) (by norm_num) bgam_ok1 ?_
  refine winOK_chunk gWb coeffPad bandGG2 _ 8192 8192 4096 12288 12288 bandGG2_len (by norm_num) (by norm_num) bgam_ok2 ?_
  exact bgam_ok3

end Window
end SIDEExplicitFormula
