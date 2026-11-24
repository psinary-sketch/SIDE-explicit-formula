import SIDEExplicitFormula.Window.ArithJoin
import SIDEExplicitFormula.ControlFailureExists

/-!
# L11d and L12: the arithmetic side at the window below `0`, and `ControlFailureExists`

`window_arith_neg` (L11d): by `arith_eq_comb` (L11c) the real part of the arithmetic side at the window is the combination; its
constants are at most `arithE` (`arithK_le`), its `m` side at most `arithA` (`arithM_le`), its prime-power side at least `arithB`
(`arithP_le`, the checks of ArithJoin.lean given), and `arithE + arithA - arithB < 0` (`arith_num`). Each constant is taken at the
end of its interval of L10 that its coefficient's sign gives.

`controlFailureExists` (L12): the window's autocorrelation is in `classK`, `0` where `|u| > log 1024`, and its arithmetic side has
negative real part.
-/

namespace SIDEExplicitFormula
namespace Window

/-- **L11d: the arithmetic side's real part at the window is below `0`**, each constant taken at the end of its interval of L10
that its coefficient's sign gives. -/
theorem window_arith_neg :
    (B321.poleTerm windowK - Schema.primeTermQ Schema.ZQ.cQ windowK + Schema.archTermQ windowK).re < 0 := by
  rw [arith_eq_comb]
  have hK := arithK_le
  have hM := arithM_le
  have hP := arithP_le ar_cov_all ar_tq_all ar_p_find
  have hN := arith_num
  linarith

/-- **L12: `ControlFailureExists`**, at the window's autocorrelation. -/
theorem controlFailureExists : B321.ControlFailureExists :=
  ⟨windowK, windowK_classK, fun u hu => windowK_eq_zero u hu, window_arith_neg⟩

end Window
end SIDEExplicitFormula
