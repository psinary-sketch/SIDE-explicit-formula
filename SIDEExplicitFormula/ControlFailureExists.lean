/-
THE CONTROL'S FAILURE, STATED WITH NO NUMBER OF A ZERO IN IT (b765, (R375)(5)(a), W-ORD-LI-ARITH).

`ControlFailureExists`: there is a test function `k` in classK, vanishing outside [-log 1024, log 1024], at which the arithmetic side
of the control's explicit formula -- the pole term less the prime-power side with the control's coefficients `cQ` plus the archimedean
term `archTermQ` -- has negative real part. The statement names no test function, no frequency and no zero; its imports are H2Sign
(classK, and poleTerm through B321Identity), Schema.EpsteinZQ (primeTermQ, archTermQ) and Schema.ZQ.LogDeriv (cQ).

A definition of a Prop, entered as a definition and not as a result: its position is DEFINITION, the proof carried. The statement of
b763 (ControlFailureStatement, FORM B at a named window) stays on its own branch. No premise is bound; nothing here is proved.
-/
import SIDEExplicitFormula.H2Sign
import SIDEExplicitFormula.Schema.EpsteinZQ
import SIDEExplicitFormula.Schema.ZQ.LogDeriv

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **The control's failure, stated:** some `k` in classK, vanishing outside `[-log 1024, log 1024]`, at which the control's
arithmetic side, the pole term less the prime-power side with `cQ` plus `archTermQ`, has negative real part. -/
def ControlFailureExists : Prop :=
  ∃ k : ℝ → ℂ, classK k ∧ (∀ u : ℝ, Real.log 1024 < |u| → k u = 0) ∧
    (poleTerm k - Schema.primeTermQ Schema.ZQ.cQ k + Schema.archTermQ k).re < 0

end B321
end SIDEExplicitFormula
