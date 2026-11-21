/-
b765 under (R375)(5)(b): GAUSS'S INTEGRAL FOR THE CONTROL'S ARCHIMEDEAN TERM, STATED APART FROM ITS PROOF.

For every `k` in classK, the archimedean term of Z_Q's explicit formula, `archTermQ k = (1/2π) ∫ k̂(r) bracketQ(r) dr`
(Schema/EpsteinZQ.lean, `bracketQ r = 2 Re ψ(1/2 + i r) − 2 log(2π/√23)`), is written by Gauss's integral for the digamma
function as `2 k(0) (log(√23/(2π)) − γ) + 2 ∫_{t>0} (e^{−t} k(0) − e^{−t/2} k(t)) / (1 − e^{−t}) dt`.

THE GATE BEFORE IT, a control and no registration: at the kernel's window at the widths of relay data/b709_grid.txt :426 and
:439, the form computed with this right side in place of the kernel's integral equals the banked S_NN to 6 digits (relay
data/b765_gauss_gate.txt, tools/b765_gauss_gate.py). This file holds the statement alone, a definition of a Prop; its proof in
steps stands in `GaussArchQSteps`, as far as it goes. NOTHING HERE IS PROVED.
-/
import SIDEExplicitFormula.H2Sign
import SIDEExplicitFormula.Schema.EpsteinZQ
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **Gauss's integral for the control's archimedean term, stated:** for every `k` in classK,
`archTermQ k = 2 k(0) (log(√23/(2π)) − γ) + 2 ∫_{t>0} (e^{−t} k(0) − e^{−t/2} k(t)) / (1 − e^{−t}) dt`. A statement, not a
result. -/
def GaussArchQ : Prop :=
  ∀ k : ℝ → ℂ, classK k →
    Schema.archTermQ k =
      2 * k 0 * ((Real.log (Real.sqrt 23 / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) +
        2 * ∫ t in Set.Ioi (0 : ℝ),
          ((Real.exp (-t) : ℂ) * k 0 - (Real.exp (-t / 2) : ℂ) * k t) / (1 - (Real.exp (-t) : ℂ))

end B321
end SIDEExplicitFormula
