/-
SIDE-explicit-formula -- SIDEExplicitFormula/ControlFailureStatement.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(7); W-ORD-LI-ARITH, W-ORD-STATEMENT-PIN) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CONTROL'S FAILURE FROM ITS COEFFICIENTS, STATED BEFORE ITS PROOF. The control is the Epstein zeta function of the form
x^2 + xy + 6y^2, discriminant -23. Two forms of the statement, each a definition of a Prop with no proof in this file; a proof, where
one is built, is a theorem stated as the Prop in a file of its own.

FORM B, THE WINDOW (`ControlFailureB`): at the named test function `witnessK`, in classK and vanishing outside
[-`witnessWidth`, `witnessWidth`], the arithmetic side of the control's explicit formula -- the pole term less the prime-power side with
the control's coefficients `cQ` plus the archimedean term `archTermQ` -- has negative real part. `witnessK` is the autocorrelation of
`witnessH`, the window of the family relay data/b709_grid.txt :46 names (relay tools/b694_witness_terms.py, the window of kind N):
`witnessH = (g^2 + D^2)[cos(g u) phi(u)]`, with `phi` the cardinal B-spline of order 6 carried onto [-log 32, log 32]
(`witnessPhi`, from `bsplineSix`) and `g` the family's frequency as that line prints it (`witnessFreq`); so `witnessK` vanishes outside
[-log 1024, log 1024]. The window is chosen with b709's family in view; the statement holds no zero of the function.

FORM A, THE COEFFICIENT (`ControlFailureA n`): the Li coefficient of the control's configuration at n is negative. The statement takes
n as its parameter: no bank names n, and none is computed here; a proof names it.

No premise is bound; nothing here is proved.
-/
import SIDEExplicitFormula.H2Sign
import SIDEExplicitFormula.Schema.EpsteinZQ
import SIDEExplicitFormula.Schema.ZQ.Zeros
import SIDEExplicitFormula.Schema.Wide.Converse

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The named window of FORM B -/

/-- The cardinal B-spline of order 6, supported on `[0, 6]`: `(1/120) Σ_{j ≤ 6} (-1)^j C(6, j) (x - j)_+^5`. -/
def bsplineSix (x : ℝ) : ℝ :=
  (1 / 120) * ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ j * (Nat.choose 6 j : ℝ) * (max (x - j) 0) ^ 5

/-- The step of the window: a third of `log 32`. -/
def witnessStep : ℝ := Real.log 32 / 3

/-- The B-spline carried onto `[-log 32, log 32]`, of integral 1. -/
def witnessPhi (u : ℝ) : ℝ := bsplineSix ((u + Real.log 32) / witnessStep) / witnessStep

/-- The family's frequency, as relay data/b709_grid.txt :46 prints it. -/
def witnessFreq : ℝ := 16290215720390390792963 / 10 ^ 21

/-- The centred window `cos(g u) phi(u)`. -/
def witnessCos (u : ℝ) : ℝ := Real.cos (witnessFreq * u) * witnessPhi u

/-- The window of kind N: `(g^2 + D^2)[cos(g u) phi(u)]`. -/
def witnessH (u : ℝ) : ℝ := witnessFreq ^ 2 * witnessCos u + deriv (deriv witnessCos) u

/-- **The named test function of FORM B:** the autocorrelation of `witnessH`. -/
def witnessK : ℝ → ℂ := Zeta23.EF.weilTest (fun u => (witnessH u : ℂ)) (fun u => (witnessH u : ℂ))

/-- **The named width of FORM B:** `log 1024`, twice the window's `log 32`. -/
def witnessWidth : ℝ := Real.log 1024

/-! ### The two forms, stated -/

/-- **FORM B, stated:** `witnessK` is in classK, vanishes outside `[-witnessWidth, witnessWidth]`, and the control's arithmetic side
at it, the pole term less the prime-power side with `cQ` plus `archTermQ`, has negative real part. -/
def ControlFailureB : Prop :=
  classK witnessK ∧ (∀ u : ℝ, witnessWidth < |u| → witnessK u = 0) ∧
    (poleTerm witnessK - Schema.primeTermQ Schema.ZQ.cQ witnessK + Schema.archTermQ witnessK).re < 0

/-- **FORM A, stated:** the Li coefficient of the control's configuration at `n` is negative. -/
def ControlFailureA (n : ℕ) : Prop :=
  Schema.Wide.liCoeff Schema.ZQ.zqZeroConfig n < 0

end B321
end SIDEExplicitFormula
