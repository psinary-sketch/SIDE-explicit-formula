/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/SupportDetection.lean
THIS PROGRAMME'S WORK (act b729, ruling (R339)(5); branch detect-b729, no main, no tag) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SUPPORT-FACE DETECTION THEOREM, THE STATEMENT ALONE. Stated, not proved; open. Nothing in this file is a theorem: the two `Prop`s below are the
statement and its contrapositive, neither is asserted, and no module imports this one.

`detector` (Detector.lean :99) gives, at a point off the line, a window in classK of negative zero side, its list `a` and power `j` existential: `j`
comes from `Metric.tendsto_atTop` over a limit with no rate (Converse.lean :171), and the list from an interpolant over the tie and kill sets, so its
size follows the score gap and the separation of those nodes. Neither is bounded by the count, the height and the distance from the line. The statement
below is therefore not `detector` with a rate read off; its proof, as priced in relay data/b729_detection.txt, is a different route.

`supportK c A₀ γ δ` is explicit in A₀ (the local-count constant, `countConst`) and `b1Const` (B1's constant at half-width 1,
`offScore_plateau_first_order`, FirstOrderBound.lean :149, read as `2 * exp (1 / 2)`); `c` is one absolute constant, which a proof must exhibit.

Nothing here proves RH or GRH or locates any zero; every statement is over an arbitrary configuration with an off-line point as a hypothesis.
-/
import SIDEExplicitFormula.Schema.Detector
import SIDEExplicitFormula.FirstOrderBound

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

/-- The configuration's local-count constant: the `A₀` its `count` field carries (`HCount`, RestBound.lean :44). -/
def countConst (C : WeilConfig) : ℝ := C.count.choose

/-- B1's constant at half-width 1: `offScore (plateau F 1) ρ * |Im ρ| ≤ 2 * exp (1 / 2)` in the strip. -/
def b1Const : ℝ := 2 * Real.exp (1 / 2)

/-- **The support bound**: at height `γ` and distance `δ` from the line, `c A₀ log (B1 (|γ| + A₀ / |δ| + 3)) / |δ|`. -/
def supportK (c A₀ γ δ : ℝ) : ℝ := c * A₀ * Real.log (b1Const * (|γ| + A₀ / |δ| + 3)) / |δ|

/-- **THE SUPPORT-FACE DETECTION STATEMENT, at the absolute constant `c`.** Stated, not proved; open. For a configuration of the schema and a point
`ρ₀` off the line, some `k` in classK of support within `supportK c A₀ (Im ρ₀) (Re ρ₀ - 1/2)` has a zero side of negative real part. -/
def SupportDetection (c : ℝ) : Prop :=
  ∀ (C : WeilConfig) (ρ₀ : ℂ), ρ₀ ∈ C.carrier → ρ₀.re ≠ 1 / 2 →
    ∃ k : ℝ → ℂ, classK k ∧
      Function.support k ⊆
        Set.Icc (-supportK c (countConst C) ρ₀.im (ρ₀.re - 1 / 2)) (supportK c (countConst C) ρ₀.im (ρ₀.re - 1 / 2)) ∧
      (zeroSide_cfg C k).re < 0

/-- **A finite positivity certificate at support `L`**: every `k` in classK of support within `[-L, L]` has a zero side of nonnegative real part. -/
def CertificateAt (C : WeilConfig) (L : ℝ) : Prop :=
  ∀ k : ℝ → ℂ, classK k → Function.support k ⊆ Set.Icc (-L) L → 0 ≤ (zeroSide_cfg C k).re

/-- **THE CONTRAPOSITIVE, at the absolute constant `c`.** Stated, not proved; open. A certificate at support `L` leaves, at each height, no point of
the configuration off the line with `supportK` at most `L`: the strip free of points farther than `K⁻¹` from the line. -/
def StripCertificate (c : ℝ) : Prop :=
  ∀ (C : WeilConfig) (L : ℝ), CertificateAt C L → ∀ ρ ∈ C.carrier,
    ρ.re = 1 / 2 ∨ L < supportK c (countConst C) ρ.im (ρ.re - 1 / 2)

end Schema
end SIDEExplicitFormula
