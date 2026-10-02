/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Epstein.lean
THIS PROGRAMME'S WORK (act b590, ruling (R200)(4)(b); the Epstein negative control, its instance) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE EPSTEIN CONFIGURATION AT INTERFACES. `Z_Q` is the Epstein zeta function of the principal form `x² + xy + 6y²` of
discriminant `−23` (class number 3). Mathlib at de5ce8a9 holds no Epstein zeta function and no Hecke L-function of a
class-group character, and `Z_Q` is a combination of those, not a product, so its zero configuration cannot be built here
as an instance of the schema. What is stated: the schema's fields for `Z_Q` as NAMED PREMISES over an abstract zero
configuration `Z` and arithmetic side `rhs` -- the explicit formula (T1-lit: the Guinand-Weil explicit formula, Weil 1952
"Sur les 'formules explicites'", cited at PLACE-papers BALANCE_AND_POSITIVITY.md :542, and Bombieri-Lagarias 1999, not
specific to zeta, :422) and the local count (T3: read off the bench's zero list, relay data/b326_epstein_zeros.json and
data/b506_c2_results.json) -- with the target taken as the strip form itself; the bench's off-line zero `rhoE` (b506's
`0.7979971571786801 + 29.551761098629115 i`) as a hypothesis of membership; and the conclusion that the configuration so
premised is not Weil-positive on classK. THE PREMISE BUNDLE'S CONSISTENCY WITH THE ACTUAL `Z_Q` IS NOT PROVED IN THE
KERNEL: the premises are named, not discharged. Nothing here is a statement about the zeros of any Epstein zeta function
beyond the compiled statements' own words.
-/
import SIDEExplicitFormula.Schema.Detector

open Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

/-- **The bench's off-line zero of `Z_Q`** (relay data/b506_c2_results.json, column R): `0.7979971571786801 + 29.551761098629115 i`. -/
def rhoE : ℂ := ⟨0.7979971571786801, 29.551761098629115⟩

theorem rhoE_re_ne_half : rhoE.re ≠ 1 / 2 := by
  show (0.7979971571786801 : ℝ) ≠ 1 / 2
  norm_num

/-- **THE EPSTEIN PREMISES**, the schema's explicit-formula and count fields for `Z_Q` as named premises over a zero
configuration `Z` and an arithmetic side `rhs`. `ef` -- T1-lit, the explicit formula for `Z_Q` from the literature (Weil
1952; Bombieri-Lagarias 1999), cited, not compiled. `count` -- T3, the local count read off the bench's zero list. -/
structure EpsteinPremises (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) : Prop where
  ef : ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k → (∀ x : ℝ, k (-x) = k x) →
    (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) = rhs k
  count : ∃ A₀ : ℝ, HCount Z A₀

/-- **The Epstein configuration**: the schema's structure built from the premises, the target the strip form itself. -/
def epsteinConfig (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : EpsteinPremises Z rhs) : WeilConfig where
  toZeroConfig := Z
  rhs := rhs
  ef := hP.ef
  count := hP.count
  target := ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2
  target_iff := Iff.rfl

/-- **THE EPSTEIN NEGATIVE CONTROL, AT INTERFACES**: under the Epstein premises, with the bench's off-line zero in the
carrier, the configuration is not Weil-positive on classK. -/
theorem epstein_not_h2_sign_cfg (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : EpsteinPremises Z rhs)
    (hE : rhoE ∈ Z.carrier) : ¬ h2_sign_cfg (epsteinConfig Z rhs hP) :=
  not_h2_sign_cfg_of_offline (epsteinConfig Z rhs hP) rhoE hE rhoE_re_ne_half

/-- **The detector at the Epstein data**: the named window, its base half-width `baseWidth rhoE`, its zero side negative. -/
theorem epstein_detector (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : EpsteinPremises Z rhs)
    (hE : rhoE ∈ Z.carrier) :
    ∃ (a : List ℝ) (j : ℕ), classK (kWindow a (detectorBase rhoE) j) ∧
      Function.support (pwWindow a (detectorBase rhoE) j) ⊆ Set.Icc (-(2 ^ j * baseWidth rhoE)) (2 ^ j * baseWidth rhoE) ∧
      (zeroSide_cfg (epsteinConfig Z rhs hP) (kWindow a (detectorBase rhoE) j)).re < 0 :=
  detector (epsteinConfig Z rhs hP) rhoE hE rhoE_re_ne_half

end Schema
end SIDEExplicitFormula
