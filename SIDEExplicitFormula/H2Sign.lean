/-
SIDE-explicit-formula -- SIDEExplicitFormula/H2Sign.lean
THIS PROGRAMME'S WORK (act b510, ruling (R119)(3)-(4), (R104)'s act 4) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

h2 stated as ONE Prop on the class the kernel derives (R119)(3): the even `k` with `ContDiff ℝ 2 k`
and compact support that are of Weil's positive-definite form `h ⋆ h~` (`Zeta23.EF.weilTest h h`).
The pole term is CARRIED in the statement. `0 ≤` on `ℂ` is Mathlib's `ComplexOrder`: nonnegative real.
The ladder's "sign of A - PR" is the pole-annihilated specialization `h2_sign_aim`, defined BESIDE
`h2_sign` and not in its place. NOTHING HERE IS PROVED ABOUT THE SIGN: these are statements.
-/
import SIDEExplicitFormula.B321Identity

open Complex
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- The class K: even, `C²`, compactly supported, and of the form `h ⋆ h~` with `h` `C²` and
compactly supported. -/
def classK (k : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, k (-x) = k x) ∧ ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
    ∃ h : ℝ → ℂ, ContDiff ℝ 2 h ∧ HasCompactSupport h ∧ k = Zeta23.EF.weilTest h h

/-- **h2, as one Prop:** for every `k` in K, `0 ≤ P(k) - PR(k) + A(k)`. -/
def h2_sign : Prop :=
  ∀ k : ℝ → ℂ, classK k → 0 ≤ poleTerm k - primeSum k + archTerm k

/-- The pole-annihilated specialization: the same, over the subclass with `poleTerm k = 0`. -/
def h2_sign_aim : Prop :=
  ∀ k : ℝ → ℂ, classK k → poleTerm k = 0 → 0 ≤ poleTerm k - primeSum k + archTerm k

/-- `h2_sign` implies its pole-annihilated specialization. -/
theorem h2_sign_imp_aim : h2_sign → h2_sign_aim := fun h k hk _ => h k hk

end B321
end SIDEExplicitFormula
