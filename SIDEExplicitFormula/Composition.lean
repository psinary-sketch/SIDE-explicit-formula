/-
SIDE-explicit-formula -- SIDEExplicitFormula/Composition.lean
THIS PROGRAMME'S WORK (act b770, ruling (R380)(4)(d), by (R379)(7)(a); relay data/b770_plan.txt (4)(d)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE COMPOSITION. `DirichletHypothesis` is one proposition over each modulus and each character: every zero of Mathlib's
`DirichletCharacter.LFunction χ` in the strip `0 < re s < 1` has real part `1/2`. On that premise, for each modulus `q`, the
summed configuration of the characters modulo `q` other than the trivial one, each at its primitive character, satisfies
Weil positivity on classK (`familyConfig_h2_sign`), by the arrow of `Schema.Family.family_theorem` (Schema/Family.lean :213)
from its right side to its left, `GRHWeil.GRH_chi` (GRHWeil.lean :53) taking its hypotheses in the order zero, `0 < re`,
`re < 1`. With Mathlib's `RiemannHypothesis` beside it as a second premise, Weil positivity on classK at zeta and at each
such family in one statement (`positivity_of_premises`), its half at zeta being `B321.rh_imp_h2_sign` (RHChain.lean :24) as
it stands. At modulus 1 the premise on the L-functions contains the statement for zeta in the strip; that is not used here.

INTERFACES on the named premises: each statement binds its premises and nothing else, its conclusion restates no premise,
and each premise is worded in Mathlib's predicates and the kernel's. Nothing here proves either premise. Nothing of any
other Lean archive is imported or copied.
-/
import SIDEExplicitFormula.Schema.Family

noncomputable section

namespace SIDEExplicitFormula

/-- **The premise on the Dirichlet L-functions, as one proposition**: for each modulus `N` and each character `χ` mod `N`,
every zero of `DirichletCharacter.LFunction χ` with `0 < re s < 1` has real part `1/2`. Named here; NOT DISCHARGED. -/
def DirichletHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 →
    DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- **On the premise, the family's positivity at each modulus**: the summed configuration of the characters mod `q` other
than the trivial one, each at its primitive character, satisfies Weil positivity on classK. -/
theorem familyConfig_h2_sign (H : DirichletHypothesis) (q : ℕ) [NeZero q] :
    Schema.h2_sign_cfg (Schema.Family.familyConfig q) := by
  refine (Schema.Family.family_theorem q).mpr fun χ _ => ?_
  intro s hz h0 h1
  exact H χ.conductor χ.primitiveCharacter s h0 h1 hz

/-- **The two premises joined**: on Mathlib's `RiemannHypothesis` and the premise on the Dirichlet L-functions, Weil
positivity on classK at zeta, by `B321.rh_imp_h2_sign`, and at each family, by `familyConfig_h2_sign`. -/
theorem positivity_of_premises (H0 : RiemannHypothesis) (H : DirichletHypothesis) :
    B321.h2_sign ∧ ∀ (q : ℕ) [NeZero q], Schema.h2_sign_cfg (Schema.Family.familyConfig q) := by
  refine ⟨B321.rh_imp_h2_sign H0, ?_⟩
  intro q _
  exact familyConfig_h2_sign H q

end SIDEExplicitFormula
