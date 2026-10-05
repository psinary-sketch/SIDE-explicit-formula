/-
SIDE-explicit-formula -- SIDEExplicitFormula/Simplicity.lean
THIS PROGRAMME'S WORK (act b596, ruling (R206)(4)(b); W-ORD-SIMPLICITY-FACE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE TITLE'S CLAUSE AS A PROP, AND THE PROPORTION BESIDE IT AS A NAMED PREMISE. `allSimple C` -- every point of a
configuration of the schema (`Schema.WeilConfig`) has multiplicity one. `simplicity` -- the clause over the genuine
configuration, `Schema.zetaWeilConfig`, whose carrier is the nontrivial zeros of Mathlib's `riemannZeta` (Zeta23's
`zetaZeroConfig`) and whose multiplicity is the analytic order (`Zeta23.zeroMult`); `simplicity_iff` checks that reading
by definition. `SimpleProportion` -- the proportion of simple zeros on the critical line as a NAMED PREMISE: its one field
is the statement of `Zeta23.thmB₀_mult` (anthropics/formal-math, `Zeta23/FinalMult.lean` :350 at the upstream pin
v1.0 = 3635e748), copied as a statement; that module is not in the vendored set (relay data/b596_lemmas.txt), so the
proportion is premised here, not compiled. `exceptional_mass_le_third` -- under that premise, the part of the count with
multiplicity that is not a simple zero on the line is eventually at most a third. The salt-check is
SIDEExplicitFormula/SaltCheckSimplicity.lean. NOTHING HERE PROVES THE CLAUSE OR ITS NEGATION, OR RH, OR LOCATES ANY ZERO.
-/
import SIDEExplicitFormula.Schema.Instances

noncomputable section

namespace SIDEExplicitFormula
namespace Simplicity

open Schema

/-- **Every point of a configuration of the schema has multiplicity one.** -/
def allSimple (C : WeilConfig) : Prop := ∀ ρ ∈ C.carrier, C.mult ρ = 1

/-- **THE TITLE'S CLAUSE, OVER THE GENUINE CONFIGURATION**: every nontrivial zero of Mathlib's `riemannZeta` has
multiplicity one. -/
def simplicity : Prop := allSimple zetaWeilConfig

/-- **The check**: the clause is, by definition, every nontrivial zero (`ζ ρ = 0`, `0 < Re ρ < 1`) of analytic order one. -/
theorem simplicity_iff : simplicity ↔ ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → Zeta23.zeroMult ρ = 1 :=
  Iff.rfl

/-- **THE PROPORTION, A NAMED PREMISE.** Its field is the statement of `Zeta23.thmB₀_mult` at the upstream pin v1.0 =
3635e748 (`Zeta23/FinalMult.lean` :350, not vendored): for every `ε > 0` and all large `T`, at least `(2/3 − ε)` of the
nontrivial zeros with `T < Im ρ ≤ 2T`, counted with multiplicity, are simple and on the critical line. -/
structure SimpleProportion : Prop where
  /-- **THE CITATION (act b628, ruling (R238)(4)).** This field is the statement of `Zeta23.thmB₀_mult`
  (`Zeta23/FinalMult.lean` :350) in the repository github.com/anthropics/formal-math at the pin v1.0 =
  3635e74826a4c1fcece7d1cd2b6fa75e43a00510, toolchain leanprover/lean4:v4.33.0-rc2 with Mathlib 51e6992e. Its axiom
  profile, `[propext, Classical.choice, Quot.sound]`, is read from that repository's `AUDIT.md` :80 at the pin -- the
  upstream's recorded run, not a build made here -- and banked with `ThmB_statement`'s print from a build of
  `Zeta23.Statement` in a clone at the pin (relay `data/b628_zeta23_axioms.txt`, sha256
  0ce2338fef17abcf5acf4ff5bc218a5590a873b7ceaa47304c79571a0f43bb85). The theorem is
  discharged at its source kernel, not in this one: here the field stays a named premise, and
  `exceptional_mass_le_third` stays INTERFACES on it. -/
  two_thirds : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T)

/-- **AT INTERFACES ON THE PROPORTION**: under the named premise, the count with multiplicity less the simple zeros on
the line is eventually at most `(1/3 + ε)` of the count. -/
theorem exceptional_mass_le_third (hP : SimpleProportion) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.Ncount T (2 * T) : ℝ) - (Zeta23.N0simple T (2 * T) : ℝ) ≤ (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := hP.two_thirds ε hε
  exact ⟨T₀, fun T hT => by
    have h1 := h T hT
    have e : (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        = (Zeta23.Ncount T (2 * T) : ℝ) - (2 / 3 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) := by ring
    rw [e]
    linarith⟩

end Simplicity
end SIDEExplicitFormula
