import SIDEExplicitFormula.Schema.DedekindRestated

/-!
# Axiom audit -- the Dedekind reading's trivial summand restated (act b642, ruling (R252)(3)(d))

Run `lake env lean AxiomCheckDedekindRestated.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Schema/DedekindRestated.lean, the `#check` of the restated premise's witness and of `dedekind_rhs'`,
and the v0.25 `dedekind_rhs` printed beside. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`; the two premises are Props `dedekind_rhs'` takes as hypotheses, not axioms. The compiler`s
output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.Dedekind.TrivialSummandPremise'
#print axioms SIDEExplicitFormula.Schema.Dedekind.trivialSummandPremise'_of_even
#print axioms SIDEExplicitFormula.Schema.Dedekind.trivialSummandPremise'_witness
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_rhs'
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_three_v026
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_rhs

#check @SIDEExplicitFormula.Schema.Dedekind.trivialSummandPremise'_witness
#check @SIDEExplicitFormula.Schema.Dedekind.dedekind_rhs'
#check @SIDEExplicitFormula.Schema.Dedekind.dedekind_three_v026
