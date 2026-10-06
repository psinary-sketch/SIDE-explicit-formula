import SIDEExplicitFormula.Schema.Dedekind

/-!
# Axiom audit -- the Dedekind instance (act b631, ruling (R241)(3) and the author's answer before b631's seal; W-ORD-DEDEKIND-INSTANCE)

Run `lake env lean AxiomCheckDedekind.lean` (once the module is built) to reproduce the `#print axioms` output for every declaration
of SIDEExplicitFormula/Schema/Dedekind.lean, the `#check` of the instance, of the arithmetic side on its two premises and of the
statement at q = 3. Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no
`sorryAx`; the two premises are Props the arithmetic side takes as hypotheses, not axioms. The compiler`s output is the verdict, not
this comment.
-/

#print axioms SIDEExplicitFormula.Schema.Dedekind.DedekindConfig
#print axioms SIDEExplicitFormula.Schema.Dedekind.DedekindTheorem
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_instance
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_rhs
#print axioms SIDEExplicitFormula.Schema.Dedekind.dedekind_three

#check @SIDEExplicitFormula.Schema.Dedekind.dedekind_instance
#check @SIDEExplicitFormula.Schema.Dedekind.dedekind_rhs
#check @SIDEExplicitFormula.Schema.Dedekind.dedekind_three
