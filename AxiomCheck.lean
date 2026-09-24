import SIDEExplicitFormula.B321Identity

/-!
# Axiom audit

Run `lake env lean AxiomCheck.lean` to reproduce the `#print axioms` output for the terminals this
programme cites from SIDE-explicit-formula (ruling (R119)(1), act b510). The first is this
programme's own; the other three are vendored from zeta23 at pin v1.0. All are expected to reduce
to the standard base (`propext`, `Classical.choice`, `Quot.sound`); the compiler's output is the
verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.B321.b321_identity
#print axioms Zeta23.WeilEF.EF_lit_zetaZeroConfig
#print axioms Zeta23.EF.EF_lit
#print axioms Zeta23.WeilEF.EF_lit_zeta
