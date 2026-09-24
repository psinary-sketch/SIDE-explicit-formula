import SIDEExplicitFormula.RHChain

/-!
# Axiom audit -- the chain RH -> h2_sign -> cell form

Run `lake env lean AxiomCheckChain.lean` to reproduce the `#print axioms` output for the three links of
the chain (ruling (R122)(1), act b513): `rh_imp_h2_sign` (RH -> h2_sign), `h2_sign_imp_cell`
(h2_sign -> the cell form, act b512) and `rh_imp_cell_form` (their composite). All are expected to
reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`); the compiler's output is the
verdict, not this comment. `AxiomCheck.lean` (act b510) is left as it stands.
-/

#print axioms SIDEExplicitFormula.B321.rh_imp_h2_sign
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_cell
#print axioms SIDEExplicitFormula.B321.rh_imp_cell_form
