import SIDEExplicitFormula.Seam

/-!
# Axiom audit -- the seam from the functional equation (act b536, ruling (R146))

Run `lake env lean AxiomCheckSeam.lean` to reproduce the `#print axioms` output for the theorems of
`SIDEExplicitFormula/Seam.lean`. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`); the compiler's output is the verdict, not this comment. The `#check` lines print the statements read;
`#print RiemannHypothesis` prints Mathlib's statement at this pin. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.zeta_zero_re_nonpos
#print axioms SIDEExplicitFormula.B321.rh_strip_imp_rh_holds
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_rh_holds
#print axioms SIDEExplicitFormula.B321.h2_sign_iff_rh
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_ch_holds
#print axioms SIDEExplicitFormula.B321.ch_iff_h2_sign

#print RiemannHypothesis
#check @SIDEExplicitFormula.B321.zeta_zero_re_nonpos
#check @SIDEExplicitFormula.B321.rh_strip_imp_rh_holds
#check @SIDEExplicitFormula.B321.h2_sign_iff_rh
#check @SIDEExplicitFormula.B321.ch_iff_h2_sign
#check @SIDEExplicitFormula.B321.h2_sign_imp_rh_holds
#check @SIDEExplicitFormula.B321.h2_sign_imp_ch_holds
