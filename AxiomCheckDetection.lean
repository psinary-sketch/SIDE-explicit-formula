import SIDEExplicitFormula.DetectionRegion

/-!
# Axiom audit -- the detection region's clean part (acts b559 and b560, rulings (R169) and (R170)(1))

Run `lake env lean AxiomCheckDetection.lean` to reproduce the `#print axioms` output for the declarations of
`SIDEExplicitFormula/DetectionRegion.lean`. Each is expected to reduce to the standard base (`propext`,
`Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler's output is the verdict, not this comment.
The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.h2_sign_upto
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_upto
#print axioms SIDEExplicitFormula.B321.upto_all_imp_h2_sign
#print axioms SIDEExplicitFormula.B321.h2_sign_iff_forall_upto
#print axioms SIDEExplicitFormula.B321.forall_upto_iff_rh

#check @SIDEExplicitFormula.B321.h2_sign_upto
#check @SIDEExplicitFormula.B321.h2_sign_iff_forall_upto
#check @SIDEExplicitFormula.B321.forall_upto_iff_rh
#print RiemannHypothesis
