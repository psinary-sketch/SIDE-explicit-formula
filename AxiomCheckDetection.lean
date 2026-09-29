import SIDEExplicitFormula.DetectionRegion

/-!
# Axiom audit -- the detection region, HELD (act b559, ruling (R169))

Run `lake env lean AxiomCheckDetection.lean` to reproduce the `#print axioms` output for the declarations of
`SIDEExplicitFormula/DetectionRegion.lean`, on the branch `detection-region-b559` only. The compiled companions are
expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less; `j₀` and
`detection_region` carry `sorryAx`, which is why the branch is HELD. The compiler's output is the verdict, not this
comment. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.h2_sign_upto
#print axioms SIDEExplicitFormula.B321.h2_sign_upto_mono
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_upto
#print axioms SIDEExplicitFormula.B321.upto_all_imp_h2_sign
#print axioms SIDEExplicitFormula.B321.h2_sign_iff_forall_upto
#print axioms SIDEExplicitFormula.B321.forall_upto_iff_rh
#print axioms SIDEExplicitFormula.B321.ellOf
#print axioms SIDEExplicitFormula.B321.j₀
#print axioms SIDEExplicitFormula.B321.detection_region

#check @SIDEExplicitFormula.B321.h2_sign_upto
#check @SIDEExplicitFormula.B321.h2_sign_iff_forall_upto
#check @SIDEExplicitFormula.B321.forall_upto_iff_rh
#check @SIDEExplicitFormula.B321.ellOf
#check @SIDEExplicitFormula.B321.detection_region
#print RiemannHypothesis
