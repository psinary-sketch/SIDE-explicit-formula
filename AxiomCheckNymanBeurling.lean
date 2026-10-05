import SIDEExplicitFormula.NymanBeurling

/-!
# Axiom audit -- the Nyman–Beurling face (act b629, ruling (R239)(4); W-ORD-NYMAN-BEURLING-FACE)

Run `lake env lean AxiomCheckNymanBeurling.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/NymanBeurling.lean, the `#check` of the face and of d_N's monotonicity, and the `#print` of the
premise. Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`;
the premise is a structure the face takes as its one hypothesis, not an axiom. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.NymanBeurling.unitMeasure
#print axioms SIDEExplicitFormula.NymanBeurling.rhoFun
#print axioms SIDEExplicitFormula.NymanBeurling.rhoFun_measurable
#print axioms SIDEExplicitFormula.NymanBeurling.rhoFun_bound
#print axioms SIDEExplicitFormula.NymanBeurling.rhoFun_memLp
#print axioms SIDEExplicitFormula.NymanBeurling.rho
#print axioms SIDEExplicitFormula.NymanBeurling.constOne
#print axioms SIDEExplicitFormula.NymanBeurling.NB
#print axioms SIDEExplicitFormula.NymanBeurling.BD
#print axioms SIDEExplicitFormula.NymanBeurling.NymanBeurlingPremise
#print axioms SIDEExplicitFormula.NymanBeurling.rh_iff_nb
#print axioms SIDEExplicitFormula.NymanBeurling.distN
#print axioms SIDEExplicitFormula.NymanBeurling.distN_antitone

#check @SIDEExplicitFormula.NymanBeurling.rh_iff_nb
#check @SIDEExplicitFormula.NymanBeurling.distN_antitone

#print SIDEExplicitFormula.NymanBeurling.NymanBeurlingPremise
