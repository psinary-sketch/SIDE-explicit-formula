import SIDEExplicitFormula.PlattRung

/-!
# Axiom audit -- the height rung, its pair and its named premise (act b626, ruling (R236)(5) and the author's answer before b626's seal)

Run `lake env lean AxiomCheckPlattRung.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/PlattRung.lean and for the vendored bridge it consumes by name, the `#check` of the pair and the
rung, and the `#print` of each definition. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`; the premise is a structure the rung takes as its one hypothesis, not an axiom. The
compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.PlattRung.rh_upto
#print axioms SIDEExplicitFormula.PlattRung.forall_rh_upto_iff_rh
#print axioms SIDEExplicitFormula.PlattRung.plattTrudgianT
#print axioms SIDEExplicitFormula.PlattRung.PlattTrudgianHeight
#print axioms SIDEExplicitFormula.PlattRung.rh_upto_platt
#print axioms LiCriterion.rh_equiv_mathlib

#check @SIDEExplicitFormula.PlattRung.forall_rh_upto_iff_rh
#check @SIDEExplicitFormula.PlattRung.rh_upto_platt

#print SIDEExplicitFormula.PlattRung.rh_upto
#print SIDEExplicitFormula.PlattRung.plattTrudgianT
#print SIDEExplicitFormula.PlattRung.PlattTrudgianHeight
