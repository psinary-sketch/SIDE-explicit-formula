import SIDEExplicitFormula.Schema.FamilyPremises

/-!
# Axiom audit -- the Dedekind reading's two premises read in the kernel (act b642, ruling (R252)(3)(c))

Run `lake env lean AxiomCheckFamilyPremises.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Schema/FamilyPremises.lean and the `#check` of the refutation, the sufficiency and the refutation at
the modulus 6. Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`.
The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.Family.parity_one
#print axioms SIDEExplicitFormula.Schema.Family.one_apply_nat
#print axioms SIDEExplicitFormula.Schema.Family.archTerm_chi_one
#print axioms SIDEExplicitFormula.Schema.Family.log_nat_gt_half
#print axioms SIDEExplicitFormula.Schema.Family.poleTerm_box_half
#print axioms SIDEExplicitFormula.Schema.Family.not_trivialSummandPremise
#print axioms SIDEExplicitFormula.Schema.Family.primitiveCharacter_apply_nat
#print axioms SIDEExplicitFormula.Schema.Family.eulerFactorPremise_of_primitive
#print axioms SIDEExplicitFormula.Schema.Family.primitive_of_ne_one_three
#print axioms SIDEExplicitFormula.Schema.Family.eulerFactorPremise_three
#print axioms SIDEExplicitFormula.Schema.Family.pointLog2
#print axioms SIDEExplicitFormula.Schema.Family.paperFT_pointLog2
#print axioms SIDEExplicitFormula.Schema.Family.archTerm_chi_pointLog2
#print axioms SIDEExplicitFormula.Schema.Family.log_nat_eq_log_two
#print axioms SIDEExplicitFormula.Schema.Family.neg_log_nat_ne_log_two
#print axioms SIDEExplicitFormula.Schema.Family.not_eulerFactorPremise_six

#check @SIDEExplicitFormula.Schema.Family.not_trivialSummandPremise
#check @SIDEExplicitFormula.Schema.Family.eulerFactorPremise_of_primitive
#check @SIDEExplicitFormula.Schema.Family.eulerFactorPremise_three
#check @SIDEExplicitFormula.Schema.Family.not_eulerFactorPremise_six
