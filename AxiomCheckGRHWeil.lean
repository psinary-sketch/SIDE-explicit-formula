import SIDEExplicitFormula.GRHWeil

/-!
# Axiom audit -- GRH-Weil, act one: the χ-side statement layer, the seam and the pairing (act b562, ruling (R172)(4))

Run `lake env lean AxiomCheckGRHWeil.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of `SIDEExplicitFormula/GRHWeil.lean`, and the `#print` of each statement-layer definition (the salt-check).
Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`.
The compiler's output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.GRHWeil.parity
#print axioms SIDEExplicitFormula.GRHWeil.IsTrivialPoint
#print axioms SIDEExplicitFormula.GRHWeil.GRH_chi
#print axioms SIDEExplicitFormula.GRHWeil.GRH_chi_trivial
#print axioms SIDEExplicitFormula.GRHWeil.primeSum_chi
#print axioms SIDEExplicitFormula.GRHWeil.gammaBracket_chi
#print axioms SIDEExplicitFormula.GRHWeil.archTerm_chi
#print axioms SIDEExplicitFormula.GRHWeil.h2_sign_chi
#print axioms SIDEExplicitFormula.GRHWeil.ne_one_of_ne_one
#print axioms SIDEExplicitFormula.GRHWeil.isPrimitive_inv
#print axioms SIDEExplicitFormula.GRHWeil.gammaFactor_ne_zero_of_re_pos
#print axioms SIDEExplicitFormula.GRHWeil.trivialPoint_of_gammaFactor_eq_zero
#print axioms SIDEExplicitFormula.GRHWeil.LFunction_zero_re_nonpos
#print axioms SIDEExplicitFormula.GRHWeil.re_nonpos_of_trivialPoint
#print axioms SIDEExplicitFormula.GRHWeil.GRH_chi_iff_trivial
#print axioms SIDEExplicitFormula.GRHWeil.LFunction_conj_of_one_lt_re
#print axioms SIDEExplicitFormula.GRHWeil.LFunction_inv_conj
#print axioms SIDEExplicitFormula.GRHWeil.LFunction_zero_iff_conj
#print axioms SIDEExplicitFormula.GRHWeil.analyticOrderAt_LFunction_inv_conj

#print SIDEExplicitFormula.GRHWeil.GRH_chi
#print SIDEExplicitFormula.GRHWeil.GRH_chi_trivial
#print SIDEExplicitFormula.GRHWeil.IsTrivialPoint
#print SIDEExplicitFormula.GRHWeil.parity
#print SIDEExplicitFormula.GRHWeil.primeSum_chi
#print SIDEExplicitFormula.GRHWeil.gammaBracket_chi
#print SIDEExplicitFormula.GRHWeil.archTerm_chi
#print SIDEExplicitFormula.GRHWeil.h2_sign_chi
#check @SIDEExplicitFormula.GRHWeil.LFunction_zero_re_nonpos
#check @SIDEExplicitFormula.GRHWeil.GRH_chi_iff_trivial
#check @SIDEExplicitFormula.GRHWeil.LFunction_inv_conj
#check @SIDEExplicitFormula.GRHWeil.LFunction_zero_iff_conj
#check @SIDEExplicitFormula.GRHWeil.analyticOrderAt_LFunction_inv_conj
#print DirichletCharacter.LFunction
#print DirichletCharacter.gammaFactor
