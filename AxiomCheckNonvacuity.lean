import SIDEExplicitFormula.SaltCheckNonvacuity

/-!
# Axiom audit -- the salt-check of the premise table (act b642, ruling (R252)(3)(e))

Run `lake env lean AxiomCheckNonvacuity.lean` (once the module is built) to reproduce the `#print axioms` output for every witness
of SIDEExplicitFormula/SaltCheckNonvacuity.lean. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.pwSetup_zero
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.zeroSideNeg_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.farSmall_zero
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.plattTrudgianHeight_neg_one
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.symPairBound_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.zetaSeam_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.isTrivialPoint_parity
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.eulerFactorPremise_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.windowObligations_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.trivialSummandPremise'_witness'
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.analyticOnNhd_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.continuous_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.eqOn_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.hasCompactSupport_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.hasDerivAt_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.integrable_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.isOpen_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.isRoot_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.monotone_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.nat_prime_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.prime_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.strictMono_witness
#print axioms SIDEExplicitFormula.SaltCheckNonvacuity.tendsto_witness
