import SIDEExplicitFormula.RestBound

/-!
# Axiom audit -- (f3), the other zeros bounded above, with its limit printed

Run `lake env lean AxiomCheckRest.lean` to reproduce the `#print axioms` output for (f3) of W-ORD-WEIL-CONVERSE (ruling
(R140)(2), act b530): Component 1, the decay lemma (d') and its window form (`DecayBound.lean`); Component 2, the rest
bounded under H-STRIP and H-COUNT (`rest_bound`), with its closed-strip and zeta forms; Component 3, the exponent
comparison; with the lemmas they rest on. Each is expected to reduce to the standard base (`propext`,
`Classical.choice`, `Quot.sound`); the compiler's output is the verdict, not this comment. The `#check` lines show
`HStrip`, `HCount`, `f4_needs` and `HMax` elaborating as Props; the `#print` lines show `restR` and `windowA` from their
definitions. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.hasCompactSupport_of_Icc
#print axioms SIDEExplicitFormula.B321.support_deriv_Icc
#print axioms SIDEExplicitFormula.B321.support_iteratedDeriv_Icc
#print axioms SIDEExplicitFormula.B321.paperFT_iteratedDeriv
#print axioms SIDEExplicitFormula.B321.paperFT_decay
#print axioms SIDEExplicitFormula.B321.paperFT_decay_re
#print axioms SIDEExplicitFormula.B321.paperFT_decay_zero
#print axioms SIDEExplicitFormula.B321.cosWin_support_Icc
#print axioms SIDEExplicitFormula.B321.window_decay_re
#print axioms SIDEExplicitFormula.B321.rest_bound
#print axioms SIDEExplicitFormula.B321.rest_bound_closed
#print axioms SIDEExplicitFormula.B321.rest_bound_zeta
#print axioms SIDEExplicitFormula.B321.finite_rest_bound
#print axioms SIDEExplicitFormula.B321.rest_le_of_finite
#print axioms SIDEExplicitFormula.B321.restR_nonneg
#print axioms SIDEExplicitFormula.B321.fiber_count
#print axioms SIDEExplicitFormula.B321.summable_zeta3
#print axioms SIDEExplicitFormula.B321.zeta3Sum_nonneg
#print axioms SIDEExplicitFormula.B321.zero_term_bound
#print axioms SIDEExplicitFormula.B321.weight_ineq
#print axioms SIDEExplicitFormula.B321.kWin_bound
#print axioms SIDEExplicitFormula.B321.window_bound
#print axioms SIDEExplicitFormula.B321.cosWin_bound
#print axioms SIDEExplicitFormula.B321.gammaOf_re'
#print axioms SIDEExplicitFormula.B321.gammaOf_im'
#print axioms SIDEExplicitFormula.B321.cosh_le_exp_abs
#print axioms SIDEExplicitFormula.B321.realizedGrowth_le_exp
#print axioms SIDEExplicitFormula.B321.two_delta_lt_one
#print axioms SIDEExplicitFormula.B321.not_f4_needs
#print axioms SIDEExplicitFormula.B321.f4_needs_of_half_le

#check @SIDEExplicitFormula.B321.HStrip
#check @SIDEExplicitFormula.B321.HCount
#check @SIDEExplicitFormula.B321.f4_needs
#check @SIDEExplicitFormula.B321.HMax
#print SIDEExplicitFormula.B321.restR
#print SIDEExplicitFormula.B321.windowA
#print SIDEExplicitFormula.B321.zeta3Sum
#print SIDEExplicitFormula.B321.f4_needs
#print SIDEExplicitFormula.B321.HMax
#print SIDEExplicitFormula.B321.HCount
#print SIDEExplicitFormula.B321.HStrip
#print SIDEExplicitFormula.B321.pairOrbit
