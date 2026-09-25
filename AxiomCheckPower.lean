import SIDEExplicitFormula.PowerWindow

/-!
# Axiom audit -- f4, the power-window route, act one of two (L1-L6 and the seam)

Run `lake env lean AxiomCheckPower.lean` to reproduce the `#print axioms` output for act b533 (ruling (R143)): L1
(`paperFT_conj_of_real_even`, `zero_term_sq`), L2 (`weilTest_even_of_even`, `classK_of_real_even`), L3 (the powers),
L4 (the polynomial operator), L5 (the base window and the dominant zero), L6 (`real_even_interpolant`) and the seam
(`rh_imp_rh_strip`). Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`); the
compiler's output is the verdict, not this comment. The `#print` lines show `tieSet`, `killSet` and `offScore` from
their definitions; the `#check` lines show the Props stated and not proved. The AxiomCheck files of earlier acts are
left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.paperFT_conj_of_real_even
#print axioms SIDEExplicitFormula.B321.zero_term_sq
#print axioms SIDEExplicitFormula.B321.weilTest_even_of_even
#print axioms SIDEExplicitFormula.B321.classK_of_real_even
#print axioms SIDEExplicitFormula.B321.weilTest_phiC
#print axioms SIDEExplicitFormula.B321.selfConv_im_zero
#print axioms SIDEExplicitFormula.B321.selfConv_eq
#print axioms SIDEExplicitFormula.B321.phiC_selfConv
#print axioms SIDEExplicitFormula.B321.selfConv_even
#print axioms SIDEExplicitFormula.B321.selfConv_support
#print axioms SIDEExplicitFormula.B321.selfConv_contDiff
#print axioms SIDEExplicitFormula.B321.power_even
#print axioms SIDEExplicitFormula.B321.power_support
#print axioms SIDEExplicitFormula.B321.power_contDiff
#print axioms SIDEExplicitFormula.B321.paperFT_power
#print axioms SIDEExplicitFormula.B321.paperFT_sum
#print axioms SIDEExplicitFormula.B321.neg_one_pow_mul_iz_pow
#print axioms SIDEExplicitFormula.B321.paperFT_polyOp
#print axioms SIDEExplicitFormula.B321.iteratedDeriv_even_even
#print axioms SIDEExplicitFormula.B321.polyOp_even
#print axioms SIDEExplicitFormula.B321.polyOp_support
#print axioms SIDEExplicitFormula.B321.polyOp_contDiff
#print axioms SIDEExplicitFormula.B321.plateau_support_Icc
#print axioms SIDEExplicitFormula.B321.plateau_nonneg
#print axioms SIDEExplicitFormula.B321.plateau_integral_pos
#print axioms SIDEExplicitFormula.B321.base_nonzero_at
#print axioms SIDEExplicitFormula.B321.off_finite_above
#print axioms SIDEExplicitFormula.B321.dominant_exists
#print axioms SIDEExplicitFormula.B321.plateau_dominant
#print axioms SIDEExplicitFormula.B321.tieSet_finite
#print axioms SIDEExplicitFormula.B321.killSet_finite
#print axioms SIDEExplicitFormula.B321.tieSet_nonempty
#print axioms SIDEExplicitFormula.B321.real_even_interpolant
#print axioms SIDEExplicitFormula.B321.rh_imp_rh_strip

#print SIDEExplicitFormula.B321.offScore
#print SIDEExplicitFormula.B321.tieSet
#print SIDEExplicitFormula.B321.killSet
#check @SIDEExplicitFormula.B321.nodes_distinct_nonreal
#check @SIDEExplicitFormula.B321.rh_strip
#check @SIDEExplicitFormula.B321.rh_strip_imp_rh
