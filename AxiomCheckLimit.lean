import SIDEExplicitFormula.PowerLimit

/-!
# Axiom audit -- f4, the power-window route, act two of two (L7-L8 and the assembly)

Run `lake env lean AxiomCheckLimit.lean` to reproduce the `#print axioms` output for act b534 (ruling (R144)): every theorem of
`SIDEExplicitFormula/PowerLimit.lean`. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`); the compiler's output is the verdict, not this comment. The `#check` lines print the three statements (R144)
orders read last, the named Prop the assembly is compiled from, and b533's superseded Prop beside its successor. The
AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.paperFT_conj_of_real
#print axioms SIDEExplicitFormula.B321.paperFT_neg_of_even
#print axioms SIDEExplicitFormula.B321.zero_term_real
#print axioms SIDEExplicitFormula.B321.paperFT_polyOpFull
#print axioms SIDEExplicitFormula.B321.polyOpFull_support
#print axioms SIDEExplicitFormula.B321.polyOpFull_contDiff
#print axioms SIDEExplicitFormula.B321.pwWindow_contDiff
#print axioms SIDEExplicitFormula.B321.pwWindow_support
#print axioms SIDEExplicitFormula.B321.kWindow_classK
#print axioms SIDEExplicitFormula.B321.kWindow_term
#print axioms SIDEExplicitFormula.B321.wOf_eq
#print axioms SIDEExplicitFormula.B321.wOf_sq
#print axioms SIDEExplicitFormula.B321.norm_wOf
#print axioms SIDEExplicitFormula.B321.gammaOf_sq
#print axioms SIDEExplicitFormula.B321.vOf_re
#print axioms SIDEExplicitFormula.B321.vOf_im
#print axioms SIDEExplicitFormula.B321.v_eq_iff
#print axioms SIDEExplicitFormula.B321.nodes_distinct
#print axioms SIDEExplicitFormula.B321.reflect_re
#print axioms SIDEExplicitFormula.B321.reflect_im
#print axioms SIDEExplicitFormula.B321.gammaOf_reflect
#print axioms SIDEExplicitFormula.B321.vOf_reflect
#print axioms SIDEExplicitFormula.B321.paperFT_conj_eq
#print axioms SIDEExplicitFormula.B321.offScore_reflect
#print axioms SIDEExplicitFormula.B321.paperFT_of_sq_eq
#print axioms SIDEExplicitFormula.B321.tie_reflect
#print axioms SIDEExplicitFormula.B321.PWSetup.c4
#print axioms SIDEExplicitFormula.B321.PWSetup.tfin
#print axioms SIDEExplicitFormula.B321.PWSetup.kfin
#print axioms SIDEExplicitFormula.B321.mem_TF
#print axioms SIDEExplicitFormula.B321.mem_KF
#print axioms SIDEExplicitFormula.B321.cE_pos
#print axioms SIDEExplicitFormula.B321.cE_big
#print axioms SIDEExplicitFormula.B321.aeval_real
#print axioms SIDEExplicitFormula.B321.aeval_conj
#print axioms SIDEExplicitFormula.B321.aeval_X_sq_comp
#print axioms SIDEExplicitFormula.B321.aeval_Ep
#print axioms SIDEExplicitFormula.B321.Ep_prod
#print axioms SIDEExplicitFormula.B321.Pof_eval
#print axioms SIDEExplicitFormula.B321.Pof_prod
#print axioms SIDEExplicitFormula.B321.polyEvalFull_coeffList
#print axioms SIDEExplicitFormula.B321.vOf_real_of_on
#print axioms SIDEExplicitFormula.B321.Kp_kill
#print axioms SIDEExplicitFormula.B321.Kp_tie_ne
#print axioms SIDEExplicitFormula.B321.Efac_ne
#print axioms SIDEExplicitFormula.B321.gHat_ne
#print axioms SIDEExplicitFormula.B321.Xval_ne
#print axioms SIDEExplicitFormula.B321.Xval_norm
#print axioms SIDEExplicitFormula.B321.Nf_pos
#print axioms SIDEExplicitFormula.B321.Xval_real_neg
#print axioms SIDEExplicitFormula.B321.rep_spec
#print axioms SIDEExplicitFormula.B321.XV_node
#print axioms SIDEExplicitFormula.B321.XV_conj
#print axioms SIDEExplicitFormula.B321.sqrtC_sq
#print axioms SIDEExplicitFormula.B321.norm_sqrtC
#print axioms SIDEExplicitFormula.B321.XV_ne
#print axioms SIDEExplicitFormula.B321.norm_Yv
#print axioms SIDEExplicitFormula.B321.Yv_ne
#print axioms SIDEExplicitFormula.B321.Yv_mul
#print axioms SIDEExplicitFormula.B321.Yv_conj
#print axioms SIDEExplicitFormula.B321.rT_conj
#print axioms SIDEExplicitFormula.B321.rT_norm
#print axioms SIDEExplicitFormula.B321.rT_sq_mul
#print axioms SIDEExplicitFormula.B321.VF_conj
#print axioms SIDEExplicitFormula.B321.poly_norm_le
#print axioms SIDEExplicitFormula.B321.fixed_poly_bound
#print axioms SIDEExplicitFormula.B321.coeffs_exist
#print axioms SIDEExplicitFormula.B321.term_eq
#print axioms SIDEExplicitFormula.B321.tie_term_neg
#print axioms SIDEExplicitFormula.B321.kill_term_zero
#print axioms SIDEExplicitFormula.B321.rest_term_small
#print axioms SIDEExplicitFormula.B321.ceil_weight
#print axioms SIDEExplicitFormula.B321.Aw_nonneg
#print axioms SIDEExplicitFormula.B321.zero_weight
#print axioms SIDEExplicitFormula.B321.weighted_finite_bound
#print axioms SIDEExplicitFormula.B321.weighted_summable
#print axioms SIDEExplicitFormula.B321.dominant_summable
#print axioms SIDEExplicitFormula.B321.fR_norm_le
#print axioms SIDEExplicitFormula.B321.fR_bound
#print axioms SIDEExplicitFormula.B321.rest_tendsto_zero
#print axioms SIDEExplicitFormula.B321.mem_sT
#print axioms SIDEExplicitFormula.B321.zeroSide_eventually_neg
#print axioms SIDEExplicitFormula.B321.zeroSideNeg_holds
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_rh_strip_of
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_rh_strip
#print axioms SIDEExplicitFormula.B321.rh_strip_imp_h2_sign
#print axioms SIDEExplicitFormula.B321.h2_sign_iff_rh_strip
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_rh_of_seam
#print axioms SIDEExplicitFormula.B321.ch_iff_h2_sign_of_seam

#check @SIDEExplicitFormula.B321.zeroSideNeg
#check @SIDEExplicitFormula.B321.nodes_distinct_nonreal
#check @SIDEExplicitFormula.B321.nodes_distinct
#check @SIDEExplicitFormula.B321.h2_sign_iff_rh_strip
#check @SIDEExplicitFormula.B321.h2_sign_imp_rh_of_seam
#check @SIDEExplicitFormula.B321.rh_strip_imp_rh
