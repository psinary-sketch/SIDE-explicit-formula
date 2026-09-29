import SIDEExplicitFormula.LiWeilSym

/-!
# Axiom audit -- the Li-Weil bridge at the symmetric family: (D1')-(D4') and li_identity_sym (act b563, ruling (R173)(4))

Run `lake env lean AxiomCheckLiWeilSym.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of `SIDEExplicitFormula/LiWeilSym.lean`, and the `#print` of each definition (the salt-check).
Each is expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`.
The compiler's output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.LiWeil.smoothTransition_one_sub
#print axioms SIDEExplicitFormula.LiWeil.symCut
#print axioms SIDEExplicitFormula.LiWeil.symMember
#print axioms SIDEExplicitFormula.LiWeil.symCut_contDiff
#print axioms SIDEExplicitFormula.LiWeil.symCut_nonneg
#print axioms SIDEExplicitFormula.LiWeil.symCut_le_one
#print axioms SIDEExplicitFormula.LiWeil.symCut_eq_zero_right
#print axioms SIDEExplicitFormula.LiWeil.symCut_eq_zero_left
#print axioms SIDEExplicitFormula.LiWeil.symCut_eq_one
#print axioms SIDEExplicitFormula.LiWeil.symMember_classEF
#print axioms SIDEExplicitFormula.LiWeil.symMember_EF
#print axioms SIDEExplicitFormula.LiWeil.symMember_integrand
#print axioms SIDEExplicitFormula.LiWeil.blTest_integrand_neg
#print axioms SIDEExplicitFormula.LiWeil.symMember_transform_tendsto
#print axioms SIDEExplicitFormula.LiWeil.LiLimitExchangeSym
#print axioms SIDEExplicitFormula.LiWeil.I_gammaOf_mul
#print axioms SIDEExplicitFormula.LiWeil.symMember_transform_conj
#print axioms SIDEExplicitFormula.LiWeil.conjEquiv
#print axioms SIDEExplicitFormula.LiWeil.symZeroSum_conj
#print axioms SIDEExplicitFormula.LiWeil.symZeroSum_im
#print axioms SIDEExplicitFormula.LiWeil.SymPairBound
#print axioms SIDEExplicitFormula.LiWeil.symMember_integrand_exp
#print axioms SIDEExplicitFormula.LiWeil.symMember_transform_re
#print axioms SIDEExplicitFormula.LiWeil.integral_mul_cos_ibp
#print axioms SIDEExplicitFormula.LiWeil.blPoly_contDiff_infty
#print axioms SIDEExplicitFormula.LiWeil.qf
#print axioms SIDEExplicitFormula.LiWeil.qf1
#print axioms SIDEExplicitFormula.LiWeil.qf2
#print axioms SIDEExplicitFormula.LiWeil.exp_mul_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.qf_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.qf1_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.qf_bounds
#print axioms SIDEExplicitFormula.LiWeil.wf
#print axioms SIDEExplicitFormula.LiWeil.wf1
#print axioms SIDEExplicitFormula.LiWeil.wf2
#print axioms SIDEExplicitFormula.LiWeil.wf_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.wf1_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.jump_cos_bound
#print axioms SIDEExplicitFormula.LiWeil.integral_mul_cexp_ibp
#print axioms SIDEExplicitFormula.LiWeil.integral_mul_cexp_ibp_iter
#print axioms SIDEExplicitFormula.LiWeil.edgeProfile
#print axioms SIDEExplicitFormula.LiWeil.deriv_smoothTransition_eq_zero
#print axioms SIDEExplicitFormula.LiWeil.edgeProfile_contDiff
#print axioms SIDEExplicitFormula.LiWeil.edgeProfile_eq_zero
#print axioms SIDEExplicitFormula.LiWeil.edgeProfile_hasCompactSupport
#print axioms SIDEExplicitFormula.LiWeil.edgeProfile_bound
#print axioms SIDEExplicitFormula.LiWeil.integrable_cut_pow_cexp
#print axioms SIDEExplicitFormula.LiWeil.edgeTail
#print axioms SIDEExplicitFormula.LiWeil.edgeCut_abs
#print axioms SIDEExplicitFormula.LiWeil.edgeTail_integrable
#print axioms SIDEExplicitFormula.LiWeil.edgeTail_hasDerivAt
#print axioms SIDEExplicitFormula.LiWeil.edgeTail_ibp
#print axioms SIDEExplicitFormula.LiWeil.edgeTail_bound
#print axioms SIDEExplicitFormula.LiWeil.left_edge_bound
#print axioms SIDEExplicitFormula.LiWeil.jumpInd
#print axioms SIDEExplicitFormula.LiWeil.symCut_split
#print axioms SIDEExplicitFormula.LiWeil.wf_neg
#print axioms SIDEExplicitFormula.LiWeil.wf_eq_zero
#print axioms SIDEExplicitFormula.LiWeil.re_ofReal_mul_cexp
#print axioms SIDEExplicitFormula.LiWeil.leftEdge_integrable
#print axioms SIDEExplicitFormula.LiWeil.symPair_bound
#print axioms SIDEExplicitFormula.LiWeil.symMember_transform_norm_le
#print axioms SIDEExplicitFormula.LiWeil.exchange_of_bound
#print axioms SIDEExplicitFormula.LiWeil.liLimitExchangeSym_holds
#print axioms SIDEExplicitFormula.LiWeil.li_identity_sym

#print SIDEExplicitFormula.LiWeil.symCut
#print SIDEExplicitFormula.LiWeil.symMember
#print SIDEExplicitFormula.LiWeil.LiLimitExchangeSym
#print SIDEExplicitFormula.LiWeil.conjEquiv
#print SIDEExplicitFormula.LiWeil.SymPairBound
#print SIDEExplicitFormula.LiWeil.qf
#print SIDEExplicitFormula.LiWeil.qf1
#print SIDEExplicitFormula.LiWeil.qf2
#print SIDEExplicitFormula.LiWeil.wf
#print SIDEExplicitFormula.LiWeil.wf1
#print SIDEExplicitFormula.LiWeil.wf2
#print SIDEExplicitFormula.LiWeil.edgeProfile
#print SIDEExplicitFormula.LiWeil.edgeTail
#print SIDEExplicitFormula.LiWeil.jumpInd
#check @SIDEExplicitFormula.LiWeil.symPair_bound
#check @SIDEExplicitFormula.LiWeil.liLimitExchangeSym_holds
#check @SIDEExplicitFormula.LiWeil.li_identity_sym
