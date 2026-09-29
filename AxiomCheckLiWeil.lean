import SIDEExplicitFormula.LiWeil

/-!
# Axiom audit -- the Li-Weil bridge, staged (act b560, ruling (R170) and its (4) amendment)

Run `lake env lean AxiomCheckLiWeil.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of `SIDEExplicitFormula/LiWeil.lean`, Stages A-D. Each is expected to reduce to the standard base
(`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. `blTransform` and `LiLimitExchange` are
`Prop` definitions -- stated, not proved. The compiler's output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.LiWeil.ne_one_of_mem
#print axioms SIDEExplicitFormula.LiWeil.conj_mem
#print axioms SIDEExplicitFormula.LiWeil.mult_conj
#print axioms SIDEExplicitFormula.LiWeil.liTerm
#print axioms SIDEExplicitFormula.LiWeil.pairTerm
#print axioms SIDEExplicitFormula.LiWeil.liTerm_conj
#print axioms SIDEExplicitFormula.LiWeil.pairTerm_eq
#print axioms SIDEExplicitFormula.LiWeil.pairTerm_im
#print axioms SIDEExplicitFormula.LiWeil.pairTerm_re
#print axioms SIDEExplicitFormula.LiWeil.norm_sub_one_of_re_half
#print axioms SIDEExplicitFormula.LiWeil.norm_one_sub_inv_of_re_half
#print axioms SIDEExplicitFormula.LiWeil.liTerm_re_nonneg_of_re_half
#print axioms SIDEExplicitFormula.LiWeil.pairTerm_re_nonneg_of_re_half
#print axioms SIDEExplicitFormula.LiWeil.rem_bound
#print axioms SIDEExplicitFormula.LiWeil.liTerm_re_abs_le
#print axioms SIDEExplicitFormula.LiWeil.liConst
#print axioms SIDEExplicitFormula.LiWeil.liConst_nonneg
#print axioms SIDEExplicitFormula.LiWeil.pairTerm_norm_le
#print axioms SIDEExplicitFormula.LiWeil.pair_summable
#print axioms SIDEExplicitFormula.LiWeil.LiCoeff
#print axioms SIDEExplicitFormula.LiWeil.LiCoeff_eq
#print axioms SIDEExplicitFormula.LiWeil.liTerm_re_summable
#print axioms SIDEExplicitFormula.LiWeil.rh_imp_li_nonneg
#print axioms SIDEExplicitFormula.LiWeil.blPoly
#print axioms SIDEExplicitFormula.LiWeil.blSmooth
#print axioms SIDEExplicitFormula.LiWeil.blTest
#print axioms SIDEExplicitFormula.LiWeil.blTransform
#print axioms SIDEExplicitFormula.LiWeil.truncMember
#print axioms SIDEExplicitFormula.LiWeil.blPoly_contDiff
#print axioms SIDEExplicitFormula.LiWeil.blSmooth_contDiff
#print axioms SIDEExplicitFormula.LiWeil.truncMember_classEF
#print axioms SIDEExplicitFormula.LiWeil.truncMember_eq
#print axioms SIDEExplicitFormula.LiWeil.truncMember_EF
#print axioms SIDEExplicitFormula.LiWeil.LiLimitExchange
#print axioms SIDEExplicitFormula.LiWeil.li_identity_of_exchange

#check @SIDEExplicitFormula.LiWeil.conj_mem
#check @SIDEExplicitFormula.LiWeil.mult_conj
#check @SIDEExplicitFormula.LiWeil.pairTerm_eq
#check @SIDEExplicitFormula.LiWeil.liTerm_re_nonneg_of_re_half
#check @SIDEExplicitFormula.LiWeil.pairTerm_norm_le
#check @SIDEExplicitFormula.LiWeil.pair_summable
#check @SIDEExplicitFormula.LiWeil.LiCoeff_eq
#check @SIDEExplicitFormula.LiWeil.rh_imp_li_nonneg
#check @SIDEExplicitFormula.LiWeil.truncMember_classEF
#check @SIDEExplicitFormula.LiWeil.truncMember_EF
#check @SIDEExplicitFormula.LiWeil.li_identity_of_exchange
#print SIDEExplicitFormula.LiWeil.LiCoeff
#print SIDEExplicitFormula.LiWeil.liConst
#print SIDEExplicitFormula.LiWeil.blTransform
#print SIDEExplicitFormula.LiWeil.LiLimitExchange
#print RiemannHypothesis
