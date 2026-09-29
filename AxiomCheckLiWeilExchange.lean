import SIDEExplicitFormula.LiWeilExchange

/-!
# Axiom audit -- the Li-Weil bridge at the limit exchange (act b561, ruling (R171))

Run `lake env lean AxiomCheckLiWeilExchange.lean` (once the modules are built) to reproduce the `#print axioms` output
for every declaration of `SIDEExplicitFormula/LiWeilExchange.lean`: (D1) `blTransform_holds` and its lemmas, (D2)
`truncMember_transform_tendsto`. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`. The compiler's output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.LiWeil.norm_pow_mul_cexp
#print axioms SIDEExplicitFormula.LiWeil.integrableOn_pow_mul_cexp
#print axioms SIDEExplicitFormula.LiWeil.integral_pow_mul_cexp
#print axioms SIDEExplicitFormula.LiWeil.blPoly_neg_cast
#print axioms SIDEExplicitFormula.LiWeil.binomial_li
#print axioms SIDEExplicitFormula.LiWeil.blTest_integrand
#print axioms SIDEExplicitFormula.LiWeil.blTransform_holds
#print axioms SIDEExplicitFormula.LiWeil.integrable_blTest_integrand
#print axioms SIDEExplicitFormula.LiWeil.truncMember_transform_tendsto

#check @SIDEExplicitFormula.LiWeil.integral_pow_mul_cexp
#check @SIDEExplicitFormula.LiWeil.binomial_li
#check @SIDEExplicitFormula.LiWeil.blTransform_holds
#check @SIDEExplicitFormula.LiWeil.integrable_blTest_integrand
#check @SIDEExplicitFormula.LiWeil.truncMember_transform_tendsto
#print SIDEExplicitFormula.LiWeil.blTransform
#print SIDEExplicitFormula.LiWeil.LiLimitExchange
