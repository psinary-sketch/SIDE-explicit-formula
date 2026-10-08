import SIDEExplicitFormula.KeiperIdentities

/-!
# Axiom audit -- Keiper's three identities at every index (act b642, ruling (R252)(3)(a))

Run `lake env lean AxiomCheckKeiperIdentities.lean` (once the module is built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/KeiperIdentities.lean and the `#check` of the three obligations proved. Each is expected to reduce to
the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not
this comment.
-/

#print axioms SIDEExplicitFormula.Keiper.binomBeta
#print axioms SIDEExplicitFormula.Keiper.binomBeta_zero_zero
#print axioms SIDEExplicitFormula.Keiper.binomBeta_top
#print axioms SIDEExplicitFormula.Keiper.binomBeta_succ_zero
#print axioms SIDEExplicitFormula.Keiper.choose_key
#print axioms SIDEExplicitFormula.Keiper.binomBeta_succ_succ
#print axioms SIDEExplicitFormula.Keiper.binomSum_step_algebra
#print axioms SIDEExplicitFormula.Keiper.wInv
#print axioms SIDEExplicitFormula.Keiper.Lj
#print axioms SIDEExplicitFormula.Keiper.binomSum
#print axioms SIDEExplicitFormula.Keiper.differentiable_riemannXi
#print axioms SIDEExplicitFormula.Keiper.xiNe
#print axioms SIDEExplicitFormula.Keiper.isOpen_xiNe
#print axioms SIDEExplicitFormula.Keiper.one_mem_xiNe
#print axioms SIDEExplicitFormula.Keiper.differentiableOn_Lj
#print axioms SIDEExplicitFormula.Keiper.hasDerivAt_wInv
#print axioms SIDEExplicitFormula.Keiper.logDeriv_phi_xi
#print axioms SIDEExplicitFormula.Keiper.iterate_deriv_eventually
#print axioms SIDEExplicitFormula.Keiper.binomialTransform_holds
#print axioms SIDEExplicitFormula.Keiper.differentiableAt_Gammaℝ
#print axioms SIDEExplicitFormula.Keiper.riemannXi_eq_split
#print axioms SIDEExplicitFormula.Keiper.logDeriv_riemannXi_eventually
#print axioms SIDEExplicitFormula.Keiper.analyticAt_logDeriv
#print axioms SIDEExplicitFormula.Keiper.analyticAt_logDeriv_riemannZeta₁
#print axioms SIDEExplicitFormula.Keiper.analyticAt_logDeriv_Gammaℝ
#print axioms SIDEExplicitFormula.Keiper.logDerivSplit_holds
#print axioms SIDEExplicitFormula.Keiper.contDiff_riemannZeta₀
#print axioms SIDEExplicitFormula.Keiper.iteratedDeriv_sub_one
#print axioms SIDEExplicitFormula.Keiper.iteratedDeriv_succ_mul_sub_one
#print axioms SIDEExplicitFormula.Keiper.poleCoeff_eq
#print axioms SIDEExplicitFormula.Keiper.stieltjesLog_holds

#check @SIDEExplicitFormula.Keiper.binomialTransform_holds
#check @SIDEExplicitFormula.Keiper.logDerivSplit_holds
#check @SIDEExplicitFormula.Keiper.stieltjesLog_holds
