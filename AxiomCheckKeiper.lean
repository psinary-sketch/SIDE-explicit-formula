import SIDEExplicitFormula.Keiper
import SIDEExplicitFormula.KeiperBounds
import SIDEExplicitFormula.SaltCheckKeiper

/-!
# Axiom audit -- the Keiper face's two lemmas and their salt-check (act b601, ruling (R211)(4))

Run `lake env lean AxiomCheckKeiper.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Keiper.lean, SIDEExplicitFormula/KeiperBounds.lean and SIDEExplicitFormula/SaltCheckKeiper.lean
and for Mathlib's inputs they consume by name, the `#check` of the named statements, and the `#print` of each Prop. Each is
expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The
compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Keiper.stieltjes
#print axioms SIDEExplicitFormula.Keiper.analyticAt_riemannZeta₀
#print axioms SIDEExplicitFormula.Keiper.stieltjes_zero
#print axioms SIDEExplicitFormula.Keiper.stieltjes_zero_limit
#print axioms SIDEExplicitFormula.Keiper.tendsto_riemannZeta₁_residue
#print axioms SIDEExplicitFormula.Keiper.taylorAt
#print axioms SIDEExplicitFormula.Keiper.xiLogCoeff
#print axioms SIDEExplicitFormula.Keiper.zetaLogCoeff
#print axioms SIDEExplicitFormula.Keiper.gammaRLogCoeff
#print axioms SIDEExplicitFormula.Keiper.keiperA
#print axioms SIDEExplicitFormula.Keiper.keiperSum
#print axioms SIDEExplicitFormula.Keiper.KeiperTaylor
#print axioms SIDEExplicitFormula.Keiper.poleCoeff
#print axioms SIDEExplicitFormula.Keiper.StieltjesLog
#print axioms SIDEExplicitFormula.Keiper.GammaRZetaValues
#print axioms SIDEExplicitFormula.Keiper.KeiperTaylorIdentity
#print axioms SIDEExplicitFormula.Keiper.BinomialTransform
#print axioms SIDEExplicitFormula.Keiper.LogDerivSplit
#print axioms SIDEExplicitFormula.Keiper.KeiperObligations
#print axioms SIDEExplicitFormula.Keiper.keiperTaylorIdentity_of
#print axioms SIDEExplicitFormula.Keiper.hasDerivAt_xi_one
#print axioms SIDEExplicitFormula.Keiper.xi_one
#print axioms SIDEExplicitFormula.Keiper.xiLogCoeff_zero
#print axioms SIDEExplicitFormula.Keiper.taylorCoeff_xi_zero
#print axioms SIDEExplicitFormula.Keiper.binomialTransform_zero
#print axioms SIDEExplicitFormula.Keiper.zetaLogCoeff_zero
#print axioms SIDEExplicitFormula.Keiper.stieltjesLog_zero
#print axioms SIDEExplicitFormula.Keiper.gammaRLogCoeff_zero
#print axioms SIDEExplicitFormula.Keiper.keiperA_zero
#print axioms SIDEExplicitFormula.Keiper.logDerivSplit_zero
#print axioms SIDEExplicitFormula.Keiper.keiperTaylor_zero
#print axioms SIDEExplicitFormula.Keiper.log_four_pi_ofReal
#print axioms SIDEExplicitFormula.Keiper.liCoeff_one_keiper
#print axioms SIDEExplicitFormula.KeiperBounds.InInterval
#print axioms SIDEExplicitFormula.KeiperBounds.stLo
#print axioms SIDEExplicitFormula.KeiperBounds.stHi
#print axioms SIDEExplicitFormula.KeiperBounds.zLo
#print axioms SIDEExplicitFormula.KeiperBounds.zHi
#print axioms SIDEExplicitFormula.KeiperBounds.StieltjesBoundsAt
#print axioms SIDEExplicitFormula.KeiperBounds.ZetaValueBoundsAt
#print axioms SIDEExplicitFormula.KeiperBounds.KeiperBounds
#print axioms SIDEExplicitFormula.KeiperBounds.BoundPremises
#print axioms SIDEExplicitFormula.KeiperBounds.keiperBounds_of
#print axioms SIDEExplicitFormula.KeiperBounds.stieltjes_zero_coarse
#print axioms SIDEExplicitFormula.KeiperBounds.table_refines_coarse
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.gamma_pos
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.log_four_pi_pos
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.keiperTaylor_zero_holds
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.split_needs_inv_s
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.split_needs_zeta
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.split_needs_gammaR
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.bounds_form_satisfiable
#print axioms SIDEExplicitFormula.Keiper.SaltCheck.bounds_form_refutable

#print axioms riemannZeta_residue_one
#print axioms tendsto_riemannZeta_sub_one_div
#print axioms riemannZeta₀
#print axioms differentiable_riemannZeta₀
#print axioms riemannZeta₀_one
#print axioms riemannZeta₁
#print axioms riemannZeta₁_one
#print axioms deriv_riemannZeta₁_one
#print axioms completedRiemannZeta₀_one
#print axioms Complex.hasDerivAt_Gammaℝ_one
#print axioms Real.one_half_lt_eulerMascheroniConstant
#print axioms Real.eulerMascheroniConstant_lt_two_thirds
#print axioms SIDEExplicitFormula.LiCriterionBridge.li_coeff_eq_taylorCoeff

#check @SIDEExplicitFormula.Keiper.stieltjes_zero
#check @SIDEExplicitFormula.Keiper.stieltjes_zero_limit
#check @SIDEExplicitFormula.Keiper.tendsto_riemannZeta₁_residue
#check @SIDEExplicitFormula.Keiper.keiperTaylorIdentity_of
#check @SIDEExplicitFormula.Keiper.keiperTaylor_zero
#check @SIDEExplicitFormula.Keiper.liCoeff_one_keiper
#check @SIDEExplicitFormula.KeiperBounds.keiperBounds_of
#check @SIDEExplicitFormula.KeiperBounds.stieltjes_zero_coarse
#check @SIDEExplicitFormula.Keiper.SaltCheck.split_needs_inv_s
#check @SIDEExplicitFormula.Keiper.SaltCheck.split_needs_zeta
#check @SIDEExplicitFormula.Keiper.SaltCheck.split_needs_gammaR
#check @SIDEExplicitFormula.Keiper.SaltCheck.keiperTaylor_zero_holds
#check @SIDEExplicitFormula.Keiper.SaltCheck.bounds_form_satisfiable
#check @SIDEExplicitFormula.Keiper.SaltCheck.bounds_form_refutable

#print SIDEExplicitFormula.Keiper.KeiperTaylor
#print SIDEExplicitFormula.Keiper.KeiperTaylorIdentity
#print SIDEExplicitFormula.Keiper.KeiperObligations
#print SIDEExplicitFormula.KeiperBounds.KeiperBounds
#print SIDEExplicitFormula.KeiperBounds.BoundPremises
