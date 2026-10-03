import SIDEExplicitFormula.Doubling
import SIDEExplicitFormula.SaltCheckDoubling

/-!
# Axiom audit -- the doubling corollary and its salt-check (act b601, ruling (R211)(3))

Run `lake env lean AxiomCheckDoubling.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Doubling.lean and SIDEExplicitFormula/SaltCheckDoubling.lean and for the terminals they
consume by name, the `#check` of the named statements, and the `#print` of each definition. Each is expected to reduce to the
standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict,
not this comment.
-/

#print axioms SIDEExplicitFormula.Doubling.sum_self_carrier
#print axioms SIDEExplicitFormula.Doubling.sum_self_mult
#print axioms SIDEExplicitFormula.Doubling.doubling_iff
#print axioms SIDEExplicitFormula.Doubling.DoublingCorollary
#print axioms SIDEExplicitFormula.Doubling.doubling_holds
#print axioms SIDEExplicitFormula.Doubling.doubledToy
#print axioms SIDEExplicitFormula.Doubling.doubledToy_pt_mem
#print axioms SIDEExplicitFormula.Doubling.doubledToy_mult_pt
#print axioms SIDEExplicitFormula.Doubling.doubledToy_h2_sign_cfg
#print axioms SIDEExplicitFormula.Doubling.doubledToy_not_allSimple
#print axioms SIDEExplicitFormula.Doubling.PositivityImpliesSimplicity
#print axioms SIDEExplicitFormula.Doubling.positivity_not_imp_simplicity
#print axioms SIDEExplicitFormula.Doubling.SaltCheck.doubling_satisfiable
#print axioms SIDEExplicitFormula.Doubling.SaltCheck.doubling_not_forced
#print axioms SIDEExplicitFormula.Doubling.SaltCheck.positivity_with_simplicity

#print axioms SIDEExplicitFormula.Product.productLemma_holds
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toyCfg
#print axioms SIDEExplicitFormula.Schema.online_imp_h2_sign_cfg

#check @SIDEExplicitFormula.Doubling.sum_self_mult
#check @SIDEExplicitFormula.Doubling.doubling_iff
#check @SIDEExplicitFormula.Doubling.doubling_holds
#check @SIDEExplicitFormula.Doubling.doubledToy_mult_pt
#check @SIDEExplicitFormula.Doubling.doubledToy_h2_sign_cfg
#check @SIDEExplicitFormula.Doubling.doubledToy_not_allSimple
#check @SIDEExplicitFormula.Doubling.positivity_not_imp_simplicity
#check @SIDEExplicitFormula.Doubling.SaltCheck.doubling_satisfiable
#check @SIDEExplicitFormula.Doubling.SaltCheck.doubling_not_forced
#check @SIDEExplicitFormula.Doubling.SaltCheck.positivity_with_simplicity

#print SIDEExplicitFormula.Doubling.DoublingCorollary
#print SIDEExplicitFormula.Doubling.doubledToy
#print SIDEExplicitFormula.Doubling.PositivityImpliesSimplicity
