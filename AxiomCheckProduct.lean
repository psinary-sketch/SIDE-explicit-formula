import SIDEExplicitFormula.Product
import SIDEExplicitFormula.SaltCheckProduct

/-!
# Axiom audit -- the product lemma and its salt-check (act b600, ruling (R210)(4))

Run `lake env lean AxiomCheckProduct.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Product.lean and SIDEExplicitFormula/SaltCheckProduct.lean and for the terminals they
consume by name, the `#check` of the named statements, and the `#print` of each definition. Each is expected to reduce to the
standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict,
not this comment.
-/

#print axioms SIDEExplicitFormula.Product.reflect_reflect
#print axioms SIDEExplicitFormula.Product.reflect_mem_iff
#print axioms SIDEExplicitFormula.Product.onMult
#print axioms SIDEExplicitFormula.Product.onMult_reflect
#print axioms SIDEExplicitFormula.Product.sumMult
#print axioms SIDEExplicitFormula.Product.sumZ
#print axioms SIDEExplicitFormula.Product.sumZ_N
#print axioms SIDEExplicitFormula.Product.sumZ_count
#print axioms SIDEExplicitFormula.Product.zeroSide_summable
#print axioms SIDEExplicitFormula.Product.sum_ef
#print axioms SIDEExplicitFormula.Product.sum_target_iff
#print axioms SIDEExplicitFormula.Product.sum
#print axioms SIDEExplicitFormula.Product.sum_carrier
#print axioms SIDEExplicitFormula.Product.sum_mult
#print axioms SIDEExplicitFormula.Product.sum_rhs
#print axioms SIDEExplicitFormula.Product.sum_target
#print axioms SIDEExplicitFormula.Product.ProductLemma
#print axioms SIDEExplicitFormula.Product.h2_sign_cfg_sum_iff_targets
#print axioms SIDEExplicitFormula.Product.productLemma_holds
#print axioms SIDEExplicitFormula.Product.SaltCheck.onCfg
#print axioms SIDEExplicitFormula.Product.SaltCheck.onCfg_h2
#print axioms SIDEExplicitFormula.Product.SaltCheck.offCfg
#print axioms SIDEExplicitFormula.Product.SaltCheck.offCfg_not_h2
#print axioms SIDEExplicitFormula.Product.SaltCheck.product_satisfiable
#print axioms SIDEExplicitFormula.Product.SaltCheck.product_part_load_bearing
#print axioms SIDEExplicitFormula.Product.SaltCheck.product_sum_not_forced

#print axioms SIDEExplicitFormula.Schema.h2_sign_cfg_iff_target
#print axioms SIDEExplicitFormula.Schema.online_imp_h2_sign_cfg
#print axioms SIDEExplicitFormula.Schema.epsteinConfig
#print axioms Zeta23.WeilEF.EF_zero_sum_summable_gen

#check @SIDEExplicitFormula.Product.sum_ef
#check @SIDEExplicitFormula.Product.sumZ_count
#check @SIDEExplicitFormula.Product.h2_sign_cfg_sum_iff_targets
#check @SIDEExplicitFormula.Product.productLemma_holds
#check @SIDEExplicitFormula.Product.SaltCheck.product_satisfiable
#check @SIDEExplicitFormula.Product.SaltCheck.product_part_load_bearing
#check @SIDEExplicitFormula.Product.SaltCheck.product_sum_not_forced

#print SIDEExplicitFormula.Product.sum
#print SIDEExplicitFormula.Product.ProductLemma
