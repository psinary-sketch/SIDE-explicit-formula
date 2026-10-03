import SIDEExplicitFormula.Schema.Family
import SIDEExplicitFormula.Schema.SaltCheckFamily

/-!
# Axiom audit -- act b603, ruling (R213)

Run `lake env lean AxiomCheckFamily.lean` (once the modules are built) to reproduce the `#print axioms` output for every declaration of
SIDEExplicitFormula/Schema/Family.lean and SIDEExplicitFormula/Schema/SaltCheckFamily.lean and for the terminals they consume by name, the `#check` of
every salt-check theorem and of the named statements, and the `#print` of each Prop. Each is expected to reduce to the standard base
(`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.Family.emptyZ
#print axioms SIDEExplicitFormula.Schema.Family.emptyZ_N
#print axioms SIDEExplicitFormula.Schema.Family.emptyZ_count
#print axioms SIDEExplicitFormula.Schema.Family.emptyCfg
#print axioms SIDEExplicitFormula.Schema.Family.emptyCfg_h2
#print axioms SIDEExplicitFormula.Schema.Family.cfg_ext
#print axioms SIDEExplicitFormula.Schema.Family.onMult_sum
#print axioms SIDEExplicitFormula.Schema.Family.sum_comm
#print axioms SIDEExplicitFormula.Schema.Family.sum_assoc
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum_empty
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum_insert
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum_productLemma
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum_target_iff
#print axioms SIDEExplicitFormula.Schema.Family.finsetSum_rhs
#print axioms SIDEExplicitFormula.Schema.Family.family
#print axioms SIDEExplicitFormula.Schema.Family.mem_family
#print axioms SIDEExplicitFormula.Schema.Family.primitiveCharacter_ne_one
#print axioms SIDEExplicitFormula.Schema.Family.charCfg
#print axioms SIDEExplicitFormula.Schema.Family.charCfg_of_ne
#print axioms SIDEExplicitFormula.Schema.Family.charCfg_target
#print axioms SIDEExplicitFormula.Schema.Family.charCfg_rhs
#print axioms SIDEExplicitFormula.Schema.Family.familyConfig
#print axioms SIDEExplicitFormula.Schema.Family.FamilyTheorem
#print axioms SIDEExplicitFormula.Schema.Family.family_theorem
#print axioms SIDEExplicitFormula.Schema.Family.familyTheorem_holds
#print axioms SIDEExplicitFormula.Schema.Family.familyConfig_arith
#print axioms SIDEExplicitFormula.Schema.Family.gammaBracket_conductor
#print axioms SIDEExplicitFormula.Schema.Family.family_three
#print axioms SIDEExplicitFormula.Schema.Family.family_three_statement
#print axioms SIDEExplicitFormula.Schema.Family.zeta_rhs_pole
#print axioms SIDEExplicitFormula.Schema.Family.TrivialSummandPremise
#print axioms SIDEExplicitFormula.Schema.Family.EulerFactorPremise
#print axioms SIDEExplicitFormula.Schema.Family.DedekindPremises
#print axioms SIDEExplicitFormula.Schema.Family.SaltCheck.finsetSum_satisfiable
#print axioms SIDEExplicitFormula.Schema.Family.SaltCheck.finsetSum_summand_load_bearing
#print axioms SIDEExplicitFormula.Schema.Family.SaltCheck.family_one_empty
#print axioms SIDEExplicitFormula.Schema.Family.SaltCheck.family_one_h2

#print axioms SIDEExplicitFormula.Product.productLemma_holds
#print axioms SIDEExplicitFormula.Schema.h2_sign_cfg_iff_target

#check @SIDEExplicitFormula.Schema.Family.SaltCheck.finsetSum_satisfiable
#check @SIDEExplicitFormula.Schema.Family.SaltCheck.finsetSum_summand_load_bearing
#check @SIDEExplicitFormula.Schema.Family.SaltCheck.family_one_empty
#check @SIDEExplicitFormula.Schema.Family.SaltCheck.family_one_h2
#check @SIDEExplicitFormula.Schema.Family.finsetSum_productLemma
#check @SIDEExplicitFormula.Schema.Family.family_theorem
#check @SIDEExplicitFormula.Schema.Family.family_three
#check @SIDEExplicitFormula.Schema.Family.family_three_statement
#check @SIDEExplicitFormula.Schema.Family.familyConfig_arith
#check @SIDEExplicitFormula.Schema.Family.gammaBracket_conductor
#check @SIDEExplicitFormula.Schema.Family.zeta_rhs_pole

#print SIDEExplicitFormula.Schema.Family.FamilyTheorem
#print SIDEExplicitFormula.Schema.Family.TrivialSummandPremise
#print SIDEExplicitFormula.Schema.Family.EulerFactorPremise
#print SIDEExplicitFormula.Schema.Family.DedekindPremises
