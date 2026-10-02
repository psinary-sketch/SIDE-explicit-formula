import SIDEExplicitFormula.Simplicity
import SIDEExplicitFormula.SaltCheckSimplicity

/-!
# Axiom audit -- the title's clause as a Prop and its salt-check (act b596, ruling (R206)(4)(b))

Run `lake env lean AxiomCheckSimplicity.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of SIDEExplicitFormula/Simplicity.lean and SIDEExplicitFormula/SaltCheckSimplicity.lean and for the terminals they
consume by name, the `#check` of the named statements, and the `#print` of each definition. Each is expected to reduce to the
standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict,
not this comment.
-/

#print axioms SIDEExplicitFormula.Simplicity.allSimple
#print axioms SIDEExplicitFormula.Simplicity.simplicity
#print axioms SIDEExplicitFormula.Simplicity.simplicity_iff
#print axioms SIDEExplicitFormula.Simplicity.SimpleProportion
#print axioms SIDEExplicitFormula.Simplicity.exceptional_mass_le_third
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.pt
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.pt_reflect
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toyZ
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toy_N_le
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toy_count
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toyCfg
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.toy_online
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.allSimple_satisfiable
#print axioms SIDEExplicitFormula.Simplicity.SaltCheck.allSimple_not_forced

#print axioms SIDEExplicitFormula.Schema.zetaWeilConfig
#print axioms SIDEExplicitFormula.Schema.h2_sign_cfg
#print axioms SIDEExplicitFormula.Schema.online_imp_h2_sign_cfg
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.log_three_gt_one
#print axioms Zeta23.zetaZeroConfig

#check @SIDEExplicitFormula.Simplicity.simplicity_iff
#check @SIDEExplicitFormula.Simplicity.exceptional_mass_le_third
#check @SIDEExplicitFormula.Simplicity.SaltCheck.allSimple_satisfiable
#check @SIDEExplicitFormula.Simplicity.SaltCheck.allSimple_not_forced

#print SIDEExplicitFormula.Simplicity.allSimple
#print SIDEExplicitFormula.Simplicity.simplicity
#print SIDEExplicitFormula.Simplicity.SimpleProportion
