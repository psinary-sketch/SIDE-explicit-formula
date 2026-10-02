import SIDEExplicitFormula.Schema.Detector
import SIDEExplicitFormula.Schema.Epstein
import SIDEExplicitFormula.Schema.SaltCheckEpstein

/-!
# Axiom audit -- the Epstein negative control (act b590, ruling (R200)(4))

Run `lake env lean AxiomCheckEpstein.lean` (once the modules are built) to reproduce the `#print axioms` output for every
declaration of Schema/Detector.lean, Schema/Epstein.lean and Schema/SaltCheckEpstein.lean and for the terminals they consume
by name, the `#check` of the named statements, and the `#print` of each definition (the salt-check by print). Each is
expected to reduce to the standard base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The
compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.half_pos'
#print axioms SIDEExplicitFormula.Schema.half_lt_one'
#print axioms SIDEExplicitFormula.Schema.baseWidth
#print axioms SIDEExplicitFormula.Schema.baseWidth_pos
#print axioms SIDEExplicitFormula.Schema.detectorBase
#print axioms SIDEExplicitFormula.Schema.base_nonzero_at_width
#print axioms SIDEExplicitFormula.Schema.detector
#print axioms SIDEExplicitFormula.Schema.not_h2_sign_cfg_of_offline
#print axioms SIDEExplicitFormula.Schema.rhoE
#print axioms SIDEExplicitFormula.Schema.rhoE_re_ne_half
#print axioms SIDEExplicitFormula.Schema.EpsteinPremises
#print axioms SIDEExplicitFormula.Schema.epsteinConfig
#print axioms SIDEExplicitFormula.Schema.epstein_not_h2_sign_cfg
#print axioms SIDEExplicitFormula.Schema.epstein_detector
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toyCarrier
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toy_strip
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toy_reflect_mem
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toy_finite
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toyZ
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.log_three_gt_one
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toy_count
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toyRhs
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.toy_premises
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.epstein_hypotheses_satisfiable
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.emptyZ
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.empty_count
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.emptyRhs
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.empty_premises
#print axioms SIDEExplicitFormula.Schema.SaltCheckEpstein.membership_load_bearing

#print axioms SIDEExplicitFormula.Schema.h2_sign_cfg_iff_target
#print axioms SIDEExplicitFormula.Schema.zeroSide_eventually_neg_cfg
#print axioms SIDEExplicitFormula.B321.dominant_exists
#print axioms SIDEExplicitFormula.B321.base_nonzero_at
#print axioms SIDEExplicitFormula.B321.kWindow_classK
#print axioms SIDEExplicitFormula.B321.pwWindow_support

#check @SIDEExplicitFormula.Schema.detector
#check @SIDEExplicitFormula.Schema.not_h2_sign_cfg_of_offline
#check @SIDEExplicitFormula.Schema.epstein_not_h2_sign_cfg
#check @SIDEExplicitFormula.Schema.epstein_detector
#check @SIDEExplicitFormula.Schema.SaltCheckEpstein.epstein_hypotheses_satisfiable
#check @SIDEExplicitFormula.Schema.SaltCheckEpstein.membership_load_bearing

#print SIDEExplicitFormula.Schema.baseWidth
#print SIDEExplicitFormula.Schema.detectorBase
#print SIDEExplicitFormula.Schema.rhoE
#print SIDEExplicitFormula.Schema.EpsteinPremises
#print SIDEExplicitFormula.Schema.epsteinConfig
