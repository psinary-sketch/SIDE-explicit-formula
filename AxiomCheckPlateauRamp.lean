import SIDEExplicitFormula.Schema.PlateauRamp
import SIDEExplicitFormula.Schema.SaltCheckPlateauRamp

/-!
# Axiom audit -- act b602, ruling (R212)

Run `lake env lean AxiomCheckPlateauRamp.lean` (once the modules are built) to reproduce the `#print axioms` output for every declaration of
SIDEExplicitFormula/Schema/PlateauRamp.lean and SIDEExplicitFormula/Schema/SaltCheckPlateauRamp.lean and for the terminals they consume by name, the `#check` of every salt-check theorem and of the named
statements, and the `#print` of each Prop. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.PlateauRamp.box
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.conv
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.box_even
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox_even
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.box_hasCompactSupport
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox_hasCompactSupport
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.conv_even
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window_even
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window_hasCompactSupport
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.box_paperFT
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox_paperFT
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.ClosedFormFT
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.WindowInClassK
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.PlateauRampWindow
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window_paperFT_zero
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.ConvStep
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.Smooth4
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.WindowObligations
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.plateauRampWindow_of
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.epstein_ef_at_window
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.box_transform_zero_at_pi
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.box_transform_ne_zero_at_half_pi
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.window_even_compact_at_seven

#print axioms SIDEExplicitFormula.Schema.detector
#print axioms SIDEExplicitFormula.Schema.epstein_not_h2_sign_cfg
#print axioms SIDEExplicitFormula.B321.classK_of_real_even
#print axioms integral_exp_mul_complex
#print axioms HasCompactSupport.convolution

#check @SIDEExplicitFormula.Schema.PlateauRamp.box_paperFT
#check @SIDEExplicitFormula.Schema.PlateauRamp.nbox_paperFT
#check @SIDEExplicitFormula.Schema.PlateauRamp.window_even
#check @SIDEExplicitFormula.Schema.PlateauRamp.window_hasCompactSupport
#check @SIDEExplicitFormula.Schema.PlateauRamp.window_paperFT_zero
#check @SIDEExplicitFormula.Schema.PlateauRamp.plateauRampWindow_of
#check @SIDEExplicitFormula.Schema.PlateauRamp.epstein_ef_at_window
#check @SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.box_transform_zero_at_pi
#check @SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.box_transform_ne_zero_at_half_pi
#check @SIDEExplicitFormula.Schema.PlateauRamp.SaltCheck.window_even_compact_at_seven

#print SIDEExplicitFormula.Schema.PlateauRamp.ClosedFormFT
#print SIDEExplicitFormula.Schema.PlateauRamp.WindowInClassK
#print SIDEExplicitFormula.Schema.PlateauRamp.PlateauRampWindow
#print SIDEExplicitFormula.Schema.PlateauRamp.ConvStep
#print SIDEExplicitFormula.Schema.PlateauRamp.Smooth4
#print SIDEExplicitFormula.Schema.PlateauRamp.WindowObligations
#print SIDEExplicitFormula.Schema.PlateauRamp.window
