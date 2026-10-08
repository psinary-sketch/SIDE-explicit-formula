import SIDEExplicitFormula.Schema.WindowProofs

/-!
# Axiom audit -- the window's two obligations (act b642, ruling (R252)(3)(b))

Run `lake env lean AxiomCheckWindowProofs.lean` (once the module is built) to reproduce the `#print axioms` output for every declaration
of SIDEExplicitFormula/Schema/WindowProofs.lean and the `#check` of the two obligations proved. Each is expected to reduce to the standard
base (`propext`, `Classical.choice`, `Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.Schema.PlateauRamp.box_integrable
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox_integrable
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window_integrable
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.nbox_of_nonpos
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.conv_nbox_eq
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.continuous_intAvg
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.contDiff_primitive
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.contDiff_intAvg
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.window_contDiff
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.smooth4_holds
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.expWt
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.continuous_expWt
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.expWt_add
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.integrable_weighted
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.paperFT_eq_fourier
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.conv_weighted
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.convStep_holds
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.windowObligations_holds
#print axioms SIDEExplicitFormula.Schema.PlateauRamp.plateauRampWindow_holds

#check @SIDEExplicitFormula.Schema.PlateauRamp.convStep_holds
#check @SIDEExplicitFormula.Schema.PlateauRamp.smooth4_holds
#check @SIDEExplicitFormula.Schema.PlateauRamp.windowObligations_holds
