import SIDEExplicitFormula.RegisterDepth

/-!
# Axiom audit -- the register depth (act b538, ruling (R148))

Run `lake env lean AxiomCheckRegisterDepth.lean` to reproduce the `#print axioms` output for the theorems of
`SIDEExplicitFormula/RegisterDepth.lean`. Each is expected to reduce to the standard base or fewer; the compiler's
output is the verdict, not this comment. The `#check` lines print the statements read; `#print mellin` prints
Mathlib's definition at this pin. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.RegisterDepth.not_register1
#print axioms SIDEExplicitFormula.RegisterDepth.silence_universal_restated
#print axioms SIDEExplicitFormula.RegisterDepth.one_le_evenKernel_zero
#print axioms SIDEExplicitFormula.RegisterDepth.rpow_le_evenKernel_zero
#print axioms SIDEExplicitFormula.RegisterDepth.mellin_Phi_eq_zero_of_re_le_one
#print axioms SIDEExplicitFormula.RegisterDepth.lv_h2_false_on_strip
#print axioms SIDEExplicitFormula.RegisterDepth.lvh2_corrected_iff
#print axioms SIDEExplicitFormula.RegisterDepth.register3_of_one_lt_re
#print axioms SIDEExplicitFormula.RegisterDepth.zeta_zeros_countable
#print axioms SIDEExplicitFormula.RegisterDepth.xi_zero_re_countable
#print axioms SIDEExplicitFormula.RegisterDepth.register5_output_holds

#print mellin
#check @SIDEExplicitFormula.RegisterDepth.not_register1
#check @SIDEExplicitFormula.RegisterDepth.silence_universal_restated
#check @SIDEExplicitFormula.RegisterDepth.one_le_evenKernel_zero
#check @SIDEExplicitFormula.RegisterDepth.rpow_le_evenKernel_zero
#check @SIDEExplicitFormula.RegisterDepth.mellin_Phi_eq_zero_of_re_le_one
#check @SIDEExplicitFormula.RegisterDepth.lv_h2_false_on_strip
#check @SIDEExplicitFormula.RegisterDepth.lvh2_corrected_iff
#check @SIDEExplicitFormula.RegisterDepth.register3_of_one_lt_re
#check @SIDEExplicitFormula.RegisterDepth.zeta_zeros_countable
#check @SIDEExplicitFormula.RegisterDepth.xi_zero_re_countable
#check @SIDEExplicitFormula.RegisterDepth.register5_output_holds
