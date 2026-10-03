import SIDEExplicitFormula.KeiperSign
import SIDEExplicitFormula.SaltCheckKeiperSign

/-!
# Axiom audit -- act b602, ruling (R212)

Run `lake env lean AxiomCheckKeiperSign.lean` (once the modules are built) to reproduce the `#print axioms` output for every declaration of
SIDEExplicitFormula/KeiperSign.lean and SIDEExplicitFormula/SaltCheckKeiperSign.lean and for the terminals they consume by name, the `#check` of every salt-check theorem and of the named
statements, and the `#print` of each Prop. Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`) or less, with no `sorryAx`. The compiler`s output is the verdict, not this comment.
-/

#print axioms SIDEExplicitFormula.KeiperSign.liCoeff_one_pos_iff
#print axioms SIDEExplicitFormula.KeiperSign.log_sixteen
#print axioms SIDEExplicitFormula.KeiperSign.eulerMascheroniSeq_fifteen
#print axioms SIDEExplicitFormula.KeiperSign.gamma_gt_seq_fifteen
#print axioms SIDEExplicitFormula.KeiperSign.log_pi_le_pi_div_e
#print axioms SIDEExplicitFormula.KeiperSign.pi_div_e_lt
#print axioms SIDEExplicitFormula.KeiperSign.log_four_pi_lt
#print axioms SIDEExplicitFormula.KeiperSign.threshold_lt_gamma
#print axioms SIDEExplicitFormula.KeiperSign.liCoeff_one_pos
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.log_pi_ge
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.e_div_pi_lt
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.log_four_pi_gt
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.coarse_lower_insufficient
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.liCoeff_one_lt_tenth
#print axioms SIDEExplicitFormula.KeiperSign.SaltCheck.liCoeff_one_pos_holds

#print axioms SIDEExplicitFormula.Keiper.liCoeff_one_keiper
#print axioms Real.eulerMascheroniSeq_lt_eulerMascheroniConstant
#print axioms Real.log_two_lt_d9
#print axioms Real.pi_lt_d4
#print axioms Real.exp_one_gt_d9
#print axioms Real.log_le_sub_one_of_pos
#print axioms Real.one_sub_inv_le_log_of_pos
#print axioms Real.pi_gt_d4
#print axioms Real.exp_one_lt_d9
#print axioms Real.log_two_gt_d9
#print axioms Real.eulerMascheroniConstant_lt_two_thirds

#check @SIDEExplicitFormula.KeiperSign.liCoeff_one_pos_iff
#check @SIDEExplicitFormula.KeiperSign.eulerMascheroniSeq_fifteen
#check @SIDEExplicitFormula.KeiperSign.gamma_gt_seq_fifteen
#check @SIDEExplicitFormula.KeiperSign.log_four_pi_lt
#check @SIDEExplicitFormula.KeiperSign.threshold_lt_gamma
#check @SIDEExplicitFormula.KeiperSign.liCoeff_one_pos
#check @SIDEExplicitFormula.KeiperSign.SaltCheck.coarse_lower_insufficient
#check @SIDEExplicitFormula.KeiperSign.SaltCheck.liCoeff_one_lt_tenth
#check @SIDEExplicitFormula.KeiperSign.SaltCheck.liCoeff_one_pos_holds

