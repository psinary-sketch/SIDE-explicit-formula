import SIDEExplicitFormula.H2Bridge

/-!
# Axiom audit -- the bridge in its trivial direction (W-ORD-H2-BRIDGE)

Run `lake env lean AxiomCheckBridge.lean` to reproduce the `#print axioms` output for the bridge of act b532
(ruling (R142)(4)): `balance_lemma` (SIDE-kernel's `balance_theorem`, ported), `ch_imp_rh`, `rh_imp_ch`, `ch_iff_rh`
(the Route 3 premise is RH restated), `ch_imp_config`, `ch_imp_h2_sign` (the bridge) and `h2_sign_imp_ch_iff` (its
converse is f4's target). Each is expected to reduce to the standard base (`propext`, `Classical.choice`,
`Quot.sound`); the compiler's output is the verdict, not this comment. The `#check` lines show the converse and the
premise elaborating as Props. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.balance_lemma
#print axioms SIDEExplicitFormula.B321.ch_imp_rh
#print axioms SIDEExplicitFormula.B321.rh_imp_ch
#print axioms SIDEExplicitFormula.B321.ch_iff_rh
#print axioms SIDEExplicitFormula.B321.ch_imp_config
#print axioms SIDEExplicitFormula.B321.ch_imp_h2_sign
#print axioms SIDEExplicitFormula.B321.h2_sign_imp_ch_iff

#check @SIDEExplicitFormula.B321.h2_sign_imp_ch
#check @SIDEExplicitFormula.B321.conservationHypothesis
#print SIDEExplicitFormula.B321.conservationHypothesis
#print SIDEExplicitFormula.B321.h2_sign_imp_ch
