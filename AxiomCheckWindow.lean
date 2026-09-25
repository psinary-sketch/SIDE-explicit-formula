import SIDEExplicitFormula.TwoPropertyWindow

/-!
# Axiom audit -- (f)(i) on variant (B), the two-property window

Run `lake env lean AxiomCheckWindow.lean` to reproduce the `#print axioms` output for (f)(i) of W-ORD-WEIL-CONVERSE
(ruling (R133)(5), act b524; the plateau made concrete at b527, ruling (R137)(2)): `kWin_classK` (i), `paperFT_window_zero` (ii), `paperFT_window` (iii), with the
plateau's properties and the lemmas they rest on. Each is expected to reduce to the standard base (`propext`,
`Classical.choice`, `Quot.sound`); the compiler's output is the verdict, not this comment. The `#check` and `#print`
lines show the hypothesis of (f)(ii) elaborating as a `Prop` and `realizedGrowth` defined by the integral. The
AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.kWin_classK
#print axioms SIDEExplicitFormula.B321.paperFT_window_zero
#print axioms SIDEExplicitFormula.B321.paperFT_window
#print axioms SIDEExplicitFormula.B321.paperFT_second_order
#print axioms SIDEExplicitFormula.B321.ibp_step
#print axioms SIDEExplicitFormula.B321.weilTest_ofReal_even
#print axioms SIDEExplicitFormula.B321.plateau_contDiff
#print axioms SIDEExplicitFormula.B321.plateau_even
#print axioms SIDEExplicitFormula.B321.plateau_hasCompactSupport
#print axioms SIDEExplicitFormula.B321.plateau_eq_one
#print axioms SIDEExplicitFormula.B321.plateau_apply_abs

#check @SIDEExplicitFormula.B321.f_pair_hypothesis
#print SIDEExplicitFormula.B321.realizedGrowth
#print SIDEExplicitFormula.B321.plateau
