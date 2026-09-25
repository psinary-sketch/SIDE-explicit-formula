import SIDEExplicitFormula.PairTerm

/-!
# Axiom audit -- (f)(ii), the pair's term, as far as it derives

Run `lake env lean AxiomCheckPair.lean` to reproduce the `#print axioms` output for (f)(ii) of W-ORD-WEIL-CONVERSE
(ruling (R139)(3), act b529): Component 1 `pairTwo_factored` (the exact algebra) and `pairTwo_near_far` (near and far
named); Component 2 `nearInt_ge`, `realizedGrowth_eq`, `realizedGrowth_ge_one`, `nearPair_eq`, `pair_near_sign`;
Component 3 `pair_bound` under the named hypothesis `farSmall`; with the lemmas they rest on. Each is expected to reduce
to the standard base (`propext`, `Classical.choice`, `Quot.sound`); the compiler's output is the verdict, not this comment.
The `#check` line shows `farSmall` elaborating as a `Prop`; the `#print` lines show `c` and `eps'` from their definitions.
The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.pairTwo_factored
#print axioms SIDEExplicitFormula.B321.pairTwo_near_far
#print axioms SIDEExplicitFormula.B321.nearInt_ge
#print axioms SIDEExplicitFormula.B321.realizedGrowth_eq
#print axioms SIDEExplicitFormula.B321.realizedGrowth_ge_one
#print axioms SIDEExplicitFormula.B321.nearPair_eq
#print axioms SIDEExplicitFormula.B321.pair_near_sign
#print axioms SIDEExplicitFormula.B321.pair_bound
#print axioms SIDEExplicitFormula.B321.pair_algebra
#print axioms SIDEExplicitFormula.B321.windowSlope_bound
#print axioms SIDEExplicitFormula.B321.kWin_FT
#print axioms SIDEExplicitFormula.B321.cosWinC_FT
#print axioms SIDEExplicitFormula.B321.cosWinC_FT_near_far
#print axioms SIDEExplicitFormula.B321.phiC_FT_imag
#print axioms SIDEExplicitFormula.B321.phiC_FT_neg
#print axioms SIDEExplicitFormula.B321.farFT_conj
#print axioms SIDEExplicitFormula.B321.paperFT_ofReal_conj
#print axioms SIDEExplicitFormula.B321.gammaOf_rhoZero
#print axioms SIDEExplicitFormula.B321.gammaOf_reflect_rhoZero

#check @SIDEExplicitFormula.B321.farSmall
#print SIDEExplicitFormula.B321.pairConst
#print SIDEExplicitFormula.B321.pairEps
#print SIDEExplicitFormula.B321.farSmall
#print SIDEExplicitFormula.B321.nearInt
#print SIDEExplicitFormula.B321.farFT
#print SIDEExplicitFormula.B321.nearPair
#print SIDEExplicitFormula.B321.pairTwo
#print SIDEExplicitFormula.B321.rhoZero
