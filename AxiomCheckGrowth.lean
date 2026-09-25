import SIDEExplicitFormula.GrowthBound

/-!
# Axiom audit -- (d), the growth bound

Run `lake env lean AxiomCheckGrowth.lean` to reproduce the `#print axioms` output for (d) of W-ORD-WEIL-CONVERSE
(ruling (R126)(3), act b517): `paperFT_growth`, the bound `‖paperFT h z‖ ≤ (∫ ‖h‖) * exp (L * |Im z|)` for `h`
integrable with support in `[-L, L]`, and `paperFT_growth_at`, its form at `gammaOf rho`. Both are expected to reduce
to the standard base (`propext`, `Classical.choice`, `Quot.sound`); the compiler's output is the verdict, not this
comment. The AxiomCheck files of earlier acts are left as they stand.
-/

#print axioms SIDEExplicitFormula.B321.paperFT_growth
#print axioms SIDEExplicitFormula.B321.paperFT_growth_at
