/-
SIDE-explicit-formula -- SIDEExplicitFormula/TransversalityWidth.lean
THIS PROGRAMME'S WORK (act b654, ruling (R264)(4)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

A definition and nothing else: the width at a zero `ρ`, THE_UNCONDITIONAL_SURROUND §6a's object (PLACE-papers
phase1.5/proofs/THE_UNCONDITIONAL_SURROUND.md :151, :153), bound to the kernel's one `ξ`, `LiCriterion.riemannXi`
(Vendored/Bulka/Lc/LiCriterion/Basic.lean:1252, vendored at b566), so that W-ORD-CLOSE-PAIR-BENCH has a kernel name.
No theorem about it is stated here.
-/
import Lc.LiCriterion.Basic

noncomputable section

namespace SIDEExplicitFormula

/-- **The transversality width at `ρ`: a definition.** The real number `‖ξ′(ρ)‖`, with `ξ` the kernel's `LiCriterion.riemannXi` and
`ξ′` Mathlib's `deriv`. The object of THE_UNCONDITIONAL_SURROUND §6a. -/
def transversalityWidth (ρ : ℂ) : ℝ := ‖deriv LiCriterion.riemannXi ρ‖

end SIDEExplicitFormula
