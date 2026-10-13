/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperFinite.lean
THIS PROGRAMME'S WORK (act b665, ruling (R275)(2)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE KEIPER FINITE-n EQUALITY, IN THE KERNEL'S TAYLOR COEFFICIENTS (relay data/b665_keiper_statement.txt, section (I)):

* `keiperTaylor_holds : KeiperTaylor` -- for every `n`, Bulka's `n`-th Taylor coefficient of the logarithmic derivative of
  `ξ(1/(1 − z))` at 0 is `keiperSum n` (b601 stated it, `KeiperTaylor`, and proved it at `n = 0`, `keiperTaylor_zero`).
* `liCoeff_succ_eq_keiperSum n : LiCoeff (n + 1) = (keiperSum n).re` -- the programme's Li coefficient at `n + 1`, a sum over
  the genuine zeros of ζ, equals the real part of `Σ_{k ≤ n} C(n + 1, k + 1) keiperA k`, with
  `keiperA k = (-1)^k + zetaLogCoeff k + gammaRLogCoeff k`, the Taylor coefficients at 1 of `1/s`, of riemannZeta₁'s and of
  Γℝ's logarithmic derivatives (Keiper.lean).

The statement is in those coefficients and in no constant beyond them: the Stieltjes constants enter `zetaLogCoeff` through
`stieltjesLog_holds` (KeiperIdentities.lean) and are the kernel's `stieltjes` (Keiper.lean, by derivative); the ζ-values that
`gammaRLogCoeff` carries are `GammaRZetaValues`, not used here. Nothing here is a statement about the zeros of ζ, proves RH, or
gives the sign of any `λ_n`.
-/
import SIDEExplicitFormula.KeiperIdentities

noncomputable section

namespace SIDEExplicitFormula
namespace Keiper

/-- **Keiper's Taylor identity at every index**: `taylorCoeff riemannXi n = keiperSum n` for every `n`. -/
theorem keiperTaylor_holds : KeiperTaylor := fun n => by
  rw [binomialTransform_holds n, keiperSum]
  exact Finset.sum_congr rfl fun k _ => by rw [logDerivSplit_holds k]

/-- **The finite-n equality**: the programme's Li coefficient at `n + 1` is the real part of `keiperSum n`. -/
theorem liCoeff_succ_eq_keiperSum (n : ℕ) : LiWeil.LiCoeff (n + 1) = (keiperSum n).re := by
  rw [LiCriterionBridge.li_coeff_eq_taylorCoeff n, keiperTaylor_holds n]

end Keiper
end SIDEExplicitFormula
