/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/VerticalLine.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED. HELD: THIS FILE DOES NOT
COMPILE AND IS NOT ON main.

THE χ-ANALOGUE OF Zeta23/WeilEF/VerticalLine.lean, ATTEMPTED AT ITS ARCHIMEDEAN STEP. Zeta23's Γ-side line shift
(`gamma_line_shift`, :659) consumes `norm_logDeriv_Gammaℝ_le` (:626): `‖Γℝ'/Γℝ(σ + it)‖ ≪ log(2 + |t|)` on
`1/2 ≤ σ ≤ 3/2`, from `digamma_growth_strip` (:261) on `1/4 ≤ Re w ≤ 1`. For χ the Γ factor is `gammaFactor χ`:
`Γℝ(s)` for even χ, `Γℝ(s + 1)` for odd χ. The even case is Zeta23's bound; the odd case needs it at `σ + 1 ∈ [3/2, 5/2]`,
i.e. digamma growth on `3/4 ≤ Re w ≤ 5/4`, which Zeta23 does not state. THE HOLD: the odd case below does not compile.
-/
import SIDEExplicitFormula.Chi.XiLogDeriv
import Zeta23.WeilEF.VerticalLine

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- `logDeriv (fun s => f (s + 1)) z = logDeriv f (z + 1)`. -/
theorem logDeriv_comp_add_one (f : ℂ → ℂ) (z : ℂ) :
    logDeriv (fun s => f (s + 1)) z = logDeriv f (z + 1) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

/-- **ATTEMPTED -- THE ARCHIMEDEAN STEP OF THE χ-ANALOGUE OF `norm_logDeriv_Gammaℝ_le`.** Growth of
`gammaFactor χ'/gammaFactor χ` on `1/2 ≤ σ ≤ 3/2`. The even case is Zeta23's bound; the odd case asks Zeta23's bound at
`σ + 1`, outside its range `[1/2, 3/2]` -- the step `σ + 1 ≤ 3/2` fails for `σ > 1/2`. -/
theorem norm_logDeriv_gammaFactor_le (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖logDeriv (gammaFactor χ) (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hG⟩ := Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le
  refine ⟨C, hC, fun σ t h1 h2 => ?_⟩
  rcases χ.even_or_odd with he | ho
  · have e : gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [e]
    exact hG σ t h1 h2
  · have e : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext ho.gammaFactor_def
    rw [e, logDeriv_comp_add_one]
    have hs : (σ : ℂ) + t * I + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [hs]
    exact hG (σ + 1) t (by linarith) (by linarith)

end GRHWeil
end SIDEExplicitFormula
