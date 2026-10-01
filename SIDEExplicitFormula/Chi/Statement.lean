/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/Statement.lean
THIS PROGRAMME'S WORK (act b567, ruling (R177)(6); W-ORD-GRH-WEIL, act three) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FRONTIER MOVED TO STATEMENT: THE EXPLICIT FORMULA FOR `χ`, STATED. Zeta23's `EF.EF_lit` (ExplicitFormula.lean :97)
asks, for every `k ∈ C_c²(ℝ)`, that the zero sum `Σ_ρ m_ρ h(γ_ρ)` (`h = paperFT k`, `γ_ρ = gammaOf ρ`) converge absolutely
and equal `literatureRHS k`. Its χ-analogue, for primitive `χ ≠ 1` of modulus `N`, over the nontrivial zeros of Mathlib's
`LFunction χ` with multiplicity (`chiZeroConfig`, Chi/ZeroConfig.lean :225):
  `Σ_ρ m_ρ h(γ_ρ) = (1/2π) ∫ h(r) [log(N/π) + Re ψ(1/4 + a/2 + ir/2)] dr − Σ_n Λ(n) n^{−1/2} (χ(n) k(log n) + conj χ(n) k(−log n))`
with `a = parity χ` -- the Γ term `archTerm_chi` and the prime term `primeSum_chi` of GRHWeil.lean (:70, :61), unchanged;
no pole term, `LFunction χ` being entire for `χ ≠ 1`. The archimedean bracket by parity is printed below
(`gammaBracket_chi_of_even`, `gammaBracket_chi_of_not_even`).

`EF_lit_chi` IS STATED AND NOT PROVED: it is HELD at its proof. Its ζ-original is the conclusion of Zeta23's whole
WeilEF arc (VerticalLine, Contour, FullLine, ZeroSumLimit), whose first ζ-specific input below Statement is the growth of ζ in
vertical strips (RvM/ZetaGrowth.lean, consuming `riemannZeta0`, `Zeta0EqZeta` and `ZetaBnd_aux1b`); the χ-analogues of those
three are now compiled (Chi/ZetaBounds.lean, Chi/ZetaBoundsStrip.lean), and the χ-analogue of ZetaGrowth is not.

Nothing here proves GRH, RH, the explicit formula for `χ`, or any statement about the zeros of `LFunction χ`.
-/
import SIDEExplicitFormula.Chi.ZeroConfig

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The literature right side of the explicit formula for `χ`: the Γ term by `χ`'s parity minus the prime term; no pole
term for `χ ≠ 1`. At `N = 1`, `a = 0` and with the pole terms added it is Zeta23's `EF.literatureRHS`. -/
def literatureRHS_chi (χ : DirichletCharacter ℂ N) (k : ℝ → ℂ) : ℂ :=
  archTerm_chi χ k - primeSum_chi χ k

/-- **EF_lit FOR `χ` -- STATED, HELD AT ITS PROOF.** For every `k ∈ C_c²(ℝ)`, the zero sum over the nontrivial zeros of
`LFunction χ` with multiplicity is absolutely summable and equals `literatureRHS_chi χ k`. -/
def EF_lit_chi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : (chiZeroConfig χ hχ h1).carrier =>
        ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) ∧
      ∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)
        = literatureRHS_chi χ k

omit [NeZero N] in
/-- The archimedean bracket for an EVEN character: `log(N/π) + Re ψ(1/4 + ir/2)` (the ζ-bracket's digamma argument). -/
theorem gammaBracket_chi_of_even {χ : DirichletCharacter ℂ N} (he : χ.Even) (r : ℝ) :
    gammaBracket_chi χ r = Real.log (N / Real.pi) + (Complex.digamma (1 / 4 + I * r / 2)).re := by
  classical
  unfold gammaBracket_chi parity
  simp [he]

omit [NeZero N] in
/-- The archimedean bracket for an ODD character: `log(N/π) + Re ψ(3/4 + ir/2)`. -/
theorem gammaBracket_chi_of_not_even {χ : DirichletCharacter ℂ N} (he : ¬ χ.Even) (r : ℝ) :
    gammaBracket_chi χ r = Real.log (N / Real.pi) + (Complex.digamma (3 / 4 + I * r / 2)).re := by
  classical
  unfold gammaBracket_chi parity
  simp only [he, ↓reduceIte, Nat.cast_one]
  norm_num

end GRHWeil
end SIDEExplicitFormula
