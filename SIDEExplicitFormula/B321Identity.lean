/-
SIDE-explicit-formula -- SIDEExplicitFormula/B321Identity.lean
THIS PROGRAMME'S WORK (act b509, ruling (R118)(4), (R104)'s act 3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

b321's four-channel identity  Z = P - PR + A  (relay `tools/b321_window.py`, `channels`), stated for
the zeros of zeta in this kernel's own objects and DERIVED from the vendored `EF_lit_zetaZeroConfig`
as its even case. The four channels are written in the kernel's objects (`paperFT`, `gammaOf`,
`EF.gammaBracket`, `vonMangoldt`); the prime channel is written in b321's EVEN form
`2 * k (log n)`, which is where the evenness hypothesis is used. The normalization constant between
EF_lit's form and b321's is the definition `b321Norm`, carried in the statement and not absorbed.
-/
import Zeta23.WeilEF.Main

open Complex MeasureTheory
open scoped Real ArithmeticFunction

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- b321's `Z`: the zero side, over the canonical zeta zero configuration, with multiplicity. -/
def zeroSide (k : ℝ → ℂ) : ℂ :=
  ∑' ρ : Zeta23.zetaZeroConfig.carrier,
    (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

/-- b321's `P`: the pole term, `h(i/2) + h(-i/2)`. -/
def poleTerm (k : ℝ → ℂ) : ℂ :=
  Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2)

/-- b321's `PR`, in its even form: `SUM_n Lambda(n) n^{-1/2} * 2 k(log n)`. -/
def primeSum (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n))

/-- b321's `A`: `(1/2pi) INT h(r) [Re psi(1/4 + i r/2) - log pi] dr`. -/
def archTerm (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

/-- The normalization constant between EF_lit's form and b321's, as a definition. -/
def b321Norm : ℂ := 1

/-- **b321's identity, derived.** For every even `k ∈ C_c²(ℝ)`, `Z = b321Norm * (P - PR + A)`. -/
theorem b321_identity (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    (he : ∀ x : ℝ, k (-x) = k x) :
    zeroSide k = b321Norm * (poleTerm k - primeSum k + archTerm k) := by
  obtain ⟨-, h⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hs
  have hp : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (k (Real.log n) + k (-Real.log n)))
      = fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (2 * k (Real.log n)) := by
    funext n
    rw [he, two_mul]
  unfold zeroSide
  rw [h]
  unfold Zeta23.EF.literatureRHS poleTerm primeSum archTerm b321Norm
  rw [hp]
  ring

end B321
end SIDEExplicitFormula
