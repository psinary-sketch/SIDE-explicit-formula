/-
SIDE-explicit-formula -- SIDEExplicitFormula/PlattRung.lean
THIS PROGRAMME'S WORK (act b626, ruling (R236)(5) and the author's answer before b626's seal; W-ORD-PLATT-RUNG) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE HEIGHT RUNG AND ITS PAIR. `rh_upto T` -- every nontrivial zero of Mathlib's `riemannZeta` (`Zeta23.IsNontrivialZero`:
ζ ρ = 0, 0 < Re ρ < 1) with |Im ρ| ≤ T lies on the critical line. `forall_rh_upto_iff_rh` -- the height pair: the rung at every
height is Mathlib's `RiemannHypothesis`, through the vendored `LiCriterion.rh_equiv_mathlib`. The pair is DEFINITIONAL: each zero
has a finite height, so it carries no analytic content and joins the rung to `RiemannHypothesis` by the quantifier alone.
`plattTrudgianT` -- the height of the numerical verification of Dave Platt and Tim Trudgian, "The Riemann hypothesis is true up
to 3·10¹²", Bulletin of the London Mathematical Society 53 (3), 792-797 (2021), DOI 10.1112/blms.12460 -- title, journal, volume
and pages as Crossref's record of the publisher's (Wiley's) deposit gives them, read at b626 when the publisher's page refused the
read (HTTP 403); the height in the title's own words, confirmed by the authors' arXiv abstract (2004.09765): "all zeroes β + iγ
of the Riemann zeta-function with 0 < γ ≤ 3·10¹² have β = 1/2" (relay data/b626_citation_reads.txt).
`PlattTrudgianHeight T` -- that verification as a NAMED PREMISE (T1-lit): `rh_upto T`, the negative ordinates taken by the
conjugate symmetry of ζ's zeros, which this module does not prove. `rh_upto_platt` -- the rung at the published
height, INTERFACES on that structure alone: the numerical tradition's result enters this kernel as a premise, not as a theorem of
it, and the rung's weight is the premise's and nothing else.
NOT the support pair of DetectionRegion.lean: `h2_sign_upto L₀` bounds a window's support, not a zero's height, and no
instantiation of it follows from this premise. NOTHING HERE PROVES RH OR LOCATES ANY ZERO BEYOND WHAT THE PREMISE NAMES.
-/
import Zeta23.Statement
import Lc.LiCriterion.RHBridge

noncomputable section

namespace SIDEExplicitFormula
namespace PlattRung

/-- **The height rung:** every nontrivial zero of ζ with `|Im ρ| ≤ T` lies on the critical line. -/
def rh_upto (T : ℝ) : Prop :=
  ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2

/-- **The height pair, definitional:** the rung at every height is Mathlib's `RiemannHypothesis` -- each zero has a finite
height, so the pair carries no analytic content; through the vendored `LiCriterion.rh_equiv_mathlib`. -/
theorem forall_rh_upto_iff_rh : (∀ T : ℝ, rh_upto T) ↔ RiemannHypothesis := by
  rw [LiCriterion.rh_equiv_mathlib]
  unfold rh_upto Zeta23.IsNontrivialZero
  constructor
  · intro h s hs hstrip
    exact h |s.im| s ⟨hs, hstrip.1, hstrip.2⟩ le_rfl
  · intro h T ρ hρ _
    exact h ρ hρ.1 ⟨hρ.2.1, hρ.2.2⟩

/-- **The published height** of Platt and Trudgian's verification, `3·10¹²`, as the title in Crossref's record of the publisher's
deposit gives it and the authors' arXiv abstract confirms (relay data/b626_citation_reads.txt). -/
def plattTrudgianT : ℝ := 3 * 10 ^ 12

/-- **THE NAMED PREMISE (T1-lit):** Platt and Trudgian's verification at the height `T` -- every nontrivial zero with
`|Im ρ| ≤ T` on the critical line. A premise of this kernel, not a theorem of it. -/
structure PlattTrudgianHeight (T : ℝ) : Prop where
  verified : rh_upto T

/-- **THE RUNG, AT INTERFACES ON THE PREMISE ALONE:** under Platt and Trudgian's verification, the height rung holds at the
published height. Its weight is the premise's and nothing else. -/
theorem rh_upto_platt (hP : PlattTrudgianHeight plattTrudgianT) : rh_upto plattTrudgianT :=
  hP.verified

end PlattRung
end SIDEExplicitFormula
