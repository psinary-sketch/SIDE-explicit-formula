/-
SIDE-explicit-formula -- SIDEExplicitFormula/RHChain.lean
THIS PROGRAMME'S WORK (act b513, ruling (R122)(1)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

RH -> h2_sign, COMPILED along the route b512 read: for `k = weilTest h h` in `classK`, every zero on
the line makes its zero term `m_rho * |h^(gamma)|^2` (`paperFT_weilTest`, `Complex.mul_conj`), so
`zeroSide k >= 0` (`Complex.normSq_nonneg`, `tsum_nonneg`), and `b321_identity` carries the sign to
`poleTerm k - primeSum k + archTerm k`. The chain RH -> h2_sign -> cell form follows in one line.
The converse is STATED and not proved. None of this moves h2: RH is the hypothesis.
-/
import SIDEExplicitFormula.Registers

open Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **RH implies h2_sign.** Under Mathlib's `RiemannHypothesis`, every `k` in `classK` has
`0 <= poleTerm k - primeSum k + archTerm k`. -/
theorem rh_imp_h2_sign : RiemannHypothesis → h2_sign := by
  intro hRH k hk
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  have hid := b321_identity (Zeta23.EF.weilTest h h) hc hs he
  have hflip : poleTerm (Zeta23.EF.weilTest h h) - primeSum (Zeta23.EF.weilTest h h)
      + archTerm (Zeta23.EF.weilTest h h) = zeroSide (Zeta23.EF.weilTest h h) := by
    rw [hid]
    unfold b321Norm
    rw [one_mul]
  rw [hflip]
  unfold zeroSide
  refine tsum_nonneg fun ρ => ?_
  have hz : Zeta23.IsNontrivialZero (ρ : ℂ) := by
    first
      | exact ρ.2
      | exact (show (ρ : ℂ) ∈ ({z | Zeta23.IsNontrivialZero z} : Set ℂ) by
          rw [← Zeta23.zetaZeroConfig_carrier]; exact ρ.2)
  have hre : (ρ : ℂ).re = 1 / 2 := Zeta23.RH_implies_on_line hRH hz
  have him : (Zeta23.gammaOf (ρ : ℂ)).im = 0 := by
    unfold Zeta23.gammaOf
    rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, hre]
    first
      | rw [Complex.div_ofNat_re, Complex.one_re, sub_self, neg_zero]
      | norm_num
  have hcj : conj (Zeta23.gammaOf (ρ : ℂ)) = Zeta23.gammaOf (ρ : ℂ) :=
    Complex.conj_eq_iff_im.mpr him
  have hterm : Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ))
      = ((Complex.normSq (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ))) : ℝ) : ℂ) := by
    rw [Zeta23.EF.paperFT_weilTest hh.continuous hh.continuous hhs hhs, hcj,
      Complex.mul_conj (Zeta23.paperFT h (Zeta23.gammaOf (ρ : ℂ)))]
  have hm : (0 : ℂ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℂ) := by
    first
      | exact Nat.cast_nonneg _
      | (rw [← Complex.ofReal_natCast]; exact Complex.zero_le_real.mpr (Nat.cast_nonneg _))
  have hnn : (0 : ℂ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℂ)
      * Zeta23.paperFT (Zeta23.EF.weilTest h h) (Zeta23.gammaOf (ρ : ℂ)) := by
    rw [hterm]
    exact mul_nonneg hm (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  exact hnn

/-- **The chain, RH -> h2_sign -> cell form**, for any admissible family: `rh_imp_h2_sign` composed
with b512's `h2_sign_imp_cell`. (The name `rh_imp_cell` is b512's `Prop` in `Registers.lean`.) -/
theorem rh_imp_cell_form (F : ℝ → ℝ → ℂ) (W : Set ℝ) (hF : admissible F W) :
    RiemannHypothesis → cell_form F W := fun hRH => h2_sign_imp_cell F W hF (rh_imp_h2_sign hRH)

-- b512`s two `Prop`s on this route are now inhabited (checks, not declarations).
example : rh_imp_h2 := rh_imp_h2_sign
example (F : ℝ → ℝ → ℂ) (W : Set ℝ) : rh_imp_cell F W := by
  intro hF
  exact rh_imp_cell_form F W hF

/-- **The converse, STATED AND NOT PROVED (ruling (R122)(2)).** `h2_sign -> RH` needs a witness
construction: a test function that makes zeroSide negative at an off-line zero -- for an arbitrary
off-line `rho`, a `k` in `classK` concentrated at `rho`'s ordinate whose zero side is negative, so
that `b321_identity` makes `poleTerm k - primeSum k + archTerm k` negative and `h2_sign` fails. The
matched window of (R121)(4) is that construction attempted numerically at Q0's pair; if it exhibits
the violation, its window is the witness this converse would need, stated for an arbitrary
off-line `rho`; if it does not, the construction is harder than a modulated bump. Neither this
statement nor that measurement claims the other's result. -/
def h2_sign_imp_rh : Prop := h2_sign → RiemannHypothesis

-- The converse is b512`s `h2_imp_rh`, by definition.
example : h2_sign_imp_rh = h2_imp_rh := rfl

end B321
end SIDEExplicitFormula
