/-
SIDE-explicit-formula -- SIDEExplicitFormula/Registers.lean
THIS PROGRAMME'S WORK (act b512, ruling (R121)(5), the register-equivalence read) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

The forms of h2 that are STATABLE in this kernel's own objects, each as a `Prop`, and the ordered
implications among them as `Prop`s -- STATED, NOT PROVED -- so that a row reading STATABLE is a
statement the compiler has accepted. The one theorem here is a specialisation that needs no lemma
beyond the definitions: `h2_sign` implies the cell form of any pole-annihilated family inside
`classK`. Every implication that needs a lemma is left as a `Prop` and proved nowhere.
-/
import SIDEExplicitFormula.H2Sign
import Zeta23.Statement

open Complex
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- RH, as Mathlib states it. -/
def rh_form : Prop := RiemannHypothesis

/-- Li's coefficient for the zeta zero configuration, the zeros paired with their conjugates as
`2 Re (1 - (1 - 1/rho)^n)` over the upper half. `tsum` carries Lean's convention: an unsummable
family sums to `0`, and summability is not proved here. -/
def liCoeff (n : ℕ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ Zeta23.zetaZeroConfig.carrier ∧ 0 < ρ.im},
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) * (2 * (1 - (1 - 1 / (ρ : ℂ)) ^ n).re)

/-- Li's criterion, single-channel: `λ_n ≥ 0` for every `n ≥ 1`. -/
def li_form : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n

/-- A family of windows, indexed by width, is admissible when every member is in `classK` with its
pole term annihilated -- the ladder's construction. -/
def admissible (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop :=
  ∀ a ∈ W, classK (F a) ∧ poleTerm (F a) = 0

/-- The cell form: `m(a) = A - PR ≥ 0` at every width of the family. -/
def cell_form (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop :=
  ∀ a ∈ W, 0 ≤ archTerm (F a) - primeSum (F a)

/-- The one compiled implication: a specialisation, no lemma beyond the definitions. -/
theorem h2_sign_imp_cell (F : ℝ → ℝ → ℂ) (W : Set ℝ) (hF : admissible F W) :
    h2_sign → cell_form F W := by
  intro h a ha
  have hk := h (F a) (hF a ha).1
  have e : poleTerm (F a) - primeSum (F a) + archTerm (F a) = archTerm (F a) - primeSum (F a) := by
    rw [(hF a ha).2]; ring
  rw [e] at hk
  exact hk

/-! ### The ordered implications, STATED and not proved. -/

def rh_imp_h2 : Prop := rh_form → h2_sign
def h2_imp_rh : Prop := h2_sign → rh_form
def rh_imp_li : Prop := rh_form → li_form
def li_imp_rh : Prop := li_form → rh_form
def h2_imp_li : Prop := h2_sign → li_form
def li_imp_h2 : Prop := li_form → h2_sign
def cell_imp_h2 (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop := admissible F W → cell_form F W → h2_sign
def cell_imp_rh (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop := admissible F W → cell_form F W → rh_form
def rh_imp_cell (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop := admissible F W → rh_form → cell_form F W
def cell_imp_li (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop := admissible F W → cell_form F W → li_form
def li_imp_cell (F : ℝ → ℝ → ℂ) (W : Set ℝ) : Prop := admissible F W → li_form → cell_form F W

end B321
end SIDEExplicitFormula
