/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/HalfScaleControl.lean
THIS PROGRAMME'S WORK (act b757, ruling (R367)(7), at the control) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ARITHMETIC SIDE AT THE CONTROL. For the Epstein zeta function of `x² + xy + 6y²` there is a test function in classK at which the
arithmetic side of its explicit formula, pole term less prime-power side plus archimedean term, has negative real part
(`zq_arith_side_re_neg`). It is `wide_detector` (HalfScale.lean) at the control's configuration `zqZeroConfig`, with its point off the
line (`zq_offline_zero`, OffZero/SP4.lean :32, the zero located near height 16.29), its local count (`zq_count_instance`, EF/Main.lean
:194) and its explicit formula (`zq_explicit_formula_instance`, EF/Main.lean :198), each a compiled theorem binding no premise. The
statement is about this function's own explicit formula and names its side; nothing here is a statement about the zeros of any other
function, and nothing here proves RH or GRH.
-/
import SIDEExplicitFormula.Schema.Wide.HalfScale
import SIDEExplicitFormula.Schema.ZQ.EF.Main
import SIDEExplicitFormula.Schema.ZQ.OffZero.SP4

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- **THE ARITHMETIC SIDE AT THE CONTROL**: there is a test function `k` in classK at which the arithmetic side of the control's
explicit formula, `poleTerm k - primeTermQ cQ k + archTermQ k`, has negative real part. -/
theorem zq_arith_side_re_neg :
    ∃ k : ℝ → ℂ, B321.classK k ∧
      (B321.poleTerm k - primeTermQ (fun n => cQ n) k + archTermQ k).re < 0 := by
  obtain ⟨ρ₀, h₀, hoff⟩ := OffZero.zq_offline_zero
  obtain ⟨A₀, hc⟩ := EF.zq_count_instance
  obtain ⟨k, hk, hneg⟩ := Wide.wide_detector zqZeroConfig hc ρ₀ h₀ hoff
  refine ⟨k, hk, ?_⟩
  obtain ⟨he, hcd, hs, -⟩ := hk
  rw [← EF.zq_explicit_formula_instance k hcd hs he]
  exact hneg

open scoped ComplexOrder in
/-- **WEIL POSITIVITY ON classK FAILS AT THE CONTROL, ON THE ARITHMETIC SIDE OF ITS EXPLICIT FORMULA**: it is not the case that
`0 ≤ poleTerm k - primeTermQ cQ k + archTermQ k` for every test function `k` in classK. This is the failure, at the control, of the
inequality that for zeta is Weil positivity on classK (`B321.h2_sign`, H2Sign.lean): the same expression, with `primeTermQ cQ` and
`archTermQ` where `primeSum` and `archTerm` stand, in the order of `ℂ` in which `h2_sign` is written (`ComplexOrder`, opened for this
theorem alone). It is `zq_arith_side_re_neg` read in that order through `Complex.le_def`, and binds no hypothesis. It is a statement
about the explicit formula of the Epstein zeta function of `x² + xy + 6y²` and about no other function; it says nothing about zeta. -/
theorem zq_weil_positivity_fails :
    ¬ ∀ k : ℝ → ℂ, B321.classK k →
      0 ≤ B321.poleTerm k - primeTermQ (fun n => cQ n) k + archTermQ k := by
  intro h
  obtain ⟨k, hk, hneg⟩ := zq_arith_side_re_neg
  have h0 := (Complex.le_def.mp (h k hk)).1
  rw [Complex.zero_re] at h0
  exact absurd h0 (not_le.mpr hneg)

end ZQ
end Schema
end SIDEExplicitFormula
