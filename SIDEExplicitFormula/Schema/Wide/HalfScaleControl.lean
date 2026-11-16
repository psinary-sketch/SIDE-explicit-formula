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

end ZQ
end Schema
end SIDEExplicitFormula
