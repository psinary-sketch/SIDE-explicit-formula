/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Carrier.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3), relay data/b737_offlinezero_plan.txt (d) S4) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S4, A ZERO IN THE CLOSED BOX IS A POINT OF THE CARRIER OFF THE LINE. Every point of the closure has `Im ≥ y0 > 0`, so it is not `0`, `1` or
`−(n + 1)`, and `Re ≥ x0 > 1/2`; with `zqFn z = 0` it is a member of `LambdaQZeros zqFn`, the carrier of `zqZeroConfig` (Zeros.lean :319).
The zero itself is a hypothesis here; nothing here locates one.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Box
import SIDEExplicitFormula.Schema.ZQ.Zeros

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **S4, `carrier_of_box`**. -/
theorem carrier_of_box {z : ℂ} (hz : z ∈ closure boxA) (h0 : zqFn z = 0) :
    z ∈ zqZeroConfig.carrier ∧ z.re ≠ 1 / 2 := by
  obtain ⟨hx0, _, hy0, _⟩ := mem_closure_boxA hz
  have him : z.im ≠ 0 := (lt_of_lt_of_le (by norm_num [y0] : (0 : ℝ) < y0) hy0).ne'
  refine ⟨?_, ?_⟩
  · show z ≠ 0 ∧ z ≠ 1 ∧ (∀ n : ℕ, z ≠ -((n : ℂ) + 1)) ∧ zqFn z = 0
    refine ⟨?_, ?_, ?_, h0⟩
    · intro h
      apply him
      rw [h, Complex.zero_im]
    · intro h
      apply him
      rw [h, Complex.one_im]
    · intro n h
      apply him
      rw [h]
      simp
  · intro h
    rw [h] at hx0
    norm_num [x0] at hx0

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
