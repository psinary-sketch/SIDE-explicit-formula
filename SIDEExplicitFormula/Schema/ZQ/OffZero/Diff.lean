/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Diff.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3), relay data/b737_offlinezero_plan.txt (d) S2) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S2, `zqFn` DIFFERENTIABLE ON BOX A AND CONTINUOUS ON ITS CLOSURE. The closure lies above the real axis (`y0 ≤ Im z`), so it misses `1`, the one
point where `zqFn_holomorphic` (Continuation.lean :147) leaves `zqFn` unbounded. Nothing here evaluates `zqFn` or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Box
import SIDEExplicitFormula.Schema.ZQ.Continuation

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

theorem ne_one_of_mem_closure_boxA {z : ℂ} (hz : z ∈ closure boxA) : z ≠ 1 := by
  intro h
  have hy := (mem_closure_boxA hz).2.2.1
  rw [h, Complex.one_im] at hy
  norm_num [y0] at hy

/-- **S2**: `zqFn` is `DiffContOnCl` on box A. -/
theorem zqFn_diffContOnCl_boxA : DiffContOnCl ℂ zqFn boxA :=
  DifferentiableOn.diffContOnCl (zqFn_holomorphic.mono fun _ hz => ne_one_of_mem_closure_boxA hz)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
