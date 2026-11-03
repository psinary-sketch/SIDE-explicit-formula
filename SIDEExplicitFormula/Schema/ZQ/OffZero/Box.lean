/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Box.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3), relay data/b737_offlinezero_plan.txt (d) S1) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S1, THE BOX. Box A of the plan with rational corners: the open square `(x0, x1) ×ℂ (y0, y1)` of half-side `1/10` about b725's numerically
located `off0`, bounded, its closure the closed square. Nothing here evaluates `zqFn` or locates any zero.
-/
import Mathlib.Analysis.Complex.ReImTopology

open Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- Box A's corners, rational: `[0.85326, 1.05326] × [16.190216, 16.390216]`. -/
def x0 : ℝ := 85326 / 100000
def x1 : ℝ := 105326 / 100000
def y0 : ℝ := 16190216 / 1000000
def y1 : ℝ := 16390216 / 1000000

theorem x0_lt_x1 : x0 < x1 := by norm_num [x0, x1]

theorem y0_lt_y1 : y0 < y1 := by norm_num [y0, y1]

/-- **S1, the box**: `U = (x0, x1) ×ℂ (y0, y1)`. -/
def boxA : Set ℂ := Ioo x0 x1 ×ℂ Ioo y0 y1

theorem boxA_isBounded : Bornology.IsBounded boxA :=
  (Metric.isBounded_Ioo x0 x1).reProdIm (Metric.isBounded_Ioo y0 y1)

theorem closure_boxA : closure boxA = Icc x0 x1 ×ℂ Icc y0 y1 := by
  rw [boxA, closure_reProdIm, closure_Ioo x0_lt_x1.ne, closure_Ioo y0_lt_y1.ne]

theorem mem_closure_boxA {z : ℂ} (hz : z ∈ closure boxA) :
    x0 ≤ z.re ∧ z.re ≤ x1 ∧ y0 ≤ z.im ∧ z.im ≤ y1 := by
  rw [closure_boxA, Complex.mem_reProdIm] at hz
  exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
