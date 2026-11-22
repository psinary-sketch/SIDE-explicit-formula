import SIDEExplicitFormula.Window.KFast
import SIDEExplicitFormula.Window.Instance
import SIDEExplicitFormula.Window.ArchData
import SIDEExplicitFormula.Window.ArchBlocks
import SIDEExplicitFormula.GaussArchQSteps

/-!
# The archimedean term at the window: Gauss's integral, and k(0) as data

`archTermQ_windowK` reads `gaussArchQ` (GaussArchQSteps.lean) at the window, which is in classK (Instance.lean `windowK_classK`):
the archimedean term is `2 k(0) (log(√23/(2π)) − γ)` plus twice Gauss's integral over `t > 0`. `k0_ok` evaluates the strided sum at
`n = 1` by the kernel in four blocks of at most `2 ^ 12` places (ArchBlocks.lean), each checked apart, and reads their sum equal to
`k0Num` (ArchData.lean; both written by relay tools/b766_k0data.py); with KFast.lean's
`windowK_log_eq_Kt` at `n = 1`, `k(0) = k0Num / (80640 * 10 ^ 34)`. (R376)(4)(d) L9, in part: Gauss's integral at the window in the
B-spline basis, and its sums as the certificate's combination, are not proved here.
-/

open MeasureTheory

namespace SIDEExplicitFormula
namespace Window

/-- **The archimedean term at the window by Gauss's integral**: `gaussArchQ` at `windowK`, which is in classK. -/
theorem archTermQ_windowK :
    Schema.archTermQ windowK =
      2 * windowK 0 * ((Real.log (Real.sqrt 23 / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) +
        2 * ∫ t in Set.Ioi (0 : ℝ),
          ((Real.exp (-t) : ℂ) * windowK 0 - (Real.exp (-t / 2) : ℂ) * windowK t) / (1 - (Real.exp (-t) : ℂ)) := by
  have h := B321.GaussArchQSteps.gaussArchQ
  unfold B321.GaussArchQ at h
  exact h windowK windowK_classK

/-- A halving sum cut in two: its first `a` places and its last `b`. -/
theorem sumDC_split (f : ℕ → ℤ) (d₁ d₂ d lo a b : ℕ) (ha : a ≤ 2 ^ d₁) (hb : b ≤ 2 ^ d₂) (hab : a + b ≤ 2 ^ d) :
    sumDC f lo (a + b) d = sumDC f lo a d₁ + sumDC f (lo + a) b d₂ := by
  rw [sumDC_eq f d lo (a + b) hab, sumDC_eq f d₁ lo a ha, sumDC_eq f d₂ (lo + a) b hb, Finset.sum_range_add]
  simp only [Nat.add_assoc]

set_option maxHeartbeats 0 in
/-- The strided sum at `n = 1` over its block 0, by the kernel's evaluation. -/
theorem k0_blk0 : sumDC (fun m => aGet m * gk 1 m) 16 4096 12 = k0Blk0 := by decide +kernel

set_option maxHeartbeats 0 in
/-- The strided sum at `n = 1` over its block 1, by the kernel's evaluation. -/
theorem k0_blk1 : sumDC (fun m => aGet m * gk 1 m) (16 + 4096) 4096 12 = k0Blk1 := by decide +kernel

set_option maxHeartbeats 0 in
/-- The strided sum at `n = 1` over its block 2, by the kernel's evaluation. -/
theorem k0_blk2 : sumDC (fun m => aGet m * gk 1 m) (16 + 4096 + 4096) 4096 12 = k0Blk2 := by decide +kernel

set_option maxHeartbeats 0 in
/-- The strided sum at `n = 1` over its block 3, by the kernel's evaluation. -/
theorem k0_blk3 : sumDC (fun m => aGet m * gk 1 m) (16 + 4096 + 4096 + 4096) 4077 12 = k0Blk3 := by decide +kernel

/-- The strided sum at `n = 1` is `k0Num`: its four blocks, each checked apart, summed. -/
theorem k0_ok : KtFast 1 = k0Num := by
  have hlen : mtop 1 + 1 - 16 = 4096 + (4096 + (4096 + 4077)) := by decide +kernel
  unfold KtFast
  rw [hlen, sumDC_split _ 12 14 14 16 4096 (4096 + (4096 + 4077)) (by norm_num) (by norm_num) (by norm_num),
    sumDC_split _ 12 14 14 (16 + 4096) 4096 (4096 + 4077) (by norm_num) (by norm_num) (by norm_num),
    sumDC_split _ 12 12 14 (16 + 4096 + 4096) 4096 4077 (by norm_num) (by norm_num) (by norm_num),
    k0_blk0, k0_blk1, k0_blk2, k0_blk3]
  decide +kernel

/-- **The window's autocorrelation at 0** is `k0Num / (80640 * 10 ^ 34)`. -/
theorem windowK_zero : windowK 0 = (((k0Num : ℝ) / (80640 * 10 ^ 34) : ℝ) : ℂ) := by
  have h := windowK_log_eq_Kt 1 (by norm_num)
  rw [Kt_eq_fast 1 (by norm_num), k0_ok] at h
  simpa using h

/-- **The archimedean term at the window**, with `k(0)` as data. -/
theorem archTermQ_windowK_k0 :
    Schema.archTermQ windowK =
      2 * (((k0Num : ℝ) / (80640 * 10 ^ 34) : ℝ) : ℂ) *
          ((Real.log (Real.sqrt 23 / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) +
        2 * ∫ t in Set.Ioi (0 : ℝ),
          ((Real.exp (-t) : ℂ) * (((k0Num : ℝ) / (80640 * 10 ^ 34) : ℝ) : ℂ) - (Real.exp (-t / 2) : ℂ) * windowK t) /
            (1 - (Real.exp (-t) : ℂ)) := by
  rw [archTermQ_windowK, windowK_zero]

end Window
end SIDEExplicitFormula
