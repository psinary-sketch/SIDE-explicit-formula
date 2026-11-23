import SIDEExplicitFormula.Window.LogData
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# L10: the enclosures of the prime form

`logPrime_bounds` and `logPrime_width`: each prime up to 16,390 has its logarithm between the table's two rationals, an
interval within `2 / 10 ^ 22` (L10a). `gamma_bounds`: Euler's constant between two rationals within `2 / 10 ^ 3`, by Mathlib's
two sequences at 500 and the table's ends at `501 = 3 * 167` and `500 = 2 ^ 2 * 5 ^ 3` (L10b). `logPi_bounds`: `log π` between
two rationals within `2 / 10 ^ 3`, by `log π = log (22 / 7) + log (7 π / 22)`, π's six-digit bounds and
`1 - 1 / y ≤ log y ≤ y - 1` (L10c). The four ends are relay data/b767_logdata.txt's.
-/

namespace SIDEExplicitFormula.Window

/-- **L10a: each prime up to 16,390 has its logarithm between the table's two rationals.** -/
theorem logPrime_bounds : ∀ p ∈ lpPrimes,
    ((lpTree.lo p : ℚ) : ℝ) ≤ Real.log p ∧ Real.log p ≤ ((lpTree.hi p : ℚ) : ℝ) :=
  fun p hp => LPTree.bounds lpTree lp_all p (lp_keys p hp)

/-- **L10a: each interval within `2 / 10 ^ 22`.** -/
theorem logPrime_width : ∀ p ∈ lpPrimes, lpTree.hi p - lpTree.lo p ≤ lpW :=
  fun p hp => LPTree.width lpTree lp_all p (lp_keys p hp)

/-- The harmonic number by recursion, for the kernel. -/
def hq : ℕ → ℚ
  | 0 => 0
  | n + 1 => hq n + ((n + 1 : ℕ) : ℚ)⁻¹

theorem harmonic_eq_hq : ∀ n : ℕ, harmonic n = hq n
  | 0 => by simp [hq]
  | n + 1 => by simp only [harmonic_succ, harmonic_eq_hq n, hq]

/-- Euler's constant's lower end. -/
def gLo : ℚ := 36013583 / 62500000

/-- Euler's constant's upper end. -/
def gHi : ℚ := 144553833 / 250000000

/-- **L10b: Euler's constant between `gLo` and `gHi`.** -/
theorem gamma_bounds : (gLo : ℝ) < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < gHi := by
  have k501 : lpTree.facOK 16391 [(3, 1), (167, 1)] = true := by decide +kernel
  have k500 : lpTree.facOK 16391 [(2, 2), (5, 3)] = true := by decide +kernel
  have h501 := (LPTree.log_facProd lpTree lp_all 16391 _ k501).2
  have h500 := (LPTree.log_facProd lpTree lp_all 16391 _ k500).1
  have p501 : facProd [(3, 1), (167, 1)] = 501 := by decide
  have p500 : facProd [(2, 2), (5, 3)] = 500 := by decide
  rw [p501] at h501
  rw [p500] at h500
  push_cast at h501 h500
  have qlo : gLo ≤ hq 500 - lpTree.facHi [(3, 1), (167, 1)] := by decide +kernel
  have qhi : hq 500 - lpTree.facLo [(2, 2), (5, 3)] ≤ gHi := by decide +kernel
  have rlo := (Rat.cast_le (K := ℝ)).mpr qlo
  have rhi := (Rat.cast_le (K := ℝ)).mpr qhi
  rw [Rat.cast_sub] at rlo rhi
  have s1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 500
  have s2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 500
  have e1 : Real.eulerMascheroniSeq 500 = ((hq 500 : ℚ) : ℝ) - Real.log 501 := by
    rw [Real.eulerMascheroniSeq, harmonic_eq_hq]
    norm_num
  have e2 : Real.eulerMascheroniSeq' 500 = ((hq 500 : ℚ) : ℝ) - Real.log 500 := by
    rw [Real.eulerMascheroniSeq', harmonic_eq_hq]
    norm_num
  rw [e1] at s1
  rw [e2] at s2
  constructor
  · linarith
  · linarith

/-- **L10b: Euler's constant's interval within `2 / 10 ^ 3`.** -/
theorem gamma_width : gHi - gLo ≤ 2 / 10 ^ 3 := by
  unfold gLo gHi
  norm_num

/-- `log π`'s lower end. -/
def pLo : ℚ := 228945919 / 200000000

/-- `log π`'s upper end. -/
def pHi : ℚ := 1144730079 / 1000000000

/-- **L10c: `log π` between `pLo` and `pHi`.** -/
theorem logPi_bounds : (pLo : ℝ) < Real.log Real.pi ∧ Real.log Real.pi < pHi := by
  have k : ∀ p ∈ [2, 7, 11], (lpTree.find p).isSome = true := by decide +kernel
  have b2 := LPTree.bounds lpTree lp_all 2 (k 2 (by simp))
  have b7 := LPTree.bounds lpTree lp_all 7 (k 7 (by simp))
  have b11 := LPTree.bounds lpTree lp_all 11 (k 11 (by simp))
  push_cast at b2 b7 b11
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  norm_num at h1 h2
  have h1' : (392699 / 125000 : ℝ) ≤ Real.pi := h1.le
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hy0 : 0 < 7 * Real.pi / 22 := by positivity
  have hlogpi : Real.log Real.pi = Real.log 2 + Real.log 11 - Real.log 7 + Real.log (7 * Real.pi / 22) := by
    have e : Real.pi = 2 * 11 / 7 * (7 * Real.pi / 22) := by ring
    conv_lhs => rw [e]
    rw [Real.log_mul (x := 2 * 11 / 7) (by norm_num) hy0.ne', Real.log_div (x := 2 * 11) (y := 7) (by norm_num) (by norm_num),
      Real.log_mul (x := 2) (y := 11) (by norm_num) (by norm_num)]
  have hu := Real.log_le_sub_one_of_pos hy0
  have hl := Real.one_sub_inv_le_log_of_pos hy0
  have hinv : (7 * Real.pi / 22)⁻¹ ≤ 22 / (7 * (392699 / 125000)) := by
    rw [inv_div]
    gcongr
  have qlo : pLo < lpTree.lo 2 + lpTree.lo 11 - lpTree.hi 7 + (1 - 22 / (7 * (392699 / 125000))) := by
    decide +kernel
  have qhi : lpTree.hi 2 + lpTree.hi 11 - lpTree.lo 7 + (7 * (3141593 / 1000000) / 22 - 1) < pHi := by
    decide +kernel
  have rlo := (Rat.cast_lt (K := ℝ)).mpr qlo
  have rhi := (Rat.cast_lt (K := ℝ)).mpr qhi
  push_cast at rlo rhi
  constructor
  · linarith
  · linarith

/-- **L10c: `log π`'s interval within `2 / 10 ^ 3`.** -/
theorem logPi_width : pHi - pLo ≤ 2 / 10 ^ 3 := by
  unfold pLo pHi
  norm_num

end SIDEExplicitFormula.Window
