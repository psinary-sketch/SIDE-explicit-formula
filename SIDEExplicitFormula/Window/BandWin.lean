import SIDEExplicitFormula.Window.BandPoly
import SIDEExplicitFormula.Window.WinCheck
import SIDEExplicitFormula.Window.Coeffs

/-!
# L9c3: the band`s blocks, its coefficient of `log n` and its constant`s terms, read at a window of `coeffPad`

Written by relay tools/b768_band_data.py from the kernel`s own files (ArchClosed.lean`s blob 3ec80af752678d30 and Coeffs.lean`s);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The numerators of `Coeffs.lean` after twenty zeros, joined to the right, so that `coeffPad[m + 4] = coeffInt m`. -/
def coeffPad : List ℤ := List.replicate 20 0 ++ (coeffChunk00 ++ (coeffChunk01 ++ (coeffChunk02 ++ (coeffChunk03 ++ (coeffChunk04 ++ (coeffChunk05 ++ (coeffChunk06 ++ (coeffChunk07 ++ (coeffChunk08 ++ (coeffChunk09 ++ (coeffChunk10 ++ (coeffChunk11 ++ (coeffChunk12 ++ (coeffChunk13 ++ (coeffChunk14 ++ (coeffChunk15 ++ (coeffChunk16 ++ (coeffChunk17 ++ (coeffChunk18 ++ (coeffChunk19 ++ (coeffChunk20 ++ (coeffChunk21 ++ (coeffChunk22 ++ (coeffChunk23 ++ (coeffChunk24 ++ (coeffChunk25 ++ (coeffChunk26 ++ (coeffChunk27 ++ (coeffChunk28 ++ (coeffChunk29 ++ (coeffChunk30 ++ (coeffChunk31 ++ (coeffChunk32 ++ (coeffChunk33 ++ (coeffChunk34 ++ (coeffChunk35 ++ (coeffChunk36 ++ (coeffChunk37 ++ (coeffChunk38 ++ (coeffChunk39 ++ (coeffChunk40 ++ (coeffChunk41 ++ (coeffChunk42 ++ (coeffChunk43 ++ (coeffChunk44 ++ (coeffChunk45 ++ (coeffChunk46 ++ (coeffChunk47 ++ (coeffChunk48 ++ (coeffChunk49 ++ (coeffChunk50 ++ (coeffChunk51 ++ (coeffChunk52 ++ (coeffChunk53 ++ (coeffChunk54 ++ (coeffChunk55 ++ (coeffChunk56 ++ (coeffChunk57 ++ (coeffChunk58 ++ (coeffChunk59 ++ (coeffChunk60 ++ (coeffChunk61 ++ (coeffChunk62 ++ coeffChunk63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem coeffPad_eq : coeffPad = List.replicate 20 0 ++ coeffList := by
  unfold coeffPad coeffList
  simp only [List.append_assoc]

/-- The block`s pair: `i, i + bD b - 3`. -/
def bD : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 4
  | 11 => 4
  | 12 => 4
  | 13 => 5
  | 14 => 5
  | 15 => 6
  | _ => 0

/-- The block`s shift: its vector read at `i + bS b`. -/
def bS : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 3
  | 10 => 1
  | 11 => 2
  | 12 => 3
  | 13 => 2
  | 14 => 3
  | 15 => 3
  | _ => 0

/-- The block`s vector: `bVec (bVi b)`. -/
def bVi : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 3
  | 11 => 4
  | 12 => 5
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | _ => 0

theorem band_table (b : ℕ) (hb : b < 16) : bS b ≤ 3 ∧ bS b ≤ bD b ∧ bD b ≤ bS b + 3 ∧ bVi b ≤ 9 := by
  interval_cases b <;> first | decide | (simp only [bS, bD, bVi]; done) | (simp only [bS, bD, bVi]; omega)

/-- The coefficient of `log n` in the band, times `bandDEN` and the square of the numerators` scale, read at the window `w`. -/
def bandW (n : ℕ) (w : List ℤ) : ℤ :=
  bpA 0 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 0 0 * w.getD 3 0)) + bpB 0 (n : ℤ) * (2 * (w.getD 1 0 * w.getD 4 0)) +
  bpA 1 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 1 0 * w.getD 3 0)) + bpB 1 (n : ℤ) * (2 * (w.getD 2 0 * w.getD 4 0)) +
  bpA 2 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 0 0 * w.getD 2 0)) + bpB 2 (n : ℤ) * (2 * (w.getD 1 0 * w.getD 3 0)) +
  bpA 3 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 2 0 * w.getD 3 0)) + bpB 3 (n : ℤ) * (2 * (w.getD 3 0 * w.getD 4 0)) +
  bpA 4 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 1 0 * w.getD 2 0)) + bpB 4 (n : ℤ) * (2 * (w.getD 2 0 * w.getD 3 0)) +
  bpA 5 ((n - 1 : ℕ) : ℤ) * (2 * (w.getD 0 0 * w.getD 1 0)) + bpB 5 (n : ℤ) * (2 * (w.getD 1 0 * w.getD 2 0)) +
  bpA 6 ((n - 1 : ℕ) : ℤ) * (w.getD 3 0 * w.getD 3 0) + bpB 6 (n : ℤ) * (w.getD 4 0 * w.getD 4 0) +
  bpA 7 ((n - 1 : ℕ) : ℤ) * (w.getD 2 0 * w.getD 2 0) + bpB 7 (n : ℤ) * (w.getD 3 0 * w.getD 3 0) +
  bpA 8 ((n - 1 : ℕ) : ℤ) * (w.getD 1 0 * w.getD 1 0) + bpB 8 (n : ℤ) * (w.getD 2 0 * w.getD 2 0) +
  bpA 9 ((n - 1 : ℕ) : ℤ) * (w.getD 0 0 * w.getD 0 0) + bpB 9 (n : ℤ) * (w.getD 1 0 * w.getD 1 0)

/-- The band`s constant`s term at the place `c`, times `bandDEN` and the square of the numerators` scale, read at the window `w`. -/
def gWb (c : ℕ) (w : List ℤ) : ℤ :=
  bpG 0 (c : ℤ) * (2 * (w.getD 1 0 * w.getD 4 0)) +
  bpG 1 (c : ℤ) * (2 * (w.getD 2 0 * w.getD 4 0)) +
  bpG 2 (c : ℤ) * (2 * (w.getD 1 0 * w.getD 3 0)) +
  bpG 3 (c : ℤ) * (2 * (w.getD 3 0 * w.getD 4 0)) +
  bpG 4 (c : ℤ) * (2 * (w.getD 2 0 * w.getD 3 0)) +
  bpG 5 (c : ℤ) * (2 * (w.getD 1 0 * w.getD 2 0)) +
  bpG 6 (c : ℤ) * (w.getD 4 0 * w.getD 4 0) +
  bpG 7 (c : ℤ) * (w.getD 3 0 * w.getD 3 0) +
  bpG 8 (c : ℤ) * (w.getD 2 0 * w.getD 2 0) +
  bpG 9 (c : ℤ) * (w.getD 1 0 * w.getD 1 0)

theorem bandW_eq (n : ℕ) (w : List ℤ) :
    bandW n w = ∑ b ∈ Finset.range 16, (w.getD (3 - bS b) 0 * w.getD (bD b - bS b) 0 * bpA (bVi b) ((n - 1 : ℕ) : ℤ) +
      w.getD (4 - bS b) 0 * w.getD (bD b - bS b + 1) 0 * bpB (bVi b) (n : ℤ)) := by
  simp only [bandW, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, bS, bD, bVi]
  ring

theorem gWb_eq (c : ℕ) (w : List ℤ) :
    gWb c w = ∑ b ∈ Finset.range 16, w.getD (4 - bS b) 0 * w.getD (bD b - bS b + 1) 0 * bpG (bVi b) (c : ℤ) := by
  simp only [gWb, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, bS, bD, bVi]
  ring

end Window
end SIDEExplicitFormula
