import SIDEExplicitFormula.Window.FarClosed

/-!
# L9c3: the band`s vectors against `fA`, `fB` and `fG` as integer polynomials over one denominator

Written by relay tools/b768_band_data.py from the kernel`s own files (ArchClosed.lean`s blob 3ec80af752678d30 and Coeffs.lean`s);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The band`s ten vectors of `ArchClosed.lean`, in the order its blocks read them (`bVi`). -/
noncomputable def bVec : ℕ → Fin 7 → ℝ
  | 0 => bandV03
  | 1 => bandV02
  | 2 => bandV12
  | 3 => bandV01
  | 4 => bandV11
  | 5 => bandV21
  | 6 => bandV00
  | 7 => bandV10
  | 8 => bandV20
  | 9 => bandV30
  | _ => fun _ => 0

/-- `bVec v` against `fA`. -/
noncomputable def bqA (v : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, bVec v l * fA l c

/-- `bVec v` against `fB`. -/
noncomputable def bqB (v : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, bVec v l * fB l c

/-- `bVec v` against `fG`. -/
noncomputable def bqG (v : ℕ) (c : ℝ) : ℝ := ∑ l : Fin 7, bVec v l * fG l c

/-- The common denominator of the coefficients of `bqA`, `bqB` and `bqG`. -/
def bandDEN : ℕ := 2116800

/-- `bandDEN * bqA v c` as a polynomial in `c` with integer coefficients. -/
def bpA : ℕ → ℤ → ℤ
  | 0, x => ((((((((-8400)) * x + (-29400)) * x + (-35280)) * x + (-14700)) * x + 0) * x + 0) * x + 0) * x + 420
  | 1, x => (((((((25200) * x + 58800) * x + 0) * x + (-58800)) * x + 0) * x + 0) * x + 0) * x + 25200
  | 2, x => (((((((25200) * x + 117600) * x + 176400) * x + 58800) * x + (-58800)) * x + 0) * x + 58800) * x + 25200
  | 3, x => ((((((((-25200)) * x + (-29400)) * x + 35280) * x + (-14700)) * x + 0) * x + 0) * x + 0) * x + 54180
  | 4, x => ((((((((-75600)) * x + (-264600)) * x + (-105840)) * x + 396900) * x + 117600) * x + (-352800)) * x + 235200) * x + 391860
  | 5, x => ((((((((-25200)) * x + (-147000)) * x + (-317520)) * x + (-249900)) * x + 117600) * x + 352800) * x + 235200) * x + 54180
  | 6, x => (((((((8400) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 8400
  | 7, x => (((((((75600) * x + 176400) * x + (-105840)) * x + (-176400)) * x + 294000) * x + (-176400)) * x + 58800) * x + 498960
  | 8, x => (((((((75600) * x + 352800) * x + 423360) * x + (-352800)) * x + (-940800)) * x + 0) * x + 940800) * x + 498960
  | 9, x => (((((((8400) * x + 58800) * x + 176400) * x + 294000) * x + 294000) * x + 176400) * x + 58800) * x + 8400
  | _, _ => 0

/-- `bandDEN * bqB v c` as a polynomial in `c` with integer coefficients. -/
def bpB : ℕ → ℤ → ℤ
  | 0, x => (((((((8400) * x + 29400) * x + 35280) * x + 14700) * x + 0) * x + 0) * x + 0) * x + 0
  | 1, x => ((((((((-25200)) * x + (-58800)) * x + 0) * x + 58800) * x + 0) * x + 0) * x + 0) * x + 0
  | 2, x => ((((((((-25200)) * x + (-117600)) * x + (-176400)) * x + (-58800)) * x + 58800) * x + 0) * x + (-58800)) * x + 0
  | 3, x => (((((((25200) * x + 29400) * x + (-35280)) * x + 14700) * x + 0) * x + 0) * x + 0) * x + 0
  | 4, x => (((((((75600) * x + 264600) * x + 105840) * x + (-396900)) * x + (-117600)) * x + 352800) * x + (-235200)) * x + 0
  | 5, x => (((((((25200) * x + 147000) * x + 317520) * x + 249900) * x + (-117600)) * x + (-352800)) * x + (-235200)) * x + 0
  | 6, x => ((((((((-8400)) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0) * x + 0
  | 7, x => ((((((((-75600)) * x + (-176400)) * x + 105840) * x + 176400) * x + (-294000)) * x + 176400) * x + (-58800)) * x + 0
  | 8, x => ((((((((-75600)) * x + (-352800)) * x + (-423360)) * x + 352800) * x + 940800) * x + 0) * x + (-940800)) * x + 0
  | 9, x => ((((((((-8400)) * x + (-58800)) * x + (-176400)) * x + (-294000)) * x + (-294000)) * x + (-176400)) * x + (-58800)) * x + 0
  | _, _ => 0

/-- `bandDEN * bqG v c` as a polynomial in `c` with integer coefficients. -/
def bpG : ℕ → ℤ → ℤ
  | 0, x => ((((((8400) * x + 25200) * x + 23380) * x + 4760) * x + (-1260)) * x + 560) * x + (-319)
  | 1, x => (((((((-25200)) * x + (-46200)) * x + 21000) * x + 45500) * x + (-19740)) * x + 12040) * x + (-8500)
  | 2, x => (((((((-25200)) * x + (-105000)) * x + (-126000)) * x + (-3500)) * x + 53760) * x + (-24220)) * x + (-43780)
  | 3, x => ((((((25200) * x + 16800) * x + (-41580)) * x + 35840) * x + (-21420)) * x + 15400) * x + (-12031)
  | 4, x => ((((((75600) * x + 226800) * x + (-1260)) * x + (-380520)) * x + 65100) * x + 293160) * x + (-363707)
  | 5, x => ((((((25200) * x + 134400) * x + 252420) * x + 133840) * x + (-168420)) * x + (-264880)) * x + (-117871)
  | 6, x => (((((((-8400)) * x + 4200) * x + (-2800)) * x + 2100) * x + (-1680)) * x + 1400) * x + (-1200)
  | 7, x => (((((((-75600)) * x + (-138600)) * x + 168840) * x + 83580) * x + (-317940)) * x + 333060) * x + (-249332)
  | 8, x => (((((((-75600)) * x + (-315000)) * x + (-272160)) * x + 465780) * x + 696360) * x + (-304920)) * x + (-752072)
  | 9, x => (((((((-8400)) * x + (-54600)) * x + (-149800)) * x + (-223300)) * x + (-192780)) * x + (-93660)) * x + (-21780)
  | _, _ => 0

theorem bqA_poly (v : ℕ) (hv : v ≤ 9) (c : ℕ) : bqA v (c : ℝ) = (bpA v (c : ℤ) : ℝ) / (bandDEN : ℝ) := by
  interval_cases v <;>
    simp only [bqA, bVec, bandV00, bandV01, bandV02, bandV03, bandV10, bandV11, bandV12, bandV20, bandV21, bandV30, fA, bpA, bandDEN, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

theorem bqB_poly (v : ℕ) (hv : v ≤ 9) (c : ℕ) : bqB v (c : ℝ) = (bpB v (c : ℤ) : ℝ) / (bandDEN : ℝ) := by
  interval_cases v <;>
    simp only [bqB, bVec, bandV00, bandV01, bandV02, bandV03, bandV10, bandV11, bandV12, bandV20, bandV21, bandV30, fB, bpB, bandDEN, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

theorem bqG_poly (v : ℕ) (hv : v ≤ 9) (c : ℕ) : bqG v (c : ℝ) = (bpG v (c : ℤ) : ℝ) / (bandDEN : ℝ) := by
  interval_cases v <;>
    simp only [bqG, bVec, bandV00, bandV01, bandV02, bandV03, bandV10, bandV11, bandV12, bandV20, bandV21, bandV30, fG, bpG, bandDEN, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    push_cast <;>
    ring

end Window
end SIDEExplicitFormula
