import SIDEExplicitFormula.Window.FarPoly
import SIDEExplicitFormula.Window.WinCheck

/-!
# L9c2: the far sum's coefficient of `log n` and its constant's terms, read at a window of the convolution sums

`farW n w` is `∑ k < 4, ∑ m < 5, bw m * (pA k (n - 1) * w[3 + m - k] + pB k n * w[4 + m - k])` and `gW c w` is
`∑ k < 4, ∑ m < 5, bw m * pG k c * w[4 + m - k]`, each unrolled so that the kernel reads them place by place (`farW_eq`,
`gW_eq`). It reads no datum.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The fourth difference of a window's places from `o`, `∑ m < 5, bw m * w[o + m]`, unrolled. -/
def sm (o : ℕ) (w : List ℤ) : ℤ :=
  w.getD o 0 - 4 * w.getD (o + 1) 0 + 6 * w.getD (o + 2) 0 - 4 * w.getD (o + 3) 0 + w.getD (o + 4) 0

/-- The coefficient of `log n` in the far sum, times `6 * farDEN`, read at the window `w`. -/
def farW (n : ℕ) (w : List ℤ) : ℤ :=
  pA 0 ((n - 1 : ℕ) : ℤ) * sm 3 w + pB 0 (n : ℤ) * sm 4 w +
  pA 1 ((n - 1 : ℕ) : ℤ) * sm 2 w + pB 1 (n : ℤ) * sm 3 w +
  pA 2 ((n - 1 : ℕ) : ℤ) * sm 1 w + pB 2 (n : ℤ) * sm 2 w +
  pA 3 ((n - 1 : ℕ) : ℤ) * sm 0 w + pB 3 (n : ℤ) * sm 1 w

/-- The term of the far sum's constant at the shift `c`, times `6 * farDEN`, read at the window `w`. -/
def gW (c : ℕ) (w : List ℤ) : ℤ :=
  pG 0 (c : ℤ) * sm 4 w + pG 1 (c : ℤ) * sm 3 w + pG 2 (c : ℤ) * sm 2 w + pG 3 (c : ℤ) * sm 1 w

theorem farW_eq (n : ℕ) (w : List ℤ) :
    farW n w = ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5,
      bw m * (pA k ((n - 1 : ℕ) : ℤ) * w.getD (3 + m - k) 0 + pB k (n : ℤ) * w.getD (4 + m - k) 0) := by
  simp only [farW, sm, Finset.sum_range_succ, Finset.sum_range_zero, bw, add_zero, zero_add]
  ring

theorem gW_eq (c : ℕ) (w : List ℤ) :
    gW c w = ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, bw m * (pG k (c : ℤ) * w.getD (4 + m - k) 0) := by
  simp only [gW, sm, Finset.sum_range_succ, Finset.sum_range_zero, bw, add_zero, zero_add]
  ring

end Window
end SIDEExplicitFormula
