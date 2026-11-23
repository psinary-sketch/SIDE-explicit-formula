import SIDEExplicitFormula.Window.LogNatData

/-!
# L11b: the logarithm of each integer from 1 to 16,390 in the primes of L10

For each `m` from 1 to 16,390, `log m` is the weighted sum `∑ e log q` over `m`'s factorization `nfac m`, each `q` a key of the
primes' tree (`logNat_eq`); and `log m` lies between the rational ends that L10's intervals give that sum (`logNat_bounds`).
-/

namespace SIDEExplicitFormula.Window

/-- **L11b: the logarithm of each integer from 1 to 16,390 as its factors' weighted sum of logarithms.** -/
theorem logNat_eq (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 16390) : Real.log m = facLog (nfac m) := by
  obtain ⟨hp, -⟩ := nfac_spec m h1 h2
  rw [← log_facProd_eq (nfac m) (by rw [hp]; omega), hp]

/-- The logarithm of each integer from 1 to 16,390 between its factors' rational ends from L10. -/
theorem logNat_bounds (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 16390) :
    ((lpTree.facLo (nfac m) : ℚ) : ℝ) ≤ Real.log m ∧ Real.log m ≤ ((lpTree.facHi (nfac m) : ℚ) : ℝ) := by
  obtain ⟨hp, hf⟩ := nfac_spec m h1 h2
  have h := LPTree.log_facProd lpTree lp_all 16391 (nfac m) hf
  rwa [hp] at h

end SIDEExplicitFormula.Window
