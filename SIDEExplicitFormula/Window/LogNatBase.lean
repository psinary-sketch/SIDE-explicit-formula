import SIDEExplicitFormula.Window.LogData

/-!
# L11b, its frame: the logarithm of a factorization list, and the check of a run of lists

`facLog fac` is the weighted sum `∑ e log q` over a list of factors `(q, e)`, and `log_facProd_eq` reads the logarithm of a nonzero
product of factors as that sum. `natChk m L` checks, list by list from the index `m`, that each list's product is its index and that
each factor is a key of the primes' tree below 16,391 (`LPTree.facOK`); `natChk_spec` carries the check to each list of the run, read
by `natAt`. The runs themselves are generated (`LogNatData.lean`).
-/

namespace SIDEExplicitFormula.Window

/-- The weighted sum of the logarithms of a factorization list's bases. -/
noncomputable def facLog : List (ℕ × ℕ) → ℝ
  | [] => 0
  | x :: r => (x.2 : ℝ) * Real.log x.1 + facLog r

/-- The logarithm of a nonzero product of factors is its weighted sum of logarithms. -/
theorem log_facProd_eq : ∀ fac : List (ℕ × ℕ), facProd fac ≠ 0 → Real.log (facProd fac) = facLog fac
  | [], _ => by simp [facProd, facLog]
  | x :: r, h => by
    have h' : x.1 ^ x.2 * facProd r ≠ 0 := h
    have ha : x.1 ^ x.2 ≠ 0 := left_ne_zero_of_mul h'
    have hb : facProd r ≠ 0 := right_ne_zero_of_mul h'
    have ha' : ((x.1 : ℝ) ^ x.2) ≠ 0 := by exact_mod_cast ha
    have hb' : ((facProd r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hb
    simp only [facProd, facLog, Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul ha' hb', Real.log_pow, log_facProd_eq r hb]

/-- The check of a run of factorization lists from the index `m`. -/
def natChk : ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [] => true
  | m, f :: r => decide (facProd f = m) && lpTree.facOK 16391 f && natChk (m + 1) r

/-- The `i`-th list of a run, the empty list past its end. -/
def natAt : List (List (ℕ × ℕ)) → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | f :: _, 0 => f
  | _ :: r, i + 1 => natAt r i

/-- The check carried to each list of the run. -/
theorem natChk_spec : ∀ (L : List (List (ℕ × ℕ))) (m i : ℕ), natChk m L = true → i < L.length →
    facProd (natAt L i) = m + i ∧ lpTree.facOK 16391 (natAt L i) = true
  | [], _, _, _, hi => by simp at hi
  | f :: r, m, 0, h, _ => by
    simp only [natChk, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [natAt, Nat.add_zero]
    exact h.1
  | f :: r, m, i + 1, h, hi => by
    simp only [natChk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hi' : i < r.length := by simpa using hi
    obtain ⟨h1, h2⟩ := natChk_spec r (m + 1) i h.2 hi'
    simp only [natAt]
    exact ⟨by rw [h1]; omega, h2⟩

end SIDEExplicitFormula.Window
