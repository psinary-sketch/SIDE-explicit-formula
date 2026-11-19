/-
SIDE-explicit-formula -- SIDEExplicitFormula/AdmissibleWeights.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(6), statement (S5); W-ORD-SIGN-SECTORS) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ADMISSIBLE WEIGHTS FORM A CONVEX SET. At a width L, the admissible weights are the real weights c for which the pole term less
the prime-power side with c plus the archimedean term is at or above 0, in the order in which h2_sign is written, at each k in classK
that vanishes outside [-L, L] (`admissibleWeights`). The set is convex (`admissibleWeights_convex`): on such a k the prime-power side
is (S1)'s finite sum, linear in c (`primeTermQ_combo`), so the form at a convex combination of weights is the same combination of the
forms, the pole term and the archimedean term held fixed. Membership turns on the values of c up to the integer part of e^L alone
(`admissibleWeights_congr`). `h2_sign_upto L` says that the von Mangoldt function is a member (`h2_sign_upto_iff_mem`), zeta's prime
sum being the prime-power side at those weights term by term. No premise is bound; nothing here concerns any zero.
-/
import SIDEExplicitFormula.FormFinite
import SIDEExplicitFormula.DetectionRegion

open Complex
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **(S5) The admissible weights at width `L`:** the weights `c` for which pole term less prime-power side with `c` plus archimedean
term is at or above 0, in `h2_sign`'s order, at each `k` in classK that vanishes outside `[-L, L]`. -/
def admissibleWeights (L : ℝ) : Set (ℕ → ℝ) :=
  {c | ∀ k : ℝ → ℂ, classK k → (∀ u : ℝ, L < |u| → k u = 0) → 0 ≤ poleTerm k - Schema.primeTermQ c k + archTerm k}

/-- On a window the prime-power side is linear in the weights: (S1)'s finite sum. -/
theorem primeTermQ_combo (c₁ c₂ : ℕ → ℝ) (a b : ℝ) (k : ℝ → ℂ) (L : ℝ) (hk : ∀ u : ℝ, L < |u| → k u = 0) :
    Schema.primeTermQ (a • c₁ + b • c₂) k = (a : ℂ) * Schema.primeTermQ c₁ k + (b : ℂ) * Schema.primeTermQ c₂ k := by
  rw [primeTermQ_window (a • c₁ + b • c₂) k L hk, primeTermQ_window c₁ k L hk, primeTermQ_window c₂ k L hk,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- **(S5) The admissible weights form a convex set** at each width. -/
theorem admissibleWeights_convex (L : ℝ) : Convex ℝ (admissibleWeights L) := by
  intro c₁ h₁ c₂ h₂ a b ha hb hab
  simp only [admissibleWeights, Set.mem_setOf_eq] at h₁ h₂ ⊢
  intro k hk hkL
  have e₁ := h₁ k hk hkL
  have e₂ := h₂ k hk hkL
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have hform : poleTerm k - Schema.primeTermQ (a • c₁ + b • c₂) k + archTerm k =
      (a : ℂ) * (poleTerm k - Schema.primeTermQ c₁ k + archTerm k) +
        (b : ℂ) * (poleTerm k - Schema.primeTermQ c₂ k + archTerm k) := by
    rw [primeTermQ_combo c₁ c₂ a b k L hkL]
    linear_combination -(poleTerm k + archTerm k) * hab'
  rw [hform]
  exact add_nonneg (mul_nonneg (Complex.zero_le_real.mpr ha) e₁) (mul_nonneg (Complex.zero_le_real.mpr hb) e₂)

/-- **(S5) Membership turns on finitely many weights:** two weights that agree up to the integer part of `e^L` are admissible at
width `L` together or not at all. -/
theorem admissibleWeights_congr {L : ℝ} {c₁ c₂ : ℕ → ℝ} (h : ∀ n : ℕ, n ≤ ⌊Real.exp L⌋₊ → c₁ n = c₂ n) :
    c₁ ∈ admissibleWeights L ↔ c₂ ∈ admissibleWeights L := by
  have key : ∀ k : ℝ → ℂ, (∀ u : ℝ, L < |u| → k u = 0) → Schema.primeTermQ c₁ k = Schema.primeTermQ c₂ k := by
    intro k hk
    rw [primeTermQ_window c₁ k L hk, primeTermQ_window c₂ k L hk]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [h n (Nat.lt_add_one_iff.mp (Finset.mem_range.mp hn))]
  simp only [admissibleWeights, Set.mem_setOf_eq]
  constructor
  · intro h₁ k hk hkL
    rw [← key k hkL]
    exact h₁ k hk hkL
  · intro h₂ k hk hkL
    rw [key k hkL]
    exact h₂ k hk hkL

/-- **(S5) `h2_sign_upto L` says that the von Mangoldt function is an admissible weight at width `L`.** -/
theorem h2_sign_upto_iff_mem (L : ℝ) :
    h2_sign_upto L ↔ (fun n : ℕ => ArithmeticFunction.vonMangoldt n) ∈ admissibleWeights L :=
  Iff.rfl

end B321
end SIDEExplicitFormula
