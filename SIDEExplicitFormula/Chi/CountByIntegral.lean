/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/CountByIntegral.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF THE PART OF Zeta23/RvM/CountByIntegral.lean THAT EF_lit'S ROUTE CONSUMES (relay data/b569_route.txt:
the Λ facts `rectangle_identity` reads -- analyticity, `Λ = Γ·L` on the right half-plane, the zero set, the orders). For
primitive `χ ≠ 1`, `Λ(·, χ) = completedLFunction χ` is entire (no poles: ζ's `{0, 1}` exclusions drop); it does not vanish
on `1 ≤ Re s` and, by the functional equation (which carries `χ⁻¹` and a nonzero root number), not on `Re s ≤ 0`; so its
zeros are exactly the nontrivial zeros of `L(·, χ)`, and on `0 < Re s` its analytic order is `zeroMultChi`.
Nothing here proves GRH or locates any zero.
-/
import SIDEExplicitFormula.Chi.XiLogDeriv

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- `Λ(·, χ)` is analytic everywhere, for `χ ≠ 1`. -/
theorem analyticAt_completedLFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (completedLFunction χ) s :=
  (differentiable_completedLFunction h1).analyticAt s

/-- `Λ(s, χ) = 0 ↔ L(s, χ) = 0` on `0 < Re s`. -/
theorem completedLFunction_eq_zero_iff_of_re_pos {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = 0 ↔ LFunction χ s = 0 := by
  rw [(completedLFunction_eventuallyEq_mul h1 hs).eq_of_nhds, mul_eq_zero]
  simp [gammaFactor_ne_zero_of_re_pos χ hs]

/-- `Λ(s, χ) ≠ 0` on `Re s ≤ 0`, for primitive `χ ≠ 1`: `Λ(s, χ) = N^{1/2 − s} ε(χ⁻¹) Λ(1 − s, χ⁻¹)` and
`1 ≤ Re (1 − s)`. -/
theorem completedLFunction_ne_zero_of_re_nonpos {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {s : ℂ}
    (hs : s.re ≤ 0) : completedLFunction χ s ≠ 0 := by
  have hinvp := isPrimitive_inv hχ
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine mul_ne_zero (mul_ne_zero (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1)
    (rootNumber_ne_zero hχ h1)) ?_
  exact completedLFunction_ne_zero_of_one_le_re hinv1 (by simp; linarith)

/-- **The zeros of `Λ(·, χ)` are exactly the nontrivial zeros of `L(·, χ)`**, for primitive `χ ≠ 1`. -/
theorem completedLFunction_eq_zero_iff {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {s : ℂ} :
    completedLFunction χ s = 0 ↔ IsNontrivialZeroChi χ s := by
  constructor
  · intro h
    have hs1 : 0 < s.re := by
      by_contra hle
      exact completedLFunction_ne_zero_of_re_nonpos hχ h1 (not_lt.mp hle) h
    have hs2 : s.re < 1 := by
      by_contra hle
      exact completedLFunction_ne_zero_of_one_le_re h1 (not_lt.mp hle) h
    exact ⟨(completedLFunction_eq_zero_iff_of_re_pos h1 hs1).mp h, hs1, hs2⟩
  · rintro ⟨hz, hs1, _⟩
    exact (completedLFunction_eq_zero_iff_of_re_pos h1 hs1).mpr hz

/-- On `0 < Re ρ` the analytic order of `Λ(·, χ)` is `zeroMultChi χ ρ`. -/
theorem analyticOrderNatAt_completedLFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {ρ : ℂ} (h : 0 < ρ.re) :
    analyticOrderNatAt (completedLFunction χ) ρ = zeroMultChi χ ρ := by
  unfold zeroMultChi analyticOrderNatAt
  rw [analyticOrderAt_LFunction_eq_completed h1 h]

end GRHWeil
end SIDEExplicitFormula
