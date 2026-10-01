/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/XiLogDeriv.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/XiLogDeriv.lean. For `χ ≠ 1` (primitive where the functional equation is used), with
Mathlib's completed function `Λ(s, χ) = completedLFunction χ s` and its Γ factor `gammaFactor χ s` (`Γℝ(s)` for even `χ`,
`Γℝ(s + 1)` for odd):
* on `0 < Re s`, `Λ(·, χ) = gammaFactor χ · L(·, χ)` as germs, and `Λ'/Λ = gammaFactor'/gammaFactor + L'/L` away from the
  zeros of `L`;
* the root number of a primitive `χ ≠ 1` is nonzero -- derived here from the functional equation at `s = −1` and
  `Λ(2, χ) ≠ 0` (Mathlib states no lemma for it);
* the functional equation for the log-derivative, which for `χ` PAIRS `χ` WITH `χ⁻¹` and carries the conductor:
  `Λ'/Λ(1 − s, χ) = −(log N + Λ'/Λ(s, χ⁻¹))` where `Λ(s, χ⁻¹) ≠ 0` (ζ's is `Λ'/Λ(1 − s) = −Λ'/Λ(s)`);
* in the open strip the zeros of `Λ(·, χ)` are the nontrivial zeros of `L(·, χ)`, with the same analytic order.
Nothing here proves GRH or locates any zero.
-/
import SIDEExplicitFormula.Chi.ZeroConfig
import Mathlib.Analysis.Calculus.LogDeriv

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- `gammaFactor ψ` is differentiable at every `s` with `0 < Re s` (the inverse of the entire `1 / gammaFactor`). -/
theorem differentiableAt_gammaFactor (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gammaFactor ψ) s := by
  have h : DifferentiableAt ℂ (fun u => ((gammaFactor ψ u)⁻¹)⁻¹) s :=
    ((gammaFactor_inv_differentiable ψ) s).inv (inv_ne_zero (gammaFactor_ne_zero_of_re_pos ψ hs))
  convert h using 1
  funext u
  rw [inv_inv]

/-- On the right half-plane `Λ(·, χ) = gammaFactor χ · L(·, χ)` as germs, for `χ ≠ 1`. -/
theorem completedLFunction_eventuallyEq_mul {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ =ᶠ[𝓝 s] fun u => gammaFactor χ u * LFunction χ u := by
  have hN := ne_one_of_ne_one h1
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hΓ := gammaFactor_ne_zero_of_re_pos χ hu
  rw [LFunction_eq_completed_div_gammaFactor χ u (Or.inr hN)]
  field_simp

/-- **`Λ'/Λ = gammaFactor'/gammaFactor + L'/L`** on `0 < Re s` away from the zeros of `L(·, χ)`. -/
theorem logDeriv_completedLFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) (hL : LFunction χ s ≠ 0)
    (hs : 0 < s.re) :
    logDeriv (completedLFunction χ) s = logDeriv (gammaFactor χ) s + logDeriv (LFunction χ) s := by
  have hev := completedLFunction_eventuallyEq_mul h1 hs
  have heq : logDeriv (completedLFunction χ) s = logDeriv (fun u => gammaFactor χ u * LFunction χ u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (gammaFactor_ne_zero_of_re_pos χ hs) hL (differentiableAt_gammaFactor χ hs)
    ((differentiable_LFunction h1) s)

/-- `Λ(s, χ) ≠ 0` on `1 ≤ Re s`, for `χ ≠ 1`. -/
theorem completedLFunction_ne_zero_of_one_le_re {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    completedLFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  rw [(completedLFunction_eventuallyEq_mul h1 hs0).eq_of_nhds]
  exact mul_ne_zero (gammaFactor_ne_zero_of_re_pos χ hs0) (LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hs)

/-- **The root number of a primitive `χ ≠ 1` is nonzero**: the functional equation at `s = −1` gives
`Λ(2, χ) = N^{−3/2} ε(χ) Λ(−1, χ⁻¹)` and `Λ(2, χ) ≠ 0`. -/
theorem rootNumber_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : rootNumber χ ≠ 0 := by
  intro h0
  have hFE := hχ.completedLFunction_one_sub (-1)
  rw [h0, mul_zero, zero_mul] at hFE
  have h2 : completedLFunction χ (1 - -1) ≠ 0 := completedLFunction_ne_zero_of_one_le_re h1 (by norm_num)
  exact h2 hFE

/-- **The functional equation for the log-derivative, across `χ` and `χ⁻¹`.** For primitive `χ ≠ 1` and `s` with
`Λ(s, χ⁻¹) ≠ 0`: `Λ'/Λ(1 − s, χ) = −(log N + Λ'/Λ(s, χ⁻¹))`. -/
theorem logDeriv_completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (s : ℂ)
    (hne : completedLFunction χ⁻¹ s ≠ 0) :
    logDeriv (completedLFunction χ) (1 - s) = -(Complex.log N + logDeriv (completedLFunction χ⁻¹) s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hε := rootNumber_ne_zero hχ h1
  set c : ℂ → ℂ := fun u => (N : ℂ) ^ (u - 1 / 2) * rootNumber χ with hc
  have hFE : (completedLFunction χ ∘ fun u : ℂ => 1 - u) = fun u => c u * completedLFunction χ⁻¹ u := by
    funext u
    simp only [Function.comp_apply, hc]
    rw [hχ.completedLFunction_one_sub u]
  have hdΛ : DifferentiableAt ℂ (completedLFunction χ) (1 - s) := (differentiable_completedLFunction h1) _
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hdΛ hg
  rw [hFE] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  have hcd : HasDerivAt c ((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1 * rootNumber χ) s :=
    (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hN0)).mul_const _
  have hc0 : c s ≠ 0 := mul_ne_zero (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1) hε
  have hp : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hlc : logDeriv c s = Complex.log N := by
    rw [logDeriv_apply, hcd.deriv, show c s = (N : ℂ) ^ (s - 1 / 2) * rootNumber χ from rfl, mul_one,
      show (N : ℂ) ^ (s - 1 / 2) * Complex.log N * rootNumber χ
        = ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ) * Complex.log N by ring]
    exact mul_div_cancel_left₀ _ (mul_ne_zero hp hε)
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  rw [logDeriv_mul s hc0 hne hcd.differentiableAt ((differentiable_completedLFunction hinv) s), hlc, hderiv] at key
  linear_combination key

/-- In the open critical strip the zeros of `Λ(·, χ)` are the nontrivial zeros of `L(·, χ)`, with the same analytic
order (the Γ factor is analytic and nonvanishing there). -/
theorem completedLFunction_zeros_strip {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {ρ : ℂ} (h : 0 < ρ.re)
    (h' : ρ.re < 1) :
    (completedLFunction χ ρ = 0 ↔ IsNontrivialZeroChi χ ρ) ∧
      analyticOrderAt (completedLFunction χ) ρ = analyticOrderAt (LFunction χ) ρ := by
  have hval : completedLFunction χ ρ = gammaFactor χ ρ * LFunction χ ρ :=
    (completedLFunction_eventuallyEq_mul h1 h).eq_of_nhds
  refine ⟨?_, (analyticOrderAt_LFunction_eq_completed h1 h).symm⟩
  rw [hval, mul_eq_zero, IsNontrivialZeroChi]
  constructor
  · rintro (hΓ0 | hz)
    · exact absurd hΓ0 (gammaFactor_ne_zero_of_re_pos χ h)
    · exact ⟨hz, h, h'⟩
  · rintro ⟨hz, -, -⟩
    exact Or.inr hz

end GRHWeil
end SIDEExplicitFormula
