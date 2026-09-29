/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZetaBounds.lean
THIS PROGRAMME'S WORK (act b564, ruling (R174)(5)(c); W-ORD-GRH-WEIL, act two) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FRONTIER'S SECOND MODULE, ITS χ-ANALOGUES IN THE MODULE'S OWN ORDER. Zeta23/FromPNTPlus/ZetaBounds.lean is the growth
side of the ζ-arc: bounds on ζ and ζ' in vertical strips, reached through the Euler–Maclaurin form `riemannZeta0` and its
agreement with ζ (`Zeta0EqZeta`), then the lower bounds near `re s = 1` and the zero-free region. Its ζ-naming declarations,
in order, begin `analyticAt_riemannZeta`, `differentiableAt_deriv_riemannZeta`, `riemannZetaResidue`,
`riemannZetaLogDerivResidue`, `riemannZetaLogDerivResidueBigO`, `riemannZeta0`. Their χ-analogues for `LFunction χ`,
primitive `χ ≠ 1`, are below: the pole at `1` is absent, so the residue statements become boundedness statements, and the
log-derivative is bounded near `1` because `LFunction χ 1 ≠ 0`. `LFunction0` is the Abel-summation analogue of
`riemannZeta0` (the partial sums of `χ` in place of `⌊x⌋ + 1/2 - x`).

Beside them, the first fact the analogue of `HasDerivAtZeta0` consumes, which the rev holds under no name: the partial sums of
`χ ≠ 1` are bounded (`norm_charPartialSum_le`, `‖S_χ(x)‖ ≤ N + 1`, from `MulChar.sum_eq_zero_of_ne_one` over a block of `N`
consecutive naturals).

WHERE THIS FILE STOPS -- the held point, at its four attempts: the χ-analogue of `HasDerivAtZeta0` (s ↦ `LFunction0 χ M s`
differentiable on `0 < re s`, the derivative taken under the integral over `(M, ∞)`), and after it the analogue of
`Zeta0EqZeta`, that `LFunction χ s = LFunction0 χ M s` on `0 < re s`. The rev holds the representation only where the
Dirichlet series converges absolutely (`LFunction_eq_LSeries`, `1 < re s`; `LSeries_eq_mul_integral` under
`LSeriesSummable`); the analytic tools the analogue would use (differentiation under the integral, the identity theorem) it
holds in general form. Nothing here is stubbed.

Nothing here proves GRH, RH, or any bound on `LFunction χ` in the strip.
-/
import SIDEExplicitFormula.Chi.ZeroConfig

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The analogue of `analyticAt_riemannZeta`: `LFunction χ` is analytic everywhere (no exception at `1` for `χ ≠ 1`). -/
theorem analyticAt_LFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) : AnalyticAt ℂ (LFunction χ) s :=
  LFunction_analyticOnNhd h1 s (mem_univ s)

/-- The analogue of `differentiableAt_deriv_riemannZeta`. -/
theorem differentiableAt_deriv_LFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    DifferentiableAt ℂ (deriv (LFunction χ)) s :=
  (analyticAt_LFunction h1 s).deriv.differentiableAt

/-- The analogue of `riemannZetaResidue`: no pole at `1` -- `LFunction χ` is bounded on a neighbourhood of `1`. -/
theorem LFunction_bddAbove_near_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    ∃ U ∈ 𝓝 (1 : ℂ), BddAbove ((norm ∘ LFunction χ) '' U) := by
  refine ⟨Metric.closedBall 1 1, Metric.closedBall_mem_nhds 1 one_pos, ?_⟩
  exact (isCompact_closedBall (1 : ℂ) 1).bddAbove_image
    (continuous_norm.comp (differentiable_LFunction h1).continuous).continuousOn

/-- `-(L'/L)` is continuous at `1`: `LFunction χ 1 ≠ 0` (`LFunction_apply_one_ne_zero`). -/
theorem continuousAt_neg_logDeriv_LFunction_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    ContinuousAt (-(deriv (LFunction χ) / LFunction χ)) 1 :=
  ((differentiableAt_deriv_LFunction h1 1).continuousAt.div
    (differentiable_LFunction h1).continuous.continuousAt (LFunction_apply_one_ne_zero h1)).neg

/-- The analogue of `riemannZetaLogDerivResidue`: `-(L'/L)` is bounded on a neighbourhood of `1`. -/
theorem LFunction_logDeriv_bddAbove_near_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    ∃ U ∈ 𝓝 (1 : ℂ), BddAbove ((norm ∘ (-(deriv (LFunction χ) / LFunction χ))) '' U) := by
  have hc := continuousAt_neg_logDeriv_LFunction_one h1
  obtain ⟨V, hV, hVb⟩ : ∃ V ∈ 𝓝 (1 : ℂ), ∀ s ∈ V,
      ‖(-(deriv (LFunction χ) / LFunction χ)) s - (-(deriv (LFunction χ) / LFunction χ)) 1‖ < 1 := by
    have := Metric.tendsto_nhds.mp hc 1 one_pos
    exact ⟨_, this, fun s hs => by simpa [dist_eq_norm] using hs⟩
  refine ⟨V, hV, ⟨‖(-(deriv (LFunction χ) / LFunction χ)) 1‖ + 1, ?_⟩⟩
  rintro y ⟨s, hs, rfl⟩
  have h := hVb s hs
  have h2 := norm_le_insert' ((-(deriv (LFunction χ) / LFunction χ)) s) ((-(deriv (LFunction χ) / LFunction χ)) 1)
  simp only [Function.comp_apply]
  linarith

/-- The analogue of `riemannZetaLogDerivResidueBigO`: `-(L'/L) = O(1)` at `1`. -/
theorem LFunction_logDeriv_isBigO_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    (-(deriv (LFunction χ) / LFunction χ)) =O[𝓝 (1 : ℂ)] (1 : ℂ → ℂ) :=
  (continuousAt_neg_logDeriv_LFunction_one h1).tendsto.isBigO_one ℂ

/-- The partial sums of `χ`: `S_χ(x) = Σ_{1 ≤ n ≤ ⌊x⌋} χ(n)`. -/
def charPartialSum (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N)

/-- A block of `N` consecutive naturals sums `χ` over all of `ZMod N`, hence to `0` for `χ ≠ 1`. -/
theorem sum_range_block_char_eq_zero {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (k : ℕ) :
    ∑ i ∈ Finset.range N, χ (((k + i : ℕ) : ZMod N)) = 0 := by
  have hbij : ∑ i ∈ Finset.range N, χ (((k + i : ℕ) : ZMod N)) = ∑ a : ZMod N, χ a := by
    refine Finset.sum_bij' (fun i _ => ((k + i : ℕ) : ZMod N)) (fun a _ => (a - (k : ZMod N)).val) ?_ ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.mem_univ _
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · intro i hi
      rw [Nat.cast_add, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    · intro a _
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
      ring
    · intro i _
      rfl
  rw [hbij]
  exact MulChar.sum_eq_zero_of_ne_one h1

/-- The partial sums of `χ ≠ 1` over `range m` are bounded by `N`. -/
theorem norm_sum_range_char_le {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, χ ((n : ℕ) : ZMod N)‖ ≤ N := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < N
    · calc ‖∑ n ∈ Finset.range m, χ ((n : ℕ) : ZMod N)‖
          ≤ ∑ n ∈ Finset.range m, ‖χ ((n : ℕ) : ZMod N)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = m := by simp
        _ ≤ N := by exact_mod_cast hm.le
    · push_neg at hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + N := ⟨m - N, by omega⟩
      rw [Finset.sum_range_add, sum_range_block_char_eq_zero h1 k, add_zero]
      exact ih k (by have := NeZero.pos N; omega)

/-- The partial sums `S_χ(x)` of `χ ≠ 1` are bounded: `‖S_χ(x)‖ ≤ N + 1` (the first fact the analogue of `HasDerivAtZeta0`
consumes, for the integrand's domination). -/
theorem norm_charPartialSum_le {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (x : ℝ) :
    ‖charPartialSum χ x‖ ≤ N + 1 := by
  unfold charPartialSum
  have e : ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ ((n : ℕ) : ZMod N)
      = χ ((0 : ℕ) : ZMod N) + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) := by
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  have hS : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N)
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ ((n : ℕ) : ZMod N) - χ ((0 : ℕ) : ZMod N) := by
    rw [e]
    ring
  rw [hS]
  calc ‖∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ ((n : ℕ) : ZMod N) - χ ((0 : ℕ) : ZMod N)‖
      ≤ ‖∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ ((n : ℕ) : ZMod N)‖ + ‖χ ((0 : ℕ) : ZMod N)‖ := norm_sub_le _ _
    _ ≤ N + 1 := add_le_add (norm_sum_range_char_le h1 _) (DirichletCharacter.norm_le_one χ _)

/-- The Abel-summation analogue of `riemannZeta0`: for `M : ℕ`,
`Σ_{1 ≤ n ≤ M} χ(n) n^{-s} - S_χ(M) M^{-s} + s ∫_{M}^{∞} S_χ(x) x^{-s-1} dx`. For `re s > 1` this is `LFunction χ s`
by summation by parts; its agreement with `LFunction χ` on `0 < re s` is the held point (see the header). -/
def LFunction0 (χ : DirichletCharacter ℂ N) (M : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) / (n : ℂ) ^ s) - charPartialSum χ M * (M : ℂ) ^ (-s)
    + s * ∫ x in Ioi (M : ℝ), charPartialSum χ x * (x : ℂ) ^ (-(s + 1))

end GRHWeil
end SIDEExplicitFormula
