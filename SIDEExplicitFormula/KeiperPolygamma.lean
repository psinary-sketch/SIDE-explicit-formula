/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperPolygamma.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(8); W-ORD-KEIPER-FACE, OPEN_TRAILS :11704, re-priced at :12132) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

TOWARD (O4) AT EVERY INDEX. Keiper's definition of λ_n at every n is `KeiperTaylorIdentity` (Keiper.lean): its first three
obligations are proved (`binomialTransform_holds`, `logDerivSplit_holds`, `stieltjesLog_holds`, KeiperIdentities.lean), and the
fourth, `GammaRZetaValues`, at its first index (`gammaRZetaOne_holds`, KeiperGammaOne.lean, by the reflection formula, which fixes
the even zeta values alone). At every index it is the polygamma value ψ⁽ⁿ⁾(1/2) = (−1)^(n+1) n! (2^(n+1) − 1) ζ(n + 1), and
Mathlib at the pin holds the digamma function `Complex.digamma = logDeriv Gamma` with its functional equation and its values at
1 and 1/2, and no series for it. This file proves, on Mathlib's `digamma`:

* `analyticAt_digamma`: digamma is analytic on the right half-plane;
* `iteratedDeriv_digamma_shift`: its functional equation at every order, ψ⁽ⁿ⁾(z) = ψ⁽ⁿ⁾(z + 1) − (−1)^n n! z^(−1−n);
* `iteratedDeriv_digamma_shift_nat`: the same N times, ψ⁽ⁿ⁾(z) = ψ⁽ⁿ⁾(z + N) − Σ_{j<N} (−1)^n n! (z + j)^(−1−n);
* `tendsto_partial_sums_of_tail`: where ψ⁽ⁿ⁾(z + N) → 0, the partial sums Σ_{j<N} (−1)^n n! (z + j)^(−1−n) tend to −ψ⁽ⁿ⁾(z).

What stays open for (O4) at every index, named and not assumed: the tail ψ⁽ⁿ⁾(z + N) → 0 for n ≥ 1; the odd-zeta split
Σ_j (j + 1/2)^(−s) = (2^s − 1) ζ(s); and Γℝ's logarithmic derivative read as −(log π)/2 + ψ(s/2)/2 at every order. Nothing here
is a statement about the zeros of ζ, or proves RH or any sign of any λ_n.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperPolygamma

/-- The right half-plane. -/
def rhp : Set ℂ := {z | 0 < z.re}

theorem mem_rhp {z : ℂ} : z ∈ rhp ↔ 0 < z.re := Iff.rfl

theorem isOpen_rhp : IsOpen rhp := by
  show IsOpen {z : ℂ | 0 < z.re}
  exact isOpen_lt continuous_const Complex.continuous_re

/-- A point of the right half-plane is no pole of Γ. -/
theorem ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  have h1 : z.re = -(m : ℝ) := by rw [h]; simp
  have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem differentiableOn_Gamma_rhp : DifferentiableOn ℂ Gamma rhp :=
  fun z hz => (differentiableAt_Gamma z (ne_neg_nat_of_re_pos (mem_rhp.mp hz))).differentiableWithinAt

theorem analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Gamma z :=
  differentiableOn_Gamma_rhp.analyticAt (isOpen_rhp.mem_nhds (mem_rhp.mpr hz))

/-- **Digamma is analytic on the right half-plane.** -/
theorem analyticAt_digamma {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ digamma z := by
  have hG : AnalyticAt ℂ Gamma z := analyticAt_Gamma_of_re_pos hz
  have h0 : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz
  have e : digamma = deriv Gamma / Gamma := by
    funext w
    rw [digamma_def, logDeriv_apply, Pi.div_apply]
  rw [e]
  exact hG.deriv.div hG h0

/-- The functional equation as germs: near a point of the right half-plane, ψ(w) = ψ(w + 1) − w⁻¹. -/
theorem digamma_eventually_shift {z : ℂ} (hz : 0 < z.re) :
    digamma =ᶠ[𝓝 z] fun w => digamma (w + 1) - w⁻¹ := by
  filter_upwards [isOpen_rhp.mem_nhds (mem_rhp.mpr hz)] with w hw
  rw [digamma_apply_add_one w (ne_neg_nat_of_re_pos (mem_rhp.mp hw))]
  ring

/-- The `n`-th derivative of `w ↦ w⁻¹`. -/
theorem iteratedDeriv_inv_apply (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => w⁻¹) z = (-1) ^ n * (n.factorial : ℂ) * z ^ (-1 - n : ℤ) := by
  rw [iteratedDeriv_eq_iterate]
  exact iter_deriv_inv n z

/-- **THE FUNCTIONAL EQUATION AT EVERY ORDER**: ψ⁽ⁿ⁾(z) = ψ⁽ⁿ⁾(z + 1) − (−1)^n n! z^(−1−n) on the right half-plane. -/
theorem iteratedDeriv_digamma_shift (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv n digamma z =
      iteratedDeriv n digamma (z + 1) - (-1) ^ n * (n.factorial : ℂ) * z ^ (-1 - n : ℤ) := by
  have hz1 : 0 < (z + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hf : ContDiffAt ℂ n (fun w : ℂ => w + 1) z := (contDiff_id.add contDiff_const).contDiffAt
  have hA : ContDiffAt ℂ n (fun w : ℂ => digamma (w + 1)) z :=
    (analyticAt_digamma hz1).contDiffAt.comp z hf
  have hB : ContDiffAt ℂ n (fun w : ℂ => w⁻¹) z := contDiffAt_inv ℂ (ne_zero_of_re_pos hz)
  have h1 : iteratedDeriv n (fun w : ℂ => digamma (w + 1)) z = iteratedDeriv n digamma (z + 1) := by
    rw [iteratedDeriv_comp_add_const n digamma 1]
  have h2 := iteratedDeriv_inv_apply n z
  calc iteratedDeriv n digamma z
      = iteratedDeriv n (fun w : ℂ => digamma (w + 1) - w⁻¹) z :=
        Filter.EventuallyEq.iteratedDeriv_eq n (digamma_eventually_shift hz)
    _ = iteratedDeriv n (fun w : ℂ => digamma (w + 1)) z - iteratedDeriv n (fun w : ℂ => w⁻¹) z :=
        iteratedDeriv_fun_sub hA hB
    _ = iteratedDeriv n digamma (z + 1) - (-1) ^ n * (n.factorial : ℂ) * z ^ (-1 - n : ℤ) := by
        rw [h1, h2]

/-- **THE FUNCTIONAL EQUATION N TIMES**: ψ⁽ⁿ⁾(z) = ψ⁽ⁿ⁾(z + N) − Σ_{j<N} (−1)^n n! (z + j)^(−1−n). -/
theorem iteratedDeriv_digamma_shift_nat (n N : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv n digamma z = iteratedDeriv n digamma (z + N)
      - ∑ j ∈ Finset.range N, (-1) ^ n * (n.factorial : ℂ) * (z + j) ^ (-1 - n : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hzN : 0 < (z + (N : ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have h3 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have e : z + ((N + 1 : ℕ) : ℂ) = z + (N : ℂ) + 1 := by
      push_cast
      ring
    rw [ih, iteratedDeriv_digamma_shift n hzN, Finset.sum_range_succ, e]
    ring

/-- **THE POLYGAMMA VALUE FROM ITS PARTIAL SUMS, ON THE TAIL**: where ψ⁽ⁿ⁾(z + N) → 0, the partial sums
Σ_{j<N} (−1)^n n! (z + j)^(−1−n) tend to −ψ⁽ⁿ⁾(z). -/
theorem tendsto_partial_sums_of_tail (n : ℕ) {z : ℂ} (hz : 0 < z.re)
    (htail : Tendsto (fun N : ℕ => iteratedDeriv n digamma (z + N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (-1) ^ n * (n.factorial : ℂ) * (z + j) ^ (-1 - n : ℤ))
      atTop (𝓝 (-iteratedDeriv n digamma z)) := by
  have h : (fun N : ℕ => ∑ j ∈ Finset.range N, (-1) ^ n * (n.factorial : ℂ) * (z + j) ^ (-1 - n : ℤ))
      = fun N : ℕ => iteratedDeriv n digamma (z + N) - iteratedDeriv n digamma z := by
    funext N
    rw [iteratedDeriv_digamma_shift_nat n N hz]
    ring
  rw [h]
  have h2 := htail.sub_const (iteratedDeriv n digamma z)
  rw [zero_sub] at h2
  exact h2

end KeiperPolygamma
end SIDEExplicitFormula
