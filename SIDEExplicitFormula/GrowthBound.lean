/-
SIDE-explicit-formula -- SIDEExplicitFormula/GrowthBound.lean
THIS PROGRAMME'S WORK (act b517, ruling (R126)(3); (R124)(2)'s (d)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(d), the growth bound of W-ORD-WEIL-CONVERSE: for `h` integrable with support in `[-L, L]`, the kernel's transform
`paperFT h z = INT h u * exp(i z u) du` satisfies `|paperFT h z| <= (INT |h|) * exp(L |Im z|)` -- the norm of the
integral below the integral of the norm, and `|exp(i z u)| = exp(-u Im z) <= exp(L |Im z|)` on the support. At a zero
`rho`, `Im (gammaOf rho) = -(Re rho - 1/2)`, so the growth there is `exp(L |Re rho - 1/2|)`, (R124)(2)'s form.
Nothing here is a statement about the zeros: the corollary holds at every complex `rho`.
-/
import Zeta23.Defs

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **(d), the growth bound.** For `h` integrable with support in `[-L, L]` and any complex `z`,
`‖paperFT h z‖ ≤ (∫ ‖h‖) * exp (L * |Im z|)`. -/
theorem paperFT_growth (h : ℝ → ℂ) (L : ℝ) (hi : Integrable h) (hs : Function.support h ⊆ Set.Icc (-L) L)
    (z : ℂ) : ‖Zeta23.paperFT h z‖ ≤ (∫ u, ‖h u‖) * Real.exp (L * |z.im|) := by
  have hpt : ∀ u : ℝ, ‖h u * Complex.exp (Complex.I * z * (u : ℂ))‖ ≤ ‖h u‖ * Real.exp (L * |z.im|) := by
    intro u
    rw [norm_mul, Complex.norm_exp]
    by_cases h0 : h u = 0
    · simp [h0]
    · have hmem : u ∈ Set.Icc (-L) L := hs (Function.mem_support.mpr h0)
      have hu : |u| ≤ L := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hre : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by
        simp [Complex.mul_re, Complex.mul_im] <;> ring
      have key : -(z.im * u) ≤ L * |z.im| :=
        calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
          _ = |u| * |z.im| := by rw [abs_mul, mul_comm]
          _ ≤ L * |z.im| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      rw [hre]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (norm_nonneg _)
  unfold Zeta23.paperFT
  calc ‖∫ u, h u * Complex.exp (Complex.I * z * (u : ℂ))‖
      ≤ ∫ u, ‖h u * Complex.exp (Complex.I * z * (u : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, ‖h u‖ * Real.exp (L * |z.im|) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hi.norm.mul_const _) (Filter.Eventually.of_forall hpt)
    _ = (∫ u, ‖h u‖) * Real.exp (L * |z.im|) := integral_mul_const _ _

/-- **The corollary at a zero, in (R124)(2)'s form.** At `gammaOf rho`, the growth is `exp (L * |Re rho - 1/2|)`;
it holds at every complex `rho`, and is a growth at an off-line zero where `Re rho ≠ 1/2`. -/
theorem paperFT_growth_at (h : ℝ → ℂ) (L : ℝ) (hi : Integrable h) (hs : Function.support h ⊆ Set.Icc (-L) L)
    (ρ : ℂ) : ‖Zeta23.paperFT h (Zeta23.gammaOf ρ)‖ ≤ (∫ u, ‖h u‖) * Real.exp (L * |ρ.re - 1 / 2|) := by
  have him : (Zeta23.gammaOf ρ).im = -(ρ.re - 1 / 2) := by
    unfold Zeta23.gammaOf
    rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  have hb := paperFT_growth h L hi hs (Zeta23.gammaOf ρ)
  rwa [him, abs_neg] at hb

end B321
end SIDEExplicitFormula
