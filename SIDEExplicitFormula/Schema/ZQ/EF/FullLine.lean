/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/FullLine.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt rows E11 E12, group F) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE TWO LINES AND THE FULL-LINE IDENTITY, at `c = 3/2`. E11: on `Re s = 3/2` the logarithmic derivative of `lamQ` splits by E2, `Z_Q'/Z_Q` bounded by the series (`cC_summable`, at exactly `3/2`), the digamma term
by `digamma_growth_strip_wide`; the left vertical folds onto the right by `lamQ`'s self-dual reflection, so `Fline` is zeta's and no conductor summand or dual function appears, Chi/FullLine.lean's proof with `χ⁻¹` gone.
E12: `(1/2π) ∫ FlineQ = Σ_ρ m_ρ H(ρ) − H(0) − H(1)` along the good heights, Chi/FullLineAssembly.lean's proof with the two poles. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.Contour
import SIDEExplicitFormula.Schema.ZQ.EF.ZeroSum

open Complex Topology Filter Set MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

open Zeta23 Zeta23.WeilEF

theorem line_ne_one {c : ℝ} (hc : 1 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 1 := fun e => by
  have := congrArg Complex.re e
  simp at this
  linarith

theorem line_ne_zero {c : ℝ} (hc : 1 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := fun e => by
  have := congrArg Complex.re e
  simp at this
  linarith

/-- `Z_Q'/Z_Q` is bounded on `Re s = 3/2`, by the absolutely convergent series. -/
theorem norm_logDeriv_zqFn_line_le {c : ℝ} (hc : c = 3 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖logDeriv zqFn ((c : ℂ) + t * I)‖ ≤ M := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hre0 : (3 / 2 : ℝ) ≤ ((c : ℂ)).re := by simp [hc]
  have hsum : Summable (fun n : ℕ => ‖LSeries.term cC (c : ℂ) n‖) :=
    summable_norm_iff.mpr (cC_summable hre0)
  refine ⟨∑' n : ℕ, ‖LSeries.term cC (c : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre1 : 3 / 2 ≤ ((c : ℂ) + t * I).re := by rw [hre]; exact hc.ge
  have h1 : logDeriv zqFn ((c : ℂ) + t * I) = -LSeries cC ((c : ℂ) + t * I) := by
    have h := zq_logDeriv _ hre1
    have h' : LSeries cC ((c : ℂ) + t * I)
        = -(deriv zqFn ((c : ℂ) + t * I) / zqFn ((c : ℂ) + t * I)) := h
    rw [h', neg_neg, logDeriv_apply]
  have hnorm : ∀ n : ℕ, ‖LSeries.term cC ((c : ℂ) + t * I) n‖ = ‖LSeries.term cC (c : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term cC ((c : ℂ) + t * I) n‖) := by
    simp_rw [hnorm]; exact hsum
  rw [h1, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term cC ((c : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term cC ((c : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsum'
    _ = ∑' n, ‖LSeries.term cC (c : ℂ) n‖ := by simp_rw [hnorm]

/-- `‖Λ'/Λ(c+it)‖ ≤ A + B log(2+|t|)` on `c = 3/2`. -/
theorem norm_logDeriv_lamQ_line_le {c : ℝ} (hc : c = 3 / 2) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
    ∀ t : ℝ, ‖logDeriv lamQ ((c : ℂ) + t * I)‖ ≤ A + B * Real.log (2 + |t|) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zqFn_line_le hc
  obtain ⟨CG, hCG, hψ⟩ := GRHWeil.digamma_growth_strip_wide
  refine ⟨‖(Real.log lam : ℂ)‖ + M, CG, by positivity, hCG.le, fun t => ?_⟩
  have hre : ((c : ℂ) + t * I).re = c := by simp
  have him : ((c : ℂ) + t * I).im = t := by simp
  have hc1 : 1 < c := by rw [hc]; norm_num
  have hz := zq_ne_zero_of_three_halves_le ((c : ℂ) + t * I) (by rw [hre]; exact hc.ge)
  rw [logDeriv_lamQ (by rw [hre]; linarith) (line_ne_one hc1 t) hz]
  have hg := hψ ((c : ℂ) + t * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him] at hg
  calc ‖-(Real.log lam : ℂ) + Complex.digamma ((c : ℂ) + t * I) + logDeriv zqFn ((c : ℂ) + t * I)‖
      ≤ ‖-(Real.log lam : ℂ)‖ + ‖Complex.digamma ((c : ℂ) + t * I)‖ + ‖logDeriv zqFn ((c : ℂ) + t * I)‖ := norm_add₃_le
    _ ≤ ‖(Real.log lam : ℂ)‖ + CG * Real.log (2 + |t|) + M := by
        rw [norm_neg]
        exact add_le_add (add_le_add le_rfl hg) (hM t)
    _ = ‖(Real.log lam : ℂ)‖ + M + CG * Real.log (2 + |t|) := by ring

/-- `t ↦ Λ'/Λ(c+it)` is continuous on `c = 3/2`. -/
theorem continuous_logDeriv_lamQ_line {c : ℝ} (hc : c = 3 / 2) :
    Continuous (fun t : ℝ => logDeriv lamQ ((c : ℂ) + t * I)) := by
  have hc1 : 1 < c := by rw [hc]; norm_num
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : lamQ ((c : ℂ) + t * I) ≠ 0 :=
    lamQ_ne_zero_of_three_halves_le (by simpa using hc.ge)
  have han := lamQ_analyticAt (line_ne_zero hc1 t) (line_ne_one hc1 t)
  have : ContinuousAt (fun s => deriv lamQ s / lamQ s) ((c : ℂ) + t * I) :=
    han.deriv.continuousAt.div han.continuousAt hne
  show ContinuousAt ((fun s => deriv lamQ s / lamQ s) ∘ (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt

section Verticals

variable {k : ℝ → ℂ}

/-- **The full-line integrand for `lamQ`**: `(H(c+it) + H(1−c−it))·Λ'/Λ(c+it)`, the form of zeta's, `lamQ` being self-dual. -/
def FlineQ (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * logDeriv lamQ ((c : ℂ) + t * I)

/-- **Integrability of the full-line integrand.** -/
theorem integrable_FlineQ (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc : c = 3 / 2) :
    Integrable (FlineQ k c) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  have hb1 : ∀ t : ℝ, ‖Hfn k ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := fun t => hC c t (by linarith) (by linarith)
  have hb2 : ∀ t : ℝ, ‖Hfn k (1 - c - t * I)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast, neg_sq] at h2
    exact h2
  obtain ⟨A, B, hA, hB, hψ⟩ := norm_logDeriv_lamQ_line_le hc
  have i1 := GRHWeil.integrable_mul_of_decay_log (continuous_Hfn_line hk hkc c) hC0 hb1
    (continuous_logDeriv_lamQ_line hc) hA hB hψ
  have i2 := GRHWeil.integrable_mul_of_decay_log (continuous_Hfn_reflect hk hkc c) hC0 hb2
    (continuous_logDeriv_lamQ_line hc) hA hB hψ
  refine (i1.add i2).congr (Eventually.of_forall fun t => ?_)
  simp only [FlineQ, Pi.add_apply]
  ring

/-- **E11. The fold**: for every `R`, `V_f(c; −R, R) − V_f(1−c; −R, R) = I • ∫_{−R}^{R} FlineQ`, `f := H·Λ'/Λ`. -/
theorem zq_verticals_eq (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc : c = 3 / 2) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv lamQ s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv lamQ s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, FlineQ k c t := by
  have hc1 : 1 < c := by rw [hc]; norm_num
  have hLc := continuous_logDeriv_lamQ_line hc
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := continuous_Hfn_reflect hk hkc c
  -- the left-line integrand, pointwise, through the reflection
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * logDeriv lamQ (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * logDeriv lamQ ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hs, logDeriv_lamQ_one_sub (line_ne_zero hc1 (-y)) (line_ne_one hc1 (-y))]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * logDeriv lamQ ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * logDeriv lamQ ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hLc).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * logDeriv lamQ (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * logDeriv lamQ ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * logDeriv lamQ ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [FlineQ]
  ring

/-- the truncated integrals converge to the full-line integral along any `R_j → ∞`. -/
theorem tendsto_interval_FlineQ (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc : c = 3 / 2)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, FlineQ k c t) atTop (𝓝 (∫ t, FlineQ k c t)) := by
  have hRtop : Tendsto R atTop atTop := tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (integrable_FlineQ hk hkc hc)
    (tendsto_neg_atTop_atBot.comp hRtop) hRtop

end Verticals

/-- **E12. The full-line identity** at `c = 3/2` (`R → ∞` along the good heights; the horizontal pieces vanish). -/
theorem zq_full_line_identity {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc : c = 3 / 2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, FlineQ k c t
      = (∑' ρ : zqZeroConfig.carrier, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
  obtain ⟨Cg, hCg, R, hR⟩ := zq_good_heights
  set f : ℂ → ℂ := fun s => Hfn k s * logDeriv lamQ s with hf
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ zqZeroConfig.carrier ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = (∑ ρ ∈ Z, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
    intro j
    obtain ⟨h1', h2, h3⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact zq_rectangle_identity hk hkc hc (R := R j) (by linarith)
      (lamQ_ne_zero_on_horizontals hc.le (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := zq_horizontal_vanish hk hkc hc hCg hR
  have hZlim := zq_zero_sum_limit hk hkc (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := tendsto_interval_FlineQ hk hkc hc (R := R) (fun j => by linarith [(hR j).1])
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral f (1 - c) c (-(R j)) - HIntegral f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, FlineQ k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := zq_verticals_eq hk hkc hc (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, FlineQ k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  have hL' : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, FlineQ k c t)) :=
    hL.congr fun j => hE j
  exact tendsto_nhds_unique hL' ((hZlim.sub tendsto_const_nhds).sub tendsto_const_nhds)

end EF
end ZQ
end Schema
end SIDEExplicitFormula
