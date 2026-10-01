/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/GammaWide.lean
THIS PROGRAMME'S WORK (act b570, ruling (R180)(5)(a); W-ORD-GRH-WEIL, act five) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE Γℝ LOG-DERIVATIVE BOUND ON THE WIDER STRIP. For odd χ the Γ factor is `Γℝ(s + 1)`, so VerticalLine's Γ side asks the
bound `‖Γℝ'/Γℝ(σ + it)‖ ≪ log(2 + |t|)` on `3/2 ≤ σ ≤ 5/2`, beyond Zeta23's `norm_logDeriv_Gammaℝ_le` (`1/2 ≤ σ ≤ 3/2`;
b569's HOLD). Zeta23's own argument, run on the wider strip: (W1) the digamma growth on `1/4 ≤ Re s ≤ 2`; (W2) the Γℝ bound
on `3/2 ≤ σ ≤ 5/2`. Generated from the vendored file by relay data/b570_gen_gammawide.py.txt (the replacements printed
there); Zeta23's file is not edited. Nothing here is a statement about any zero.
-/
import Zeta23.WeilEF.VerticalLine

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

/-- **(W1)** Zeta23`s `digamma_growth_strip` (VerticalLine.lean :261) on the wider strip `1/4 ≤ Re s ≤ 2`: its proof, the
compact rectangle widened to `[1/4, 2] × [−1/2, 1/2]` and `‖s‖ ≤ 1 + |Im s|` to `‖s‖ ≤ 2 + |Im s|`. -/
theorem digamma_growth_strip_wide : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  -- differentiability of ψ on the right half-plane
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
    intro s hs
    have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re, Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hΓan : AnalyticAt ℂ Complex.Gamma s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m => ?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re, Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
    have hψan : AnalyticAt ℂ Complex.digamma s := by
      have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
      have h2 := h1.div hΓan hΓne
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def, logDeriv_apply]
        rfl)
    exact hψan.differentiableAt
  -- bound on the compact rectangle |Im| ≤ 1/2
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2))) := by
    intro s hs
    have hsre : 1/4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1/2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1, by positivity, fun s hre1 hre2 => ?_⟩
  have hlogmono : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    have := abs_nonneg s.im
    linarith
  have hlogpos : (0 : ℝ) < Real.log (2 + |s.im|) := lt_of_lt_of_le hlog2 hlogmono
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · -- compact part
    have hsK : s ∈ Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨hre1, hre2⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by
          field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul ?_ hlogmono hlog2.le (by positivity)
          calc M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) := le_max_left _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
  · -- Stirling part: ‖ψ‖ ≤ ‖ψ − log s + (1/2)/s‖ + ‖log s‖ + ‖(1/2)/s‖
    have hsre0 : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.StirlingVert.digamma_stirling (w := s) hsre0 (by linarith)
    have hsnorm_lo : (1/4 : ℝ) ≤ ‖s‖ :=
      le_trans hre1 (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have hsnorm0 : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm0
      exact lt_irrefl 0 hsnorm0
    have hsnorm_hi : ‖s‖ ≤ 2 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 2 + |s.im| := by
            have : |s.re| ≤ 2 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    -- ‖log s‖ ≤ |log ‖s‖| + π ≤ (log 4 + log(2+|im|)) + π
    have hlog_s : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have hlog_abs : |Real.log ‖s‖| ≤ Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · -- ‖s‖ ≤ 1-ish: |log| = −log ≤ log 4 since ‖s‖ ≥ 1/4
        have h1 : Real.log (1/4 : ℝ) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hsnorm_lo
        have h2 : Real.log (1/4 : ℝ) = -Real.log 4 := by
          rw [show (1/4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          have := abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) := by
          apply Real.log_le_log hsnorm0
          have := abs_nonneg s.im
          linarith
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have hinv_s : ‖(1/2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by
        rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1, div_le_iff₀ hsnorm0]
      linarith
    have him2 : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1/4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1/2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have htot : ‖Complex.digamma s‖
        ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s = (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
            + Complex.log s - (1/2 : ℂ) / s := by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                + Complex.log s - (1/2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s) + Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := by
              have := norm_add_le (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have hπ4 : Real.pi < 4 := Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
            have := hst
            linarith [hlog_s, hinv_s]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
            linarith [him2, hlog_abs]
        _ ≤ Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by linarith
    calc ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := htot
      _ ≤ Real.log (2 + |s.im|) + (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
          have h3 : K₀ / Real.log 2 * Real.log 2 ≤ K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
          have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
          linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul_of_nonneg_right ?_ hlogpos.le
          calc (1 + K₀ / Real.log 2) ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
                le_max_right _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith

/-- **(W2)** Zeta23`s `norm_logDeriv_Gammaℝ_le` (VerticalLine.lean :626) on `3/2 ≤ σ ≤ 5/2`: its proof, with (W1) at
`(σ + it)/2`, `3/4 ≤ σ/2 ≤ 5/4`. -/
theorem norm_logDeriv_Gammaℝ_le_wide : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 / 2 ≤ σ → σ ≤ 5 / 2 →
    ‖logDeriv Complex.Gammaℝ (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hψ⟩ := digamma_growth_strip_wide
  have hlogπ0 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨2 * Real.log Real.pi + C, by positivity, ?_⟩
  intro σ t h1 h2
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [Zeta23.WeilEF.logDeriv_Gammaℝ hre]
  have hs2 : ((σ : ℂ) + t * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hψb := hψ (((σ : ℂ) + t * I) / 2) (by rw [hs2]; simp; linarith) (by rw [hs2]; simp; linarith)
  have him : (((σ : ℂ) + t * I) / 2).im = t / 2 := by rw [hs2]; simp
  rw [him] at hψb
  have hlog2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2' : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hloght : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  have hlogπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖
      ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖ :=
        norm_add_le _ _
    _ = Real.log Real.pi / 2 + (1 / 2) * ‖Complex.digamma (((σ : ℂ) + t * I) / 2)‖ := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogπ, norm_mul]
        norm_num
    _ ≤ Real.log Real.pi / 2 + (1 / 2) * (C * Real.log (2 + |t / 2|)) := by gcongr
    _ ≤ Real.log Real.pi * Real.log (2 + |t|) * 2 + C * Real.log (2 + |t|) := by
        nlinarith [hC.le, hloght, Real.log_nonneg (show (1:ℝ) ≤ 2 + |t/2| by linarith [abs_nonneg (t/2)])]
    _ = (2 * Real.log Real.pi + C) * Real.log (2 + |t|) := by ring

end GRHWeil
end SIDEExplicitFormula
