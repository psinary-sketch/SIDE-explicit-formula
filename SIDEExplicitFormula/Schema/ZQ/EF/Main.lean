/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/Main.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt row E16, group H) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE FIELD. `zq_explicitFormula : ZQExplicitFormula zqZeroConfig (fun n => cQ n)`: for `k ∈ C_c²` even, `zeroSideQ zqZeroConfig k = poleTerm k − primeTermQ cQ k + archTermQ k`, assembled at `c = 3/2` from E12 (the full-line identity),
E13 (the prime line), E14 (the Gamma line), E15 (the bracket) and `conductor_line_shift`, Chi/Main.lean's `EF_lit_chi_holds` with the conductor's place taken by `−2 log(2π/√23)` and zeta's pole values. `k` even folds
`H(1−c−it)` onto `H(c+it)`. A field of a premise, proved as it stands: nothing here proves RH or GRH or locates any zero, and this theorem alone says nothing of the instance.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.FullLine
import SIDEExplicitFormula.Schema.ZQ.EF.Lines

open Complex Topology Filter Set MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

open Zeta23 Zeta23.WeilEF

/-- **E16. THE FIELD.** -/
theorem zq_explicitFormula : ZQExplicitFormula zqZeroConfig (fun n => cQ n) := by
  refine ⟨fun k hk hkc heven => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 3 / 2 := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℂ, l = -(2 * (Real.log lam : ℂ)) := ⟨_, rfl⟩
  have hc1 : 1 < c := by rw [hc]; norm_num
  have hc2 : c ≤ 3 / 2 := hc.le
  have hmir : (fun u => k (-u)) = k := funext heven
  have hrefl : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn k ((c : ℂ) + t * I) := fun t => by
    rw [Hfn_mirror k c t, hmir]
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  have hb1 : ∀ t : ℝ, ‖Hfn k ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := fun t => hC c t (by linarith) (by linarith)
  have hb2 : ∀ t : ℝ, ‖Hfn k (1 - c - t * I)‖ ≤ C / (1 + t ^ 2) := fun t => by
    rw [hrefl]
    exact hb1 t
  have hH1c : Continuous (fun t : ℝ => Hfn k ((c : ℂ) + t * I)) := continuous_Hfn_line hk hkc c
  have hH2c : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := continuous_Hfn_reflect hk hkc c
  -- the split of the line's logarithmic derivative
  have hsplitL : ∀ t : ℝ, logDeriv lamQ ((c : ℂ) + t * I)
      = -(Real.log lam : ℂ) + Complex.digamma ((c : ℂ) + t * I) + logDeriv zqFn ((c : ℂ) + t * I) := fun t =>
    logDeriv_lamQ (by simp; linarith) (line_ne_one hc1 t)
      (zq_ne_zero_of_three_halves_le _ (by simpa using hc.ge))
  have hF : ∀ t : ℝ, FlineQ k c t
      = (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * Complex.digamma ((c : ℂ) + t * I)
        + 2 * (Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I))
        + Hfn k ((c : ℂ) + t * I) * l := by
    intro t
    simp only [FlineQ]
    rw [hsplitL t, hrefl t, hl]
    ring
  -- integrability of the parts
  obtain ⟨CG, hCG, hψ⟩ := GRHWeil.digamma_growth_strip_wide
  have hPc : Continuous (fun t : ℝ => Complex.digamma ((c : ℂ) + t * I)) :=
    continuous_digamma_comp (by fun_prop) (fun t => by simp; linarith)
  have hPb : ∀ t : ℝ, ‖Complex.digamma ((c : ℂ) + t * I)‖ ≤ CG * Real.log (2 + |t|) := fun t => by
    have h := hψ ((c : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
    rw [show ((c : ℂ) + t * I).im = t by simp] at h
    exact h
  have iG : Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
      * Complex.digamma ((c : ℂ) + t * I)) := by
    refine GRHWeil.integrable_mul_of_decay_log (hH1c.add hH2c) (C := 2 * C) (by positivity) (fun t => ?_)
      hPc le_rfl hCG.le (fun t => by rw [zero_add]; exact hPb t)
    calc ‖Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)‖
        ≤ ‖Hfn k ((c : ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add (hb1 t) (hb2 t)
      _ = 2 * C / (1 + t ^ 2) := by ring
  have hLzc : Continuous (fun t : ℝ => logDeriv zqFn ((c : ℂ) + t * I)) := by
    have h3 : Continuous (fun t : ℝ => logDeriv lamQ ((c : ℂ) + t * I) + (Real.log lam : ℂ)
        - Complex.digamma ((c : ℂ) + t * I)) :=
      ((continuous_logDeriv_lamQ_line hc).add continuous_const).sub hPc
    refine h3.congr fun t => ?_
    show logDeriv lamQ ((c : ℂ) + t * I) + (Real.log lam : ℂ) - Complex.digamma ((c : ℂ) + t * I)
      = logDeriv zqFn ((c : ℂ) + t * I)
    rw [hsplitL t]
    ring
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zqFn_line_le hc
  have iP : Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I)) :=
    GRHWeil.integrable_mul_of_decay_log hH1c hC0 hb1 hLzc hM0 le_rfl
      (fun t => by rw [zero_mul, add_zero]; exact hM t)
  have i2P : Integrable (fun t : ℝ => 2 * (Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I))) :=
    iP.const_mul 2
  have iL : Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * l) :=
    GRHWeil.integrable_mul_of_decay_log (ψ := fun _ : ℝ => l) hH1c hC0 hb1 continuous_const
      (norm_nonneg l) le_rfl (fun t => by simp)
  -- the full-line integral split
  have hsplit : ∫ t : ℝ, FlineQ k c t
      = (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * Complex.digamma ((c : ℂ) + t * I))
        + 2 * (∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I))
        + ∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * l := by
    have i12 : Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * Complex.digamma ((c : ℂ) + t * I)
        + 2 * (Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I))) := iG.add i2P
    rw [integral_congr_ae (Eventually.of_forall hF), integral_add i12 iL, integral_add iG i2P,
      integral_const_mul]
  -- the Gamma part
  have eG := zq_gamma_line_shift hk hkc hc1 hc2
  -- the constant part, on the critical line
  have eN : (∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * l) = (∫ r : ℝ, paperFT k r) * l := by
    rw [integral_mul_const, ← GRHWeil.conductor_line_shift hk hkc (c := c) (by linarith) (by linarith)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => (hrefl t).symm)
  -- the prime line
  have ePr := zq_prime_side_line hk hkc (c := c) hc.ge
  have h2 : (∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv zqFn (c + t * I)))
      = -∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * logDeriv zqFn ((c : ℂ) + t * I) := by
    rw [← integral_neg]
    congr 1
    funext t
    ring
  rw [h2] at ePr
  have eS : primeTermQ (fun n => cQ n) k
      = 2 * ∑' n : ℕ, cC n * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
    unfold primeTermQ
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [cC]
    push_cast
    ring
  -- the archimedean side
  have hcont_h : Continuous (fun r : ℝ => paperFT k r) :=
    (differentiable_paperFT hk.continuous hkc).continuous.comp Complex.continuous_ofReal
  have hbh : ∀ r : ℝ, ‖paperFT k r‖ ≤ C / (1 + r ^ 2) := fun r => by
    rw [GRHWeil.paperFT_eq_Hfn_half]
    exact hC _ r (by norm_num) (by norm_num)
  have hcp : Continuous (fun r : ℝ => (1 / 2 : ℂ) + r * I) := by fun_prop
  have hcm : Continuous (fun r : ℝ => (1 / 2 : ℂ) - r * I) := by fun_prop
  have hPp := continuous_digamma_comp hcp (fun r => by norm_num)
  have hPm := continuous_digamma_comp hcm (fun r => by norm_num)
  have hψb : ∀ r : ℝ, ‖Complex.digamma (1 / 2 + r * I) + Complex.digamma (1 / 2 - r * I)‖
      ≤ 0 + 2 * CG * Real.log (2 + |r|) := by
    intro r
    have rp : ((1 / 2 : ℂ) + r * I).re = 1 / 2 := by norm_num
    have rm : ((1 / 2 : ℂ) - r * I).re = 1 / 2 := by norm_num
    have ip : ((1 / 2 : ℂ) + r * I).im = r := by norm_num
    have im : ((1 / 2 : ℂ) - r * I).im = -r := by norm_num
    have h1 := hψ ((1 / 2 : ℂ) + r * I) (by rw [rp]; norm_num) (by rw [rp]; norm_num)
    have h3 := hψ ((1 / 2 : ℂ) - r * I) (by rw [rm]; norm_num) (by rw [rm]; norm_num)
    rw [ip] at h1
    rw [im, abs_neg] at h3
    calc ‖Complex.digamma (1 / 2 + r * I) + Complex.digamma (1 / 2 - r * I)‖
        ≤ ‖Complex.digamma (1 / 2 + r * I)‖ + ‖Complex.digamma (1 / 2 - r * I)‖ := norm_add_le _ _
      _ ≤ CG * Real.log (2 + |r|) + CG * Real.log (2 + |r|) := add_le_add h1 h3
      _ = 0 + 2 * CG * Real.log (2 + |r|) := by ring
  have iΓh : Integrable (fun r : ℝ => paperFT k r
      * (Complex.digamma (1 / 2 + r * I) + Complex.digamma (1 / 2 - r * I))) :=
    GRHWeil.integrable_mul_of_decay_log hcont_h hC0 hbh (hPp.add hPm) le_rfl
      (by positivity : (0 : ℝ) ≤ 2 * CG) hψb
  have iNh : Integrable (fun r : ℝ => paperFT k r * l) :=
    GRHWeil.integrable_mul_of_decay_log (ψ := fun _ : ℝ => l) hcont_h hC0 hbh continuous_const
      (norm_nonneg l) le_rfl (fun r => by simp)
  have hbr : ∀ r : ℝ, paperFT k r * (bracketQ r : ℂ)
      = paperFT k r * (Complex.digamma (1 / 2 + r * I) + Complex.digamma (1 / 2 - r * I))
        + paperFT k r * l := by
    intro r
    rw [← zq_bracket r, hl]
    ring
  have hcast : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by simp
  have earch : archTermQ k
      = (1 / (2 * Real.pi) : ℂ) * ((∫ r : ℝ, paperFT k r
          * (Complex.digamma (1 / 2 + r * I) + Complex.digamma (1 / 2 - r * I)))
        + (∫ r : ℝ, paperFT k r) * l) := by
    unfold archTermQ
    rw [hcast, integral_congr_ae (Eventually.of_forall hbr), integral_add iΓh iNh, integral_mul_const]
  -- pole values
  have hpole0 : Hfn k 0 = paperFT k (I / 2) := by
    unfold Hfn
    congr 1
    rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have hpole1 : Hfn k 1 = paperFT k (-I / 2) := by
    unfold Hfn
    congr 1
    rw [div_eq_iff Complex.I_ne_zero]
    rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]
    norm_num
  -- assemble
  have hfull := zq_full_line_identity hk hkc hc
  rw [hsplit, eG, eN] at hfull
  have hzero : zeroSideQ zqZeroConfig k
      = ∑' ρ : zqZeroConfig.carrier, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ := rfl
  rw [hzero, eS, earch]
  unfold poleTerm
  rw [← hpole0, ← hpole1]
  linear_combination -hfull - 2 * ePr

/-- **THE FIVE FIELDS TOGETHER**: `ZQPremises` at `zqFn`, `zqZeroConfig`, `cQ`, each field its compiled theorem. -/
theorem zq_premises : ZQPremises zqFn zqZeroConfig (fun n => cQ n) :=
  ⟨zq_continuation, zq_zeros, zq_logDeriv, zq_explicitFormula, zq_count_holds⟩

/-- `zq_count` at the instance, binding no premise. -/
theorem zq_count_instance : ∃ A₀ : ℝ, Wide.HCount zqZeroConfig A₀ :=
  zq_count zq_premises

/-- `zq_explicit_formula` at the instance, binding no premise. -/
theorem zq_explicit_formula_instance (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    (he : ∀ x : ℝ, k (-x) = k x) :
    zeroSideQ zqZeroConfig k = poleTerm k - primeTermQ (fun n => cQ n) k + archTermQ k :=
  zq_explicit_formula zq_premises k hk hs he

/-- `zq_li_nonneg_imp_online` at the instance, binding no premise: the implication, its hypothesis the Li positivity of the
configuration, which nothing here proves; no zero is located. -/
theorem zq_li_nonneg_imp_online_instance :
    (∀ n : ℕ, 0 ≤ Wide.liCoeff zqZeroConfig n) → ∀ ρ ∈ zqZeroConfig.carrier, ρ.re = 1 / 2 :=
  zq_li_nonneg_imp_online zq_premises

end EF
end ZQ
end Schema
end SIDEExplicitFormula
