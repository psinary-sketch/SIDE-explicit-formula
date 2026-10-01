/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/FullLine.lean
THIS PROGRAMME'S WORK (act b571, ruling (R181)(4)(a)-(b); W-ORD-GRH-WEIL, act six) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/FullLine.lean, RESTATED AT χ⁻¹ WITH THE CONDUCTOR. Zeta23 folds the left vertical side of the
rectangle onto the right line by `Λ'/Λ(1 − s) = −Λ'/Λ(s)`. For primitive `χ ≠ 1` the compiled identity is
`Λ'/Λ(1 − s, χ) = −(log N + Λ'/Λ(s, χ⁻¹))` (Chi/XiLogDeriv.lean, `logDeriv_completedLFunction_one_sub`), so the left line's
integrand at `χ` is `−log N` minus the right line's integrand at `χ⁻¹`, and the full-line integrand is
  `Fline_chi χ k c t = H(c+it)·Λ'/Λ(c+it, χ) + H(1−c−it)·Λ'/Λ(c+it, χ⁻¹) + H(1−c−it)·log N`,
the last summand -- the conductor term, `FlineCond_chi` -- its own term. The heights lemma reflects the left half of a horizontal
side onto `Λ(·, χ⁻¹)` and carries the nonvanishing back to `L(·, χ)` by b562's pairing (`LFunction_inv_conj`).
Nothing here locates any zero of any `L(s, χ)`.
-/
import SIDEExplicitFormula.Chi.Contour

open Complex Topology Filter Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF
open scoped ArithmeticFunction LSeries.notation

variable {N : ℕ} [NeZero N]

/-! ## The line facts -/

section LineFacts

/-- On `re = c > 1`: `Λ'/Λ(·, χ) = gammaFactor'/gammaFactor + L'/L`. -/
theorem logDeriv_completedLFunction_line {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    logDeriv (completedLFunction χ) ((c : ℂ) + t * I)
      = logDeriv (gammaFactor χ) ((c : ℂ) + t * I) + logDeriv (LFunction χ) ((c : ℂ) + t * I) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  exact logDeriv_completedLFunction h1 _ (LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (by rw [hre]; linarith))
    (by rw [hre]; linarith)

/-- **`L'/L(·, χ)` is bounded on vertical lines to the right of 1**: `‖L'/L(c+it, χ)‖ ≤ Σ ‖χ(n)Λ(n) n^{−c}‖`. -/
theorem norm_logDeriv_LFunction_le_of_one_lt_re (χ : DirichletCharacter ℂ N) {c : ℝ} (hc1 : 1 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖logDeriv (LFunction χ) ((c : ℂ) + t * I)‖ ≤ M := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) (c : ℂ) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ (s := (c : ℂ)) (by simpa using hc1))
  refine ⟨∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) (c : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre1 : 1 < ((c : ℂ) + t * I).re := by rw [hre]; exact hc1
  have h1 : logDeriv (LFunction χ) ((c : ℂ) + t * I) = -LSeries (↗χ * ↗Λ) ((c : ℂ) + t * I) := by
    rw [← neg_logDeriv_LFunction_eq hre1, neg_neg]
  have hnorm : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗Λ) ((c : ℂ) + t * I) n‖ = ‖LSeries.term (↗χ * ↗Λ) (c : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) ((c : ℂ) + t * I) n‖) := by
    simp_rw [hnorm]; exact hsum
  rw [h1, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term (↗χ * ↗Λ) ((c : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) ((c : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsum'
    _ = ∑' n, ‖LSeries.term (↗χ * ↗Λ) (c : ℂ) n‖ := by simp_rw [hnorm]

/-- `t ↦ Λ'/Λ(c+it, χ)` is continuous for `c ≥ 1` (`Λ(·, χ)` entire and nonvanishing on `re ≥ 1`). -/
theorem continuous_logDeriv_completedLFunction_line {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {c : ℝ} (hc1 : 1 ≤ c) :
    Continuous (fun t : ℝ => logDeriv (completedLFunction χ) ((c : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : completedLFunction χ ((c : ℂ) + t * I) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re h1 (by simpa using hc1)
  have han := analyticAt_completedLFunction h1 ((c : ℂ) + t * I)
  have : ContinuousAt (fun s => deriv (completedLFunction χ) s / completedLFunction χ s) ((c : ℂ) + t * I) :=
    han.deriv.continuousAt.div han.continuousAt hne
  show ContinuousAt ((fun s => deriv (completedLFunction χ) s / completedLFunction χ s) ∘
    (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt

/-- generic: a continuous `φ` with `‖φ(t)‖ ≤ C/(1+t²)` times a continuous `ψ` with `‖ψ(t)‖ ≤ A + B log(2+|t|)` is
integrable -- Zeta23's `integrable_mul_logDeriv_Gammaℝ_of_decay` (FullLine.lean :227) with the bound as a hypothesis. -/
theorem integrable_mul_of_decay_log {φ ψ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) (hψc : Continuous ψ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hψ : ∀ t, ‖ψ t‖ ≤ A + B * Real.log (2 + |t|)) :
    Integrable (fun t : ℝ => φ t * ψ t) := by
  set K : ℝ := C * (A + 5 * B) with hK
  have hmaj : Integrable (fun t : ℝ => K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K
  refine Integrable.mono' hmaj (hφc.mul hψc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hq : 0 < (1 + t ^ 2 : ℝ) := by positivity
  have hone : (1 : ℝ) ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  have hlog : Real.log (2 + |t|) ≤ 5 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    have := log_two_add_le (abs_nonneg t)
    rwa [sq_abs] at this
  have hL : ‖ψ t‖ ≤ (A + 5 * B) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    calc ‖ψ t‖ ≤ A + B * Real.log (2 + |t|) := hψ t
      _ ≤ A * (1 + t ^ 2) ^ (1 / 4 : ℝ) + B * (5 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) := by
          apply add_le_add
          · nlinarith
          · exact mul_le_mul_of_nonneg_left hlog hB
      _ = (A + 5 * B) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by ring
  rw [norm_mul]
  have hpow : (C / (1 + t ^ 2)) * ((A + 5 * B) * (1 + t ^ 2) ^ (1 / 4 : ℝ))
      = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.norm_eq_abs, sq_abs, hK]
    have e : (1 + t ^ 2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
      rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq, Real.rpow_one]
    rw [e]
    field_simp
  calc ‖φ t‖ * ‖ψ t‖ ≤ (C / (1 + t ^ 2)) * ((A + 5 * B) * (1 + t ^ 2) ^ (1 / 4 : ℝ)) :=
        mul_le_mul (hC t) hL (norm_nonneg _) (by positivity)
    _ = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := hpow

/-- `‖Λ'/Λ(c+it, χ)‖ ≤ M + C_G log(2+|t|)` on `re = c ∈ (1, 3/2]`. -/
theorem norm_logDeriv_completedLFunction_line_le {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {c : ℝ} (hc1 : 1 < c)
    (hc2 : c ≤ 3 / 2) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ t : ℝ, ‖logDeriv (completedLFunction χ) ((c : ℂ) + t * I)‖ ≤ A + B * Real.log (2 + |t|) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_LFunction_le_of_one_lt_re χ hc1
  obtain ⟨CG, hCG, hG⟩ := norm_logDeriv_gammaFactor_le χ
  refine ⟨M, CG, hM0, hCG.le, fun t => ?_⟩
  rw [logDeriv_completedLFunction_line h1 hc1 t]
  calc ‖logDeriv (gammaFactor χ) ((c : ℂ) + t * I) + logDeriv (LFunction χ) ((c : ℂ) + t * I)‖
      ≤ ‖logDeriv (gammaFactor χ) ((c : ℂ) + t * I)‖ + ‖logDeriv (LFunction χ) ((c : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ CG * Real.log (2 + |t|) + M := add_le_add (hG c t (by linarith) hc2) (hM t)
    _ = M + CG * Real.log (2 + |t|) := by ring

end LineFacts

/-! ## Good heights: the horizontals avoid the zeros of `Λ(·, χ)` -/

section Heights

/-- **Nonvanishing of `Λ(·, χ)` on the horizontal sides** `im = ±R`, `1−c ≤ re ≤ c`, given `L(·, χ) ≠ 0` on `im = ±R`,
`1/2 ≤ re ≤ 2`. The left half reflects by the functional equation onto `Λ(1 − s, χ⁻¹)`, and `L(1 − s, χ⁻¹)` is
`conj L(conj (1 − s), χ)` by b562's pairing, `conj (1 − s)` lying on the same horizontal. -/
theorem completedLFunction_ne_zero_on_horizontals_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℝ}
    (hL : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 → LFunction χ s ≠ 0) :
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → completedLFunction χ s ≠ 0 := by
  intro s him hr1 hr2
  rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
  · intro h0
    exact hL s him hre (by linarith) ((completedLFunction_eq_zero_iff_of_re_pos h1 (by linarith)).mp h0)
  · have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
    have hFE := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hFE
    rw [hFE]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    refine mul_ne_zero (mul_ne_zero (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1)
      (rootNumber_ne_zero hχ h1)) ?_
    have hw : 0 < (1 - s).re := by simp; linarith
    intro h0
    have hL0 : LFunction χ⁻¹ (1 - s) = 0 := (completedLFunction_eq_zero_iff_of_re_pos hinv1 hw).mp h0
    have hpair := LFunction_inv_conj h1 (conj (1 - s))
    rw [Complex.conj_conj, hL0] at hpair
    have hz : LFunction χ (conj (1 - s)) = 0 := by
      have := hpair.symm
      rwa [map_eq_zero] at this
    refine hL (conj (1 - s)) ?_ (by simp; linarith) (by simp; linarith) hz
    simp only [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub, neg_neg]
    exact him

end Heights

/-! ## The vertical sides, folded at `χ⁻¹` with the conductor -/

section Verticals

variable {k : ℝ → ℂ}

/-- **THE CONDUCTOR TERM**, its own summand of the full-line integrand: `H(1 − c − it)·log N`. -/
def FlineCond_chi (N : ℕ) (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  Hfn k (1 - c - t * I) * Complex.log N

/-- **The full-line integrand for χ**: `H(c+it)·Λ'/Λ(c+it, χ) + H(1−c−it)·Λ'/Λ(c+it, χ⁻¹) + H(1−c−it)·log N`. -/
def Fline_chi (χ : DirichletCharacter ℂ N) (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  Hfn k ((c : ℂ) + t * I) * logDeriv (completedLFunction χ) ((c : ℂ) + t * I)
    + Hfn k (1 - c - t * I) * logDeriv (completedLFunction χ⁻¹) ((c : ℂ) + t * I)
    + FlineCond_chi N k c t

/-- **Integrability of the full-line integrand for χ.** -/
theorem integrable_Fline_chi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) : Integrable (Fline_chi χ k c) := by
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  have hb1 : ∀ t : ℝ, ‖Hfn k ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := fun t => hC c t (by linarith) (by linarith)
  have hb2 : ∀ t : ℝ, ‖Hfn k (1 - c - t * I)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast, neg_sq] at h2
    exact h2
  obtain ⟨A₁, B₁, hA₁, hB₁, hψ₁⟩ := norm_logDeriv_completedLFunction_line_le h1 hc1 hc2
  obtain ⟨A₂, B₂, hA₂, hB₂, hψ₂⟩ := norm_logDeriv_completedLFunction_line_le hinv1 hc1 hc2
  have i1 := integrable_mul_of_decay_log (continuous_Hfn_line hk hkc c) hC0 hb1
    (continuous_logDeriv_completedLFunction_line h1 hc1.le) hA₁ hB₁ hψ₁
  have i2 := integrable_mul_of_decay_log (continuous_Hfn_reflect hk hkc c) hC0 hb2
    (continuous_logDeriv_completedLFunction_line hinv1 hc1.le) hA₂ hB₂ hψ₂
  have i3 := integrable_mul_of_decay_log (ψ := fun _ : ℝ => Complex.log (N : ℂ)) (continuous_Hfn_reflect hk hkc c) hC0 hb2
    continuous_const (norm_nonneg (Complex.log (N : ℂ))) le_rfl (fun t => by simp)
  refine ((i1.add i2).add i3).congr (Eventually.of_forall fun t => ?_)
  simp only [Fline_chi, FlineCond_chi, Pi.add_apply]

/-- **THE FOLD AT `χ⁻¹`**: for every `R`, `V_f(c; −R, R) − V_f(1−c; −R, R) = I • ∫_{−R}^{R} Fline_chi`, `f := H·Λ'/Λ(·, χ)`:
the left line's integrand is `−(H(1−c−i(−y))·(log N + Λ'/Λ(c+i(−y), χ⁻¹)))`, then `y ↦ −y`. -/
theorem verticals_eq_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (_hc2 : c ≤ 3 / 2) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv (completedLFunction χ) s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv (completedLFunction χ) s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, Fline_chi χ k c t := by
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  set Lχ := logDeriv (completedLFunction χ) with hLχ
  set Lι := logDeriv (completedLFunction χ⁻¹) with hLι
  have hLχc : Continuous (fun t : ℝ => Lχ ((c : ℂ) + t * I)) := continuous_logDeriv_completedLFunction_line h1 hc1.le
  have hLιc : Continuous (fun t : ℝ => Lι ((c : ℂ) + t * I)) := continuous_logDeriv_completedLFunction_line hinv1 hc1.le
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := continuous_Hfn_reflect hk hkc c
  -- the left-line integrand, pointwise, through the compiled identity
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * Lχ (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * (Complex.log N + Lι ((c : ℂ) + ((-y : ℝ) : ℂ) * I))) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    have hne : completedLFunction χ⁻¹ ((c : ℂ) + ((-y : ℝ) : ℂ) * I) ≠ 0 :=
      completedLFunction_ne_zero_of_one_le_re hinv1 (by simp; linarith)
    rw [hs, hLχ, logDeriv_completedLFunction_one_sub hχ h1 _ hne]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * Lχ ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLχc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * (Complex.log N + Lι ((c : ℂ) + t * I)))
      volume (-R) R := (hH2.mul (continuous_const.add hLιc)).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * Lχ (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * (Complex.log N + Lι ((c : ℂ) + t * I)) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * (Complex.log N + Lι ((c : ℂ) + t * I)))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Fline_chi, FlineCond_chi, hLχ, hLι]
  ring

/-- the truncated integrals converge to the full-line integral along any `R_j → ∞`. -/
theorem tendsto_interval_Fline_chi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, Fline_chi χ k c t) atTop (𝓝 (∫ t, Fline_chi χ k c t)) := by
  have hRtop : Tendsto R atTop atTop := tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (integrable_Fline_chi h1 hk hkc hc1 hc2)
    (tendsto_neg_atTop_atBot.comp hRtop) hRtop

end Verticals

end GRHWeil
end SIDEExplicitFormula
