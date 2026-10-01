/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/VerticalLine.lean
THIS PROGRAMME'S WORK (act b570, ruling (R180)(5)(b)-(c); W-ORD-GRH-WEIL, act five) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/VerticalLine.lean. (b) THE ODD-χ STEP RE-ATTEMPTED: the Γ factor `gammaFactor χ` is
`Γℝ(s)` for even χ and `Γℝ(s + 1)` for odd χ; its log-derivative bound on `1/2 ≤ σ ≤ 3/2` is Zeta23's
`norm_logDeriv_Gammaℝ_le` (even) and `norm_logDeriv_Gammaℝ_le_wide` of Chi/GammaWide.lean at `σ + 1` (odd). b569's attempt,
which asked Zeta23's bound at `σ + 1`, stays on grh-weil-b569-held.
Nothing here is a statement about any zero.
-/
import SIDEExplicitFormula.Chi.XiLogDeriv
import SIDEExplicitFormula.Chi.GammaWide

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- `logDeriv (fun s => f (s + 1)) z = logDeriv f (z + 1)`. -/
theorem logDeriv_comp_add_one (f : ℂ → ℂ) (z : ℂ) :
    logDeriv (fun s => f (s + 1)) z = logDeriv f (z + 1) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

omit [NeZero N] in
/-- **(b) THE ODD-χ STEP.** Growth of `gammaFactor χ'/gammaFactor χ` on `1/2 ≤ σ ≤ 3/2`: Zeta23's bound for even χ, the
wider-strip bound at `σ + 1` for odd χ. -/
theorem norm_logDeriv_gammaFactor_le (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖logDeriv (gammaFactor χ) (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C₁, hC₁, hG₁⟩ := Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le
  obtain ⟨C₂, _hC₂, hG₂⟩ := norm_logDeriv_Gammaℝ_le_wide
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun σ t h1 h2 => ?_⟩
  have hL : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  rcases χ.even_or_odd with he | ho
  · rw [show gammaFactor χ = Gammaℝ from funext he.gammaFactor_def]
    exact (hG₁ σ t h1 h2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hL)
  · rw [show gammaFactor χ = fun s => Gammaℝ (s + 1) from funext ho.gammaFactor_def, logDeriv_comp_add_one]
    have hs : (σ : ℂ) + t * I + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [hs]
    exact (hG₂ (σ + 1) t (by linarith) (by linarith)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL)

/-! ## (c) THE PRIME SIDE FOR χ (Zeta23's VerticalLine :100-:259, the coefficient `Λ(n)` replaced by `χ(n) Λ(n)`) -/

section PrimeSide

open MeasureTheory
open scoped ArithmeticFunction LSeries.notation

/-- On `1 < Re s`: `−L'/L(s, χ) = L(χΛ, s)` (Mathlib's `LSeries_twist_vonMangoldt_eq`, with `LFunction χ = L ↗χ` on the open
half-plane `1 < Re s`). -/
theorem neg_logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (LFunction χ) s = LSeries (↗χ * ↗Λ) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : LFunction χ =ᶠ[nhds s] LSeries ↗χ := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact LFunction_eq_LSeries χ hz
  rw [LSeries_twist_vonMangoldt_eq χ hs, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  ring

/-- Step 1 for χ (pointwise on the line `Re s = c > 1`). -/
theorem integrand_eq_tsum_chi {χ : DirichletCharacter ℂ N} {k : ℝ → ℂ} {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    Zeta23.WeilEF.Hfn k (c + t * I) * (-logDeriv (LFunction χ) (c + t * I))
      = ∑' n : ℕ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * LSeries.term (↗χ * ↗Λ) (c + t * I) n := by
  have hre : 1 < ((c : ℂ) + t * I).re := by simpa using hc1
  rw [Zeta23.WeilEF.Hfn_line, neg_logDeriv_LFunction_eq hre, LSeries, ← tsum_mul_left]

omit [NeZero N] in
/-- Step 2 for χ (the per-`n` line integral): `(1/2π)∫ paperFT(tilt k b) t · term_n(c + it) dt = χ(n)Λ(n) n^{−1/2} k(log n)`. -/
theorem per_n_line_integral_chi {χ : DirichletCharacter ℂ N} {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * LSeries.term (↗χ * ↗Λ) (c + t * I) n
      = (↗χ * ↗Λ) n * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    set a : ℂ := (↗χ * ↗Λ) n with ha
    have hterm : ∀ t : ℝ, LSeries.term (↗χ * ↗Λ) (c + t * I) n
        = a * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((c:ℂ) + t * I)) = (-(c:ℂ)) + (-(I * t)) := by ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n:ℂ) ^ (-(c:ℂ)) = (((n:ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl,
          show (-(c:ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hn0.le]
      have h2 : (n:ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2, ha]
      ring
    simp_rw [hterm]
    have hre : (fun t : ℝ => Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
        * (a * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => (a * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * (Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.cintegral_const_mul]
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((a * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * cexp (-I * t * Real.log n))
        = (a * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
            * cexp (-I * t * Real.log n)) from by ring]
    rw [Zeta23.WeilEF.tilted_inversion hk hkc (c - 1/2) (Real.log n)]
    have hexp : Real.exp ((c - 1/2) * Real.log n) = (n:ℝ) ^ (c - 1/2) := by
      rw [Real.rpow_def_of_pos hn0]
      ring_nf
    have hpow : ((n:ℝ) ^ (-c) : ℝ) * ((n:ℝ) ^ (c - 1/2) : ℝ) = ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hsqrt : ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    calc a * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * (k (Real.log n) * ((Real.exp ((c - 1/2) * Real.log n) : ℝ) : ℂ))
        = a * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * (k (Real.log n) * (((n:ℝ) ^ (c - 1/2) : ℝ) : ℂ)) := by rw [hexp]
      _ = a * ((((n:ℝ) ^ (-c) * (n:ℝ) ^ (c - 1/2)) : ℝ) : ℂ) * k (Real.log n) := by
          push_cast
          ring
      _ = a * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
          rw [hpow, hsqrt]

omit [NeZero N] in
/-- Step 3 for χ (the tsum/integral swap): dominated by `‖paperFT (tilt k b)‖ ∈ L¹ × Σ ‖χ(n)Λ(n)‖ n^{−c} < ∞`. -/
theorem line_integral_swap_chi {χ : DirichletCharacter ℂ N} {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * LSeries.term (↗χ * ↗Λ) (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * LSeries.term (↗χ * ↗Λ) (c + t * I) n := by
  have hkb2 : ContDiff ℝ 2 (Zeta23.WeilEF.tilt k (c - 1/2)) := Zeta23.WeilEF.tilt_contDiff hk _
  have hkbc : HasCompactSupport (Zeta23.WeilEF.tilt k (c - 1/2)) := Zeta23.WeilEF.tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hre : ∀ t : ℝ, ((c:ℂ) + t * I).re = c := by
    intro t
    simp
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n‖
      = if n = 0 then (0:ℝ) else ‖(↗χ * ↗Λ) n‖ * ((n:ℝ) ^ (-c)) := by
    intro n t
    rw [LSeries.norm_term_eq, hre, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ => LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
      * LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := if n = 0 then (0:ℝ) else ‖(↗χ * ↗Λ) n‖ * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [hnorm n t]
  have heval : ∀ n : ℕ, (∫ t : ℝ, ‖Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
      * LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n‖)
      = (∫ t : ℝ, ‖Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t‖)
        * (if n = 0 then (0:ℝ) else ‖(↗χ * ↗Λ) n‖ * ((n:ℝ) ^ (-c))) := by
    intro n
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_mul, hnorm n t]
  have hcn : Summable (fun n : ℕ => if n = 0 then (0:ℝ) else ‖(↗χ * ↗Λ) n‖ * ((n:ℝ) ^ (-c))) := by
    have hs : LSeriesSummable (↗χ * ↗Λ) (c : ℂ) := LSeriesSummable_twist_vonMangoldt χ (by simpa using hc1)
    have hns : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) (c : ℂ) n‖) := summable_norm_iff.mpr hs
    refine hns.congr fun n => ?_
    simpa using hnorm n 0
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
      * LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n‖) := by
    refine ((hcn.mul_left (∫ t : ℝ, ‖Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t‖)).congr fun n => ?_)
    rw [heval n]
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm

/-- **The prime side for χ on `Re s = c > 1`**: `(1/2π)∫ H(c + it)·(−L'/L)(c + it, χ) dt = Σ_n χ(n)Λ(n) n^{−1/2} k(log n)`. -/
theorem prime_side_line_chi {χ : DirichletCharacter ℂ N} {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Zeta23.WeilEF.Hfn k (c + t * I) * (-logDeriv (LFunction χ) (c + t * I))
      = ∑' n : ℕ, (↗χ * ↗Λ) n * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  have h1 : ∀ t : ℝ, Zeta23.WeilEF.Hfn k (c + t * I) * (-logDeriv (LFunction χ) (c + t * I))
      = ∑' n : ℕ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t * LSeries.term (↗χ * ↗Λ) (c + t * I) n :=
    fun t => integrand_eq_tsum_chi hc1 t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Zeta23.WeilEF.Hfn k (c + t * I) * (-logDeriv (LFunction χ) (c + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
          * LSeries.term (↗χ * ↗Λ) (c + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
          * LSeries.term (↗χ * ↗Λ) (c + t * I) n := by
        rw [line_integral_swap_chi hk hkc hc1]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Zeta23.paperFT (Zeta23.WeilEF.tilt k (c - 1/2)) t
          * LSeries.term (↗χ * ↗Λ) (c + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, (↗χ * ↗Λ) n * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => per_n_line_integral_chi hk hkc n

end PrimeSide

/-- `gammaFactor ψ` is analytic at every `s` with `0 < Re s`. -/
theorem analyticAt_gammaFactor (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (gammaFactor ψ) s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (differentiableAt_gammaFactor ψ hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

section GammaShift

open MeasureTheory Zeta23 Zeta23.WeilEF

/-- **(d) THE ARCHIMEDEAN LINE SHIFT FOR χ** -- Zeta23`s `gamma_line_shift` (VerticalLine.lean :659) with `Γℝ` replaced by
χ`s Γ factor `gammaFactor χ` (its bound: `norm_logDeriv_gammaFactor_le`, the odd case by the wider strip). Zeta23`s text:
**Archimedean line shift**: the Γℝ'/Γℝ-part of the two
vertical lines shifts to the critical line (rectangle with no poles of Γℝ'/Γℝ in Re s > 0,
horizontal pieces vanish by digamma growth × [eq:hfbound] decay of paperFT k). -/
theorem gamma_line_shift_chi (χ : DirichletCharacter ℂ N) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * logDeriv (gammaFactor χ) (c + t * I)
      = ∫ t : ℝ, paperFT k t
        * (logDeriv (gammaFactor χ) (1/2 + t * I) + logDeriv (gammaFactor χ) (1/2 - t * I)) := by
  set G := logDeriv (gammaFactor χ) with hG
  -- differentiability
  have hHd : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk.continuous hkc
    show Differentiable ℂ (fun s => paperFT k ((s - 1/2) / I))
    exact h.comp ((differentiable_id.sub_const _).div_const I)
  have hGd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s := by
    intro s hs
    have hA := analyticAt_gammaFactor χ hs
    have : G = fun z => deriv (gammaFactor χ) z / gammaFactor χ z := by funext z; rw [hG, logDeriv_apply]
    rw [this]
    exact hA.deriv.differentiableAt.div hA.differentiableAt (gammaFactor_ne_zero_of_re_pos χ hs)
  set f₁ : ℂ → ℂ := fun s => Hfn k s * G s with hf₁
  set f₂ : ℂ → ℂ := fun s => Hfn k (1 - s) * G s with hf₂
  have hf₁d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₁ s := fun s h1 _ =>
    (hHd s).mul (hGd s (by linarith))
  have hf₂d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₂ s := fun s h1 _ =>
    ((hHd (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)).mul (hGd s (by linarith))
  -- the majorant
  obtain ⟨Lam₁, hLam₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  set Lam : ℝ := max Lam₁ 0 with hLam
  have hLam0 : 0 ≤ Lam := le_max_right _ _
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam := fun u hu => (hLam₁ u hu).trans (le_max_left _ _)
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set N : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hN
  have hN0 : 0 ≤ N := add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨CG, hCG, hGb⟩ := norm_logDeriv_gammaFactor_le χ
  set M : ℝ := 2 * Real.exp Lam * N * CG * 6 with hM
  have hM0 : 0 ≤ M := by positivity
  set φ : ℝ → ℝ := fun t => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) with hφ
  have hφi : Integrable φ := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3/2)
      (by rw [Module.finrank_self]; norm_num)).const_mul M
    exact this
  have hφlim : Filter.Tendsto (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using h1.const_mul M
  have hφtop : Filter.Tendsto φ Filter.atTop (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atTop_atTop)
  have hφbot : Filter.Tendsto φ Filter.atBot (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atBot_atTop)
  -- the key pointwise bound: for |Im z| ≤ 1, ‖paperFT k z‖·‖G(σ+it)‖ ≤ φ t when Re z = ±t
  have hkey : ∀ (σ t : ℝ) (z : ℂ), 1 / 2 ≤ σ → σ ≤ c → |z.im| ≤ 1 → z.re ^ 2 = t ^ 2 →
      ‖paperFT k z‖ * ‖G (σ + t * I)‖ ≤ φ t := by
    intro σ t z h1 h2 hz hzt
    have hH := norm_paperFT_le_uniform hk hki hLam0 hsupp hz
    rw [hzt] at hH
    have hGG := hGb σ t h1 (by linarith)
    have hl := log_two_add_div_le (abs_nonneg t)
    calc ‖paperFT k z‖ * ‖G (σ + t * I)‖
        ≤ (2 * Real.exp Lam * N / (1 + t ^ 2)) * (CG * Real.log (2 + |t|)) :=
          mul_le_mul hH hGG (norm_nonneg _) (by positivity)
      _ = (2 * Real.exp Lam * N * CG) * (Real.log (2 + |t|) / (1 + |t| ^ 2)) := by
          rw [sq_abs]; ring
      _ ≤ (2 * Real.exp Lam * N * CG) * (6 * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = φ t := by simp only [hφ, hM, Real.norm_eq_abs]; ring
  -- z-bookkeeping for Hfn on the two lines
  have hz₁ : ∀ σ t : ℝ, ((σ : ℂ) + t * I - 1 / 2) / I = (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hz₂ : ∀ σ t : ℝ, ((1 - ((σ : ℂ) + t * I)) - 1 / 2) / I = ((-t : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hb₁ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₁ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₁, Hfn, norm_mul]
    rw [hz₁]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  have hb₂ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₂ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₂, Hfn, norm_mul]
    rw [hz₂]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  -- shift both lines
  have hab : (1:ℝ) / 2 ≤ c := by linarith
  have hs₁ := vertical_line_shift hab hf₁d hφi hb₁ hφtop hφbot
  have hs₂ := vertical_line_shift hab hf₂d hφi hb₂ hφtop hφbot
  -- integrability on the lines
  have hi₁c : Integrable (fun t : ℝ => f₁ (c + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp; linarith) (by simp)) hφi (fun t => hb₁ c t hab le_rfl)
  have hi₂c : Integrable (fun t : ℝ => f₂ (c + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp; linarith) (by simp)) hφi (fun t => hb₂ c t hab le_rfl)
  have hi₁h : Integrable (fun t : ℝ => f₁ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp) (by simp; linarith)) hφi (fun t => hb₁ (1/2) t le_rfl hab)
  have hi₂h : Integrable (fun t : ℝ => f₂ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp) (by simp; linarith)) hφi (fun t => hb₂ (1/2) t le_rfl hab)
  -- LHS = ∫ f₁(c+it) + ∫ f₂(c+it)
  have hL : ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * G (c + t * I)
      = (∫ t : ℝ, f₁ (c + t * I)) + ∫ t : ℝ, f₂ (c + t * I) := by
    rw [← integral_add hi₁c hi₂c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf₁, hf₂]
    rw [show (1 : ℂ) - (↑c + ↑t * I) = 1 - ↑c - ↑t * I by ring]
    ring
  rw [hL, hs₁, hs₂]
  -- evaluate on the critical line
  have e₁ : ∀ t : ℝ, f₁ ((1/2 : ℝ) + t * I) = paperFT k t * G (1/2 + t * I) := by
    intro t
    simp only [hf₁, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  have e₂ : ∀ t : ℝ, f₂ ((1/2 : ℝ) + t * I) = paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I) := by
    intro t
    simp only [hf₂, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  simp_rw [e₁, e₂]
  -- t ↦ −t in the second integral
  have hneg : ∫ t : ℝ, paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I)
      = ∫ t : ℝ, paperFT k t * G (1/2 - t * I) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    push_cast
    ring_nf
  rw [hneg, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  · have := hi₁h; simp_rw [e₁] at this; exact this
  · have := hi₂h; simp_rw [e₂] at this
    have h2 := this.comp_neg
    simp only [neg_neg] at h2
    refine (h2.congr (Filter.Eventually.of_forall fun t => ?_))
    push_cast; ring_nf

end GammaShift

end GRHWeil
end SIDEExplicitFormula
