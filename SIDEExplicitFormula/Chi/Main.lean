/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/Main.lean
THIS PROGRAMME'S WORK (act b571, ruling (R181)(4)(c)-(d); W-ORD-GRH-WEIL, act six) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/Main.lean: the final assembly of `EF_lit_chi` (Chi/Statement.lean). At `c = 5/4` the full-line
identity for χ (Chi/FullLineAssembly) splits, by `Λ'/Λ = gammaFactor'/gammaFactor + L'/L` on `re = c` for `χ` and for `χ⁻¹`
(whose Γ factor is `χ`'s, the parities agreeing), into four parts:
* the Γ part `∫ [H(c+it) + H(1−c−it)]·gammaFactor'/gammaFactor(c+it)`, shifted to the critical line (`gamma_line_shift_chi`) and
  evaluated by the bracket `gammaFactor_bracket`: `(1/2π)∫ h(r)[Re ψ(1/4 + a/2 + ir/2) − log π] dr`;
* the prime line at `χ`: `−Σ Λ(n) n^{−1/2} χ(n) k(log n)` (`prime_side_line_chi`);
* the prime line at `χ⁻¹`, the test function mirrored (`Hfn_mirror`): `−Σ Λ(n) n^{−1/2} conj χ(n) k(−log n)`, since
  `χ⁻¹(n) = conj χ(n)`;
* THE CONDUCTOR TERM `log N · ∫ H(1−c−it) dt`, shifted to the critical line by Zeta23's `vertical_line_shift`:
  `log N · (1/2π)∫ h(r) dr` -- on the archimedean side, where with the Γ part's `−log π` it makes the bracket's `log(N/π)`.
The zero side is `Σ_ρ m_ρ H(ρ) = Σ_ρ m_ρ h(γ_ρ)`; no pole terms. Nothing here proves GRH or locates any zero of any `L(s, χ)`.
-/
import SIDEExplicitFormula.Chi.FullLineAssembly
import SIDEExplicitFormula.Chi.Statement
import Zeta23.WeilEF.Main

open Complex Topology Filter Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF
open scoped ArithmeticFunction LSeries.notation

variable {N : ℕ} [NeZero N]

/-! ## The pair's characters: parity and values -/

section Pair

omit [NeZero N] in
/-- `χ⁻¹` is even iff `χ` is (`χ⁻¹(−1) = conj χ(−1)`). -/
theorem even_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Even ↔ χ.Even := by
  show χ⁻¹ (-1) = 1 ↔ χ (-1) = 1
  rw [← MulChar.star_apply']
  constructor
  · intro h
    have := congrArg star h
    rwa [star_star, star_one] at this
  · intro h
    rw [h, star_one]

omit [NeZero N] in
/-- `χ⁻¹`'s Γ factor is `χ`'s. -/
theorem gammaFactor_inv (χ : DirichletCharacter ℂ N) : gammaFactor χ⁻¹ = gammaFactor χ := by
  funext s
  by_cases h : χ.Even
  · rw [h.gammaFactor_def, ((even_inv_iff χ).mpr h).gammaFactor_def]
  · have h' : ¬ χ⁻¹.Even := fun h'' => h ((even_inv_iff χ).mp h'')
    unfold gammaFactor
    simp [h, h']

omit [NeZero N] in
/-- `χ⁻¹(n) = conj χ(n)`. -/
theorem inv_apply_natCast (χ : DirichletCharacter ℂ N) (n : ℕ) : χ⁻¹ (n : ZMod N) = conj (χ (n : ZMod N)) := by
  rw [← MulChar.star_apply']
  rfl

end Pair

/-! ## The critical-line bracket for `χ`'s Γ factor -/

section Bracket

/-- `w = a + bi` with `4a ∈ {1, 3}` is off the integers. -/
theorem mem_integerComplement_quarter {a : ℝ} (ha : 4 * a = 1 ∨ 4 * a = 3) (b : ℝ) :
    ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hre := congrArg Complex.re hm
  simp at hre
  have h4 : (4 : ℝ) * m = 4 * a := by rw [hre]
  rcases ha with h | h
  · have : (4 * m : ℤ) = 1 := by exact_mod_cast h4.trans h
    omega
  · have : (4 * m : ℤ) = 3 := by exact_mod_cast h4.trans h
    omega

/-- `Γℝ'/Γℝ(σ+it) + Γℝ'/Γℝ(σ−it) = Re ψ(σ/2 + it/2) − log π` (Zeta23's `gammaR_bracket` at a general `σ > 0`). -/
theorem logDeriv_Gammaℝ_bracket {σ : ℝ} (hσ : 0 < σ) (t : ℝ)
    (hw : ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I ∈ Complex.integerComplement) :
    logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I) + logDeriv Complex.Gammaℝ ((σ : ℂ) - t * I)
      = (((Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re - Real.log Real.pi : ℝ) : ℂ) := by
  have hp : 0 < ((σ : ℂ) + t * I).re := by simp; exact hσ
  have hm : 0 < ((σ : ℂ) - t * I).re := by simp; exact hσ
  rw [logDeriv_Gammaℝ hp, logDeriv_Gammaℝ hm]
  set w : ℂ := ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I with hwdef
  have e1 : ((σ : ℂ) + t * I) / 2 = w := by rw [hwdef]; push_cast; ring
  have e2 : ((σ : ℂ) - t * I) / 2 = starRingEnd ℂ w := by
    rw [hwdef]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [e1, e2, digamma_conj hw]
  have hre : (1/2 : ℂ) * Complex.digamma w + (1/2 : ℂ) * starRingEnd ℂ (Complex.digamma w)
      = ((Complex.digamma w).re : ℂ) := by
    rw [← mul_add, Complex.add_conj]; push_cast; ring
  push_cast
  linear_combination hre

omit [NeZero N] in
/-- **The critical-line bracket for χ's Γ factor**: `G'/G(1/2+it) + G'/G(1/2−it) = Re ψ(1/4 + a/2 + it/2) − log π`,
`a = parity χ` -- the bracket of `archTerm_chi` without its `log N`. -/
theorem gammaFactor_bracket (χ : DirichletCharacter ℂ N) (t : ℝ) :
    logDeriv (gammaFactor χ) (1/2 + t * I) + logDeriv (gammaFactor χ) (1/2 - t * I)
      = (((Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * t / 2)).re - Real.log Real.pi : ℝ) : ℂ) := by
  rcases χ.even_or_odd with he | ho
  · rw [show gammaFactor χ = Gammaℝ from funext he.gammaFactor_def]
    have hpar : parity χ = 0 := by unfold parity; simp [he]
    have h := logDeriv_Gammaℝ_bracket (σ := 1/2) (by norm_num) t
      (mem_integerComplement_quarter (Or.inl (by norm_num)) _)
    have e1 : ((1:ℂ)/2 + t * I) = (((1/2:ℝ)) : ℂ) + t * I := by push_cast; ring
    have e2 : ((1:ℂ)/2 - t * I) = (((1/2:ℝ)) : ℂ) - t * I := by push_cast; ring
    have e3 : (((1/2:ℝ) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I = 1 / 4 + ((parity χ : ℕ) : ℂ) / 2 + I * t / 2 := by
      rw [hpar]; push_cast; ring
    rw [e1, e2, h, e3]
  · rw [show gammaFactor χ = fun s => Gammaℝ (s + 1) from funext ho.gammaFactor_def, logDeriv_comp_add_one,
      logDeriv_comp_add_one]
    have hpar : parity χ = 1 := by unfold parity; simp [ho.not_even]
    have h := logDeriv_Gammaℝ_bracket (σ := 3/2) (by norm_num) t
      (mem_integerComplement_quarter (Or.inr (by norm_num)) _)
    have e1 : ((1:ℂ)/2 + t * I + 1) = (((3/2:ℝ)) : ℂ) + t * I := by push_cast; ring
    have e2 : ((1:ℂ)/2 - t * I + 1) = (((3/2:ℝ)) : ℂ) - t * I := by push_cast; ring
    have e3 : (((3/2:ℝ) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I = 1 / 4 + ((parity χ : ℕ) : ℂ) / 2 + I * t / 2 := by
      rw [hpar]; push_cast; ring
    rw [e1, e2, h, e3]

end Bracket

/-! ## Line facts for the evaluation -/

section LineFacts

/-- `t ↦ L'/L(c+it, ψ)` is continuous for `c ≥ 1`, `ψ ≠ 1`. -/
theorem continuous_logDeriv_LFunction_line {ψ : DirichletCharacter ℂ N} (hψ1 : ψ ≠ 1) {c : ℝ} (hc1 : 1 ≤ c) :
    Continuous (fun t : ℝ => logDeriv (LFunction ψ) ((c : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : LFunction ψ ((c : ℂ) + t * I) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by simpa using hc1)
  have han := (differentiable_LFunction hψ1).analyticAt ((c : ℂ) + t * I)
  have : ContinuousAt (fun s => deriv (LFunction ψ) s / LFunction ψ s) ((c : ℂ) + t * I) :=
    han.deriv.continuousAt.div han.continuousAt hne
  show ContinuousAt ((fun s => deriv (LFunction ψ) s / LFunction ψ s) ∘ (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt

/-- `t ↦ G'/G(g t)` is continuous for a continuous path `g` in the right half-plane. -/
theorem continuous_logDeriv_gammaFactor_comp (ψ : DirichletCharacter ℂ N) {g : ℝ → ℂ} (hg : Continuous g)
    (hre : ∀ t, 0 < (g t).re) : Continuous (fun t : ℝ => logDeriv (gammaFactor ψ) (g t)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have han := analyticAt_gammaFactor ψ (hre t)
  have : ContinuousAt (fun s => deriv (gammaFactor ψ) s / gammaFactor ψ s) (g t) :=
    han.deriv.continuousAt.div han.continuousAt (gammaFactor_ne_zero_of_re_pos ψ (hre t))
  show ContinuousAt ((fun s => deriv (gammaFactor ψ) s / gammaFactor ψ s) ∘ g) t
  exact ContinuousAt.comp this hg.continuousAt

/-- `h(t) = H(1/2 + it)`. -/
theorem paperFT_eq_Hfn_half (k : ℝ → ℂ) (t : ℝ) : paperFT k t = Hfn k (((1/2 : ℝ) : ℂ) + t * I) := by
  unfold Hfn
  congr 1
  rw [eq_div_iff I_ne_zero]
  push_cast; ring

/-- **The prime line at ψ, evaluated**: `(1/2π)∫ H(c+it)·L'/L(c+it, ψ) dt = −Σ Λ(n) n^{−1/2} ψ(n) k(log n)`. -/
theorem prime_line_eval (ψ : DirichletCharacter ℂ N) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * logDeriv (LFunction ψ) ((c : ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (ψ (n : ZMod N) * k (Real.log n)) := by
  have h := prime_side_line_chi (χ := ψ) hk hkc hc1
  have h2 : (∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv (LFunction ψ) (c + t * I)))
      = -∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * logDeriv (LFunction ψ) ((c : ℂ) + t * I) := by
    rw [← integral_neg]
    congr 1
    funext t
    ring
  rw [h2] at h
  have h3 : ∀ n : ℕ, (↗ψ * ↗Λ) n * ((1 / Real.sqrt n : ℝ) : ℂ) * k (Real.log n)
      = ((Λ n / Real.sqrt n : ℝ) : ℂ) * (ψ (n : ZMod N) * k (Real.log n)) := by
    intro n
    simp only [Pi.mul_apply]
    push_cast
    ring
  rw [tsum_congr h3] at h
  linear_combination -h

/-- **THE CONDUCTOR TERM'S LINE SHIFT**: `∫ H(1−c−it) dt = ∫ h(r) dr` for `1/2 ≤ c ≤ 2` (Zeta23's `vertical_line_shift` for the
entire `s ↦ H(1 − s)`, majorant `C/(1+t²)`). -/
theorem conductor_line_shift {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 2) :
    ∫ t : ℝ, Hfn k (1 - c - t * I) = ∫ t : ℝ, paperFT k t := by
  have hHd : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk.continuous hkc
    show Differentiable ℂ (fun s => paperFT k ((s - 1/2) / I))
    exact h.comp ((differentiable_id.sub_const _).div_const I)
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  set f : ℂ → ℂ := fun s => Hfn k (1 - s) with hf
  have hfd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f s := fun s _ _ =>
    (hHd (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)
  set φ : ℝ → ℝ := fun t => C * (1 + t ^ 2)⁻¹ with hφ
  have hφi : Integrable φ := integrable_inv_one_add_sq.const_mul C
  have hb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    have e : (1 : ℂ) - (σ + t * I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have := hC (1 - σ) (-t) (by linarith) (by linarith)
    rw [neg_sq, div_eq_mul_inv] at this
    simp only [hf, hφ]
    rw [e]
    exact this
  have hsq : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have hsq' : Tendsto (fun t : ℝ => 1 + t ^ 2) atBot atTop := by
    refine tendsto_atTop_add_const_left _ 1 ?_
    have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_neg_atBot_atTop
    refine this.congr fun t => ?_
    simp
  have htop : Tendsto φ atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hsq).const_mul C
  have hbot : Tendsto φ atBot (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hsq').const_mul C
  have hshift := vertical_line_shift (f := f) (a := 1/2) (b := c) hc1 hfd hφi hb htop hbot
  have hL : (fun t : ℝ => Hfn k (1 - c - t * I)) = fun t : ℝ => f (c + t * I) := by
    funext t
    simp only [hf]
    congr 1
    ring
  have hR : (fun t : ℝ => f (((1/2 : ℝ) : ℂ) + t * I)) = fun t : ℝ => paperFT k ((-t : ℝ) : ℂ) := by
    funext t
    simp only [hf]
    unfold Hfn
    congr 1
    rw [div_eq_iff I_ne_zero]
    push_cast; ring
  rw [hL, hshift, hR]
  exact integral_neg_eq_self (fun t : ℝ => paperFT k (t : ℂ)) volume

/-- A sum `Σ a(n) g(log n)` with `g` vanishing off `[−B, B]` has finite support. -/
theorem summable_mul_log_of_bounded_support {g : ℝ → ℂ} {B : ℝ} (hg : ∀ u, g u ≠ 0 → |u| ≤ B) (a : ℕ → ℂ) :
    Summable (fun n : ℕ => a n * g (Real.log n)) := by
  refine summable_of_hasFiniteSupport ?_
  have hsub : Function.support (fun n : ℕ => a n * g (Real.log n)) ⊆ Set.Iic ⌈Real.exp B⌉₊ := by
    intro n hn
    rw [Function.mem_support] at hn
    have hgne : g (Real.log n) ≠ 0 := fun h => hn (by rw [h, mul_zero])
    rw [Set.mem_Iic]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
      have h2 : Real.log n ≤ B := (le_abs_self _).trans (hg _ hgne)
      have : (n:ℝ) ≤ Real.exp B := by
        calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp B := Real.exp_le_exp.mpr h2
      exact_mod_cast this.trans (Nat.le_ceil _)
  exact (Set.finite_Iic _).subset hsub

end LineFacts

/-! ## The explicit formula for χ -/

/-- **EF_lit FOR `χ`, PROVED.** For primitive `χ ≠ 1` and every `k ∈ C_c²(ℝ)`, the zero sum over the nontrivial zeros of
`LFunction χ` with multiplicity converges absolutely and equals `literatureRHS_chi χ k = archTerm_chi χ k − primeSum_chi χ k`.
The conductor enters as `log N · (1/2π)∫ h(r) dr` on the archimedean side (`conductor_line_shift`), where it joins the Γ part's
`−log π` in `gammaBracket_chi`'s `log(N/π)`; it enters neither the prime side nor the zero side. -/
theorem EF_lit_chi_holds {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : EF_lit_chi χ hχ h1 := by
  intro k hk hkc
  refine ⟨EF_zero_sum_summable_chi hχ h1 hk hkc, ?_⟩
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have hc1 : (1:ℝ) < 5/4 := by norm_num
  have hc2 : (5/4:ℝ) ≤ 3/2 := by norm_num
  have hkneg2 : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknegc : HasCompactSupport (fun u : ℝ => k (-u)) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  have hb1 : ∀ t : ℝ, ‖Hfn k (((5/4:ℝ):ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := fun t => hC _ t (by norm_num) (by norm_num)
  have hb2 : ∀ t : ℝ, ‖Hfn k (1 - (5/4:ℝ) - t * I)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    have h2 := hC (1 - 5/4) (-t) (by norm_num) (by norm_num)
    rw [← one_sub_cast, neg_sq] at h2
    exact h2
  have hH1c : Continuous (fun t : ℝ => Hfn k (((5/4:ℝ):ℂ) + t * I)) := continuous_Hfn_line hk hkc _
  have hH2c : Continuous (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I)) := continuous_Hfn_reflect hk hkc _
  -- the pointwise split of the full-line integrand
  have hF : ∀ t : ℝ, Fline_chi χ k (5/4) t
      = (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (1 - (5/4:ℝ) - t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (1 - (5/4:ℝ) - t * I) * Complex.log (N : ℂ) := by
    intro t
    simp only [Fline_chi, FlineCond_chi]
    rw [logDeriv_completedLFunction_line h1 hc1 t, logDeriv_completedLFunction_line hinv1 hc1 t, gammaFactor_inv]
    ring
  -- integrability of the four parts
  obtain ⟨CG, hCG, hGb⟩ := norm_logDeriv_gammaFactor_le χ
  have iG : Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
      * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I)) := by
    refine integrable_mul_of_decay_log (hH1c.add hH2c) (C := 2 * C) (by positivity) (fun t => ?_)
      (continuous_logDeriv_gammaFactor_comp χ (by fun_prop) (fun t => by norm_num)) le_rfl hCG.le
      (fun t => by rw [zero_add]; exact hGb _ t (by norm_num) (by norm_num))
    calc ‖Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I)‖
        ≤ ‖Hfn k (((5/4:ℝ):ℂ) + t * I)‖ + ‖Hfn k (1 - (5/4:ℝ) - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add (hb1 t) (hb2 t)
      _ = 2 * C / (1 + t ^ 2) := by ring
  obtain ⟨Mχ, hMχ0, hMχ⟩ := norm_logDeriv_LFunction_le_of_one_lt_re χ hc1
  obtain ⟨Mι, hMι0, hMι⟩ := norm_logDeriv_LFunction_le_of_one_lt_re χ⁻¹ hc1
  have iPχ : Integrable (fun t : ℝ => Hfn k (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ) (((5/4:ℝ):ℂ) + t * I)) :=
    integrable_mul_of_decay_log hH1c hC0 hb1 (continuous_logDeriv_LFunction_line h1 hc1.le) hMχ0 le_rfl
      (fun t => by rw [zero_mul, add_zero]; exact hMχ t)
  have iPι : Integrable (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I)) :=
    integrable_mul_of_decay_log hH2c hC0 hb2 (continuous_logDeriv_LFunction_line hinv1 hc1.le) hMι0 le_rfl
      (fun t => by rw [zero_mul, add_zero]; exact hMι t)
  have iN : Integrable (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I) * Complex.log (N : ℂ)) :=
    integrable_mul_of_decay_log (ψ := fun _ : ℝ => Complex.log (N : ℂ)) hH2c hC0 hb2 continuous_const
      (norm_nonneg (Complex.log (N : ℂ))) le_rfl (fun t => by simp)
  -- the full-line integral split into the four parts
  have hsplit : ∫ t : ℝ, Fline_chi χ k (5/4) t
      = (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
            * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I))
        + (∫ t : ℝ, Hfn k (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ) (((5/4:ℝ):ℂ) + t * I))
        + (∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I))
        + ∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I) * Complex.log (N : ℂ) := by
    have i12 : Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ) (((5/4:ℝ):ℂ) + t * I)) := iG.add iPχ
    have i123 : Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ) (((5/4:ℝ):ℂ) + t * I)
        + Hfn k (1 - (5/4:ℝ) - t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I)) := i12.add iPι
    rw [integral_congr_ae (Eventually.of_forall hF), integral_add i123 iN, integral_add i12 iPι, integral_add iG iPχ]
  -- the Γ part, on the critical line
  have eΓ : (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * logDeriv (gammaFactor χ) (((5/4:ℝ):ℂ) + t * I))
      = ∫ r : ℝ, paperFT k r
        * (((Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ) := by
    rw [gamma_line_shift_chi χ hk hkc hc1 hc2]
    congr 1
    funext r
    rw [gammaFactor_bracket χ r]
  -- the prime lines
  have ePχ := prime_line_eval χ hk hkc hc1
  have ePι : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I)
        * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (conj (χ (n : ZMod N)) * k (-Real.log n)) := by
    have h := prime_line_eval χ⁻¹ hkneg2 hknegc hc1
    have hm : (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I))
        = fun t : ℝ => Hfn (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I) * logDeriv (LFunction χ⁻¹) (((5/4:ℝ):ℂ) + t * I) := by
      funext t
      rw [Hfn_mirror k (5/4) t]
    rw [hm, h]
    congr 2
    funext n
    rw [inv_apply_natCast]
  -- the conductor term, on the critical line
  have eN : (∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I) * Complex.log (N : ℂ))
      = Complex.log (N : ℂ) * ∫ r : ℝ, paperFT k r := by
    rw [integral_mul_const, conductor_line_shift hk hkc (by norm_num) (by norm_num)]
    ring
  -- the archimedean side: the Γ part and the conductor term make archTerm_chi
  have hcont_h : Continuous (fun r : ℝ => paperFT k r) :=
    (differentiable_paperFT hk.continuous hkc).continuous.comp Complex.continuous_ofReal
  have hbh : ∀ r : ℝ, ‖paperFT k r‖ ≤ C / (1 + r ^ 2) := fun r => by
    rw [paperFT_eq_Hfn_half]; exact hC _ r (by norm_num) (by norm_num)
  have iΓh : Integrable (fun r : ℝ => paperFT k r
      * (((Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)) := by
    have hcp : Continuous (fun r : ℝ => (1/2 : ℂ) + r * I) := by fun_prop
    have hcm : Continuous (fun r : ℝ => (1/2 : ℂ) - r * I) := by fun_prop
    have i0 := integrable_mul_of_decay_log hcont_h hC0 hbh
      ((continuous_logDeriv_gammaFactor_comp χ hcp (fun r => by norm_num)).add
        (continuous_logDeriv_gammaFactor_comp χ hcm (fun r => by norm_num)))
      le_rfl (by positivity : (0:ℝ) ≤ 2 * CG) (fun r => ?_)
    · refine i0.congr (Eventually.of_forall fun r => ?_)
      simp only [Pi.add_apply]
      rw [gammaFactor_bracket χ r]
    · have e1 : ((1:ℂ)/2 + r * I) = (((1/2:ℝ)) : ℂ) + r * I := by push_cast; ring
      have e2 : ((1:ℂ)/2 - r * I) = (((1/2:ℝ)) : ℂ) + ((-r : ℝ) : ℂ) * I := by push_cast; ring
      simp only [Pi.add_apply]
      rw [zero_add, e1, e2]
      calc ‖logDeriv (gammaFactor χ) (((1/2:ℝ) : ℂ) + r * I) + logDeriv (gammaFactor χ) (((1/2:ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I)‖
          ≤ ‖logDeriv (gammaFactor χ) (((1/2:ℝ) : ℂ) + r * I)‖
            + ‖logDeriv (gammaFactor χ) (((1/2:ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ CG * Real.log (2 + |r|) + CG * Real.log (2 + |-r|) :=
            add_le_add (hGb _ r (by norm_num) (by norm_num)) (hGb _ (-r) (by norm_num) (by norm_num))
        _ = 2 * CG * Real.log (2 + |r|) := by rw [abs_neg]; ring
  have iNh : Integrable (fun r : ℝ => paperFT k r * Complex.log (N : ℂ)) :=
    integrable_mul_of_decay_log (ψ := fun _ : ℝ => Complex.log (N : ℂ)) hcont_h hC0 hbh continuous_const
      (norm_nonneg (Complex.log (N : ℂ))) le_rfl (fun r => by simp)
  have hlogN : Complex.log (N : ℂ) = ((Real.log N : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg N), Complex.ofReal_natCast]
  have hbr : ∀ r : ℝ, paperFT k r * (gammaBracket_chi χ r : ℂ)
      = paperFT k r * (((Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)
        + paperFT k r * Complex.log (N : ℂ) := by
    intro r
    unfold gammaBracket_chi
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [Real.log_div hN0 Real.pi_ne_zero, hlogN]
    push_cast
    ring
  have earch : archTerm_chi χ k
      = (1 / (2 * Real.pi) : ℂ) * (∫ r : ℝ, paperFT k r
          * (((Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ))
        + Complex.log (N : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r) := by
    unfold archTerm_chi
    rw [integral_congr_ae (Eventually.of_forall hbr), integral_add iΓh iNh, integral_mul_const]
    ring
  -- the prime side: the two prime lines make primeSum_chi
  obtain ⟨B₁, hB₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hs1 : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * (χ (n : ZMod N) * k (Real.log n))) := by
    refine (summable_mul_log_of_bounded_support (g := k) hB₁
      (fun n => ((Λ n / Real.sqrt n : ℝ) : ℂ) * χ (n : ZMod N))).congr fun n => ?_
    ring
  have hs2 : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * (conj (χ (n : ZMod N)) * k (-Real.log n))) := by
    refine (summable_mul_log_of_bounded_support (g := fun u => k (-u)) (B := B₁) (fun u hu => ?_)
      (fun n => ((Λ n / Real.sqrt n : ℝ) : ℂ) * conj (χ (n : ZMod N)))).congr fun n => ?_
    · have h2 := hB₁ (-u) hu
      rwa [abs_neg] at h2
    · ring
  have eprime : primeSum_chi χ k
      = (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (χ (n : ZMod N) * k (Real.log n)))
        + ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (conj (χ (n : ZMod N)) * k (-Real.log n)) := by
    unfold primeSum_chi
    rw [← Summable.tsum_add hs1 hs2]
    refine tsum_congr fun n => ?_
    ring
  -- assemble
  have hfull := full_line_identity_chi hχ h1 hk hkc hc1 hc2
  rw [literatureRHS_chi, earch, eprime]
  calc ∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * paperFT k (gammaOf (ρ : ℂ))
      = ∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Hfn k (ρ : ℂ) := rfl
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Fline_chi χ k (5/4) t := hfull.symm
    _ = _ := by
        rw [hsplit, eΓ, eN]
        linear_combination ePχ + ePι
