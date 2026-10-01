/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/Horizontal.lean
THIS PROGRAMME'S WORK (act b571, ruling (R181)(4)(c); W-ORD-GRH-WEIL, act six) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/Horizontal.lean: the horizontal sides of the rectangle vanish along good heights. For
`s = x ± iR_j`, `x ∈ [1−c, c]`: `‖H(s)‖ ≤ C_H/(1+R_j²)` and `‖Λ'/Λ(s, χ)‖ ≤ K·log²(j+10)` -- for `re s ≥ 1/2` by
`Λ'/Λ = gammaFactor'/gammaFactor + L'/L`, the Γ factor's growth (`norm_logDeriv_gammaFactor_le`) and the good-height bound;
for `re s < 1/2` by the compiled identity `Λ'/Λ(1 − s', χ) = −(log N + Λ'/Λ(s', χ⁻¹))`, the χ⁻¹-side bounded at `s'` on the
opposite horizontal by b562's pairing differentiated (`logDeriv_LFunction_inv_conj`: `L'/L(conj s, χ⁻¹) = conj L'/L(s, χ)`),
which carries χ's good-height bound to χ⁻¹. Nothing here locates any zero.
-/
import SIDEExplicitFormula.Chi.FullLine

open Complex Topology Filter Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF

variable {N : ℕ} [NeZero N]

/-- **The pairing, differentiated**: `L'/L(conj s, χ⁻¹) = conj (L'/L(s, χ))` for every `s`, `χ ≠ 1`. -/
theorem logDeriv_LFunction_inv_conj {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    logDeriv (LFunction χ⁻¹) (conj s) = conj (logDeriv (LFunction χ) s) := by
  have e : LFunction χ⁻¹ = conj ∘ LFunction χ ∘ conj := by
    funext z
    have h := LFunction_inv_conj h1 (conj z)
    rw [Complex.conj_conj] at h
    exact h
  have hd : HasDerivAt (LFunction χ) (deriv (LFunction χ) s) s := (differentiable_LFunction h1 s).hasDerivAt
  have hc := hd.conj_conj
  rw [logDeriv_apply, logDeriv_apply, e, hc.deriv]
  simp only [Function.comp_apply, Complex.conj_conj, map_div₀]

/-- On a point of a good horizontal with `1/2 ≤ re ≤ 3/2`: `‖Λ'/Λ(s, ψ)‖ ≤ (C_G + C_g)·Lg²` from the Γ factor's growth and a
bound `C_g·Lg²` on `L'/L(s, ψ)`. -/
theorem norm_logDeriv_completed_le_of_good {ψ : DirichletCharacter ℂ N} (hψ1 : ψ ≠ 1) {CG Cg Lg : ℝ} (hCG : 0 ≤ CG)
    (hLg1 : 1 ≤ Lg)
    (hG : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → ‖logDeriv (gammaFactor ψ) (σ + t * I)‖ ≤ CG * Real.log (2 + |t|))
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) (hlog : Real.log (2 + |s.im|) ≤ Lg)
    (hL : LFunction ψ s ≠ 0) (hLb : ‖logDeriv (LFunction ψ) s‖ ≤ Cg * Lg ^ 2) :
    ‖logDeriv (completedLFunction ψ) s‖ ≤ (CG + Cg) * Lg ^ 2 := by
  rw [logDeriv_completedLFunction hψ1 s hL (by linarith)]
  have hGs : ‖logDeriv (gammaFactor ψ) s‖ ≤ CG * Lg ^ 2 := by
    have h := hG s.re s.im hs1 hs2
    rw [Complex.re_add_im] at h
    have hLg2 : Lg ≤ Lg ^ 2 := by nlinarith
    calc ‖logDeriv (gammaFactor ψ) s‖ ≤ CG * Real.log (2 + |s.im|) := h
      _ ≤ CG * Lg ^ 2 := mul_le_mul_of_nonneg_left (hlog.trans hLg2) hCG
  calc ‖logDeriv (gammaFactor ψ) s + logDeriv (LFunction ψ) s‖
      ≤ ‖logDeriv (gammaFactor ψ) s‖ + ‖logDeriv (LFunction ψ) s‖ := norm_add_le _ _
    _ ≤ CG * Lg ^ 2 + Cg * Lg ^ 2 := add_le_add hGs hLb
    _ = (CG + Cg) * Lg ^ 2 := by ring

/-- **Horizontal sides vanish for χ** (interface for the full-line identity for χ). -/
theorem horizontal_vanish_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
        LFunction χ s ≠ 0 ∧ ‖logDeriv (LFunction χ) s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv (completedLFunction χ) s)
        (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv (completedLFunction χ) s)
        (1 - c) c (-(R j))) atTop (𝓝 0) := by
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  obtain ⟨CG₁, hCG₁, hG₁⟩ := norm_logDeriv_gammaFactor_le χ
  obtain ⟨CG₂, hCG₂, hG₂⟩ := norm_logDeriv_gammaFactor_le χ⁻¹
  set Lg : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 10) with hLgdef
  have hLg1 : ∀ j : ℕ, 1 ≤ Lg j := fun j => by
    rw [hLgdef, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  set CN : ℝ := ‖Complex.log (N : ℂ)‖ with hCN
  have hCN0 : 0 ≤ CN := norm_nonneg _
  set K : ℝ := CN + CG₁ + CG₂ + Cg with hKdef
  have hK0 : 0 < K := by positivity
  -- the good horizontals, |im| ∈ [j+7, j+8]
  have him8 : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → Real.log (2 + |s.im|) ≤ Lg j := by
    intro j s hsim
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hRj0 : 0 ≤ R j := by linarith
    have h8 : |s.im| ≤ (j : ℝ) + 8 := by
      rcases hsim with h | h
      · rw [h, abs_of_nonneg hRj0]; exact hR2
      · rw [h, abs_neg, abs_of_nonneg hRj0]; exact hR2
    rw [hLgdef]
    exact Real.log_le_log (by positivity) (by linarith)
  -- the right half, at χ
  have hright : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖logDeriv (completedLFunction χ) s‖ ≤ K * (Lg j) ^ 2 := by
    intro j s hsim hre1 hre2
    obtain ⟨hL, hLb⟩ := (hR j).2.2 s hsim hre1 (by linarith)
    have h := norm_logDeriv_completed_le_of_good h1 hCG₁.le (hLg1 j) hG₁ hre1 hre2 (him8 j s hsim) hL hLb
    have : (CG₁ + Cg) * Lg j ^ 2 ≤ K * Lg j ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith) (by positivity)
    exact h.trans this
  -- the right half, at χ⁻¹, through the pairing (conj s lies on the opposite good horizontal)
  have hright_inv : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖logDeriv (completedLFunction χ⁻¹) s‖ ≤ (K - CN) * (Lg j) ^ 2 := by
    intro j s hsim hre1 hre2
    have hcim : (conj s).im = R j ∨ (conj s).im = -R j := by
      rw [Complex.conj_im]
      rcases hsim with h | h
      · right; rw [h]
      · left; rw [h, neg_neg]
    obtain ⟨hL, hLb⟩ := (hR j).2.2 (conj s) hcim (by simpa using hre1) (by simp; linarith)
    have hLi : LFunction χ⁻¹ s ≠ 0 := by
      have := LFunction_inv_conj h1 (conj s)
      rw [Complex.conj_conj] at this
      rw [this, map_ne_zero]
      exact hL
    have hLib : ‖logDeriv (LFunction χ⁻¹) s‖ ≤ Cg * Lg j ^ 2 := by
      have := logDeriv_LFunction_inv_conj h1 (conj s)
      rw [Complex.conj_conj] at this
      rw [this, Complex.norm_conj]
      exact hLb
    have h := norm_logDeriv_completed_le_of_good hinv1 hCG₂.le (hLg1 j) hG₂ hre1 hre2 (him8 j s hsim) hLi hLib
    have : (CG₂ + Cg) * Lg j ^ 2 ≤ (K - CN) * Lg j ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith) (by positivity)
    exact h.trans this
  -- the same bound on the whole horizontal segment x ∈ [1-c, c], by the compiled identity for x < 1/2
  have hall : ∀ (j : ℕ) (x y : ℝ), (y = R j ∨ y = -R j) → 1 - c ≤ x → x ≤ c →
      ‖logDeriv (completedLFunction χ) ((x : ℂ) + y * I)‖ ≤ K * (Lg j) ^ 2 := by
    intro j x y hy hx1 hx2
    rcases le_or_gt (1/2 : ℝ) x with hx | hx
    · exact hright j _ (by rcases hy with h | h <;> simp [h]) (by simpa using hx) (by simp; linarith)
    · -- reflect: s = 1 − s', s' := (1 − x) − y i on the opposite good horizontal
      set s' : ℂ := ((1 - x : ℝ) : ℂ) + (-y) * I with hs'def
      have him' : s'.im = -y := by simp [hs'def]
      have hre' : s'.re = 1 - x := by simp [hs'def]
      have hs'h : s'.im = R j ∨ s'.im = -R j := by
        rw [him']
        rcases hy with h | h
        · right; rw [h]
        · left; rw [h, neg_neg]
      have hb := hright_inv j s' hs'h (by rw [hre']; linarith) (by rw [hre']; linarith)
      have hne : completedLFunction χ⁻¹ s' ≠ 0 := by
        intro h0
        have hw : 0 < s'.re := by rw [hre']; linarith
        have hL0 := (completedLFunction_eq_zero_iff_of_re_pos hinv1 hw).mp h0
        have hcim : (conj s').im = R j ∨ (conj s').im = -R j := by
          rw [Complex.conj_im]
          rcases hs'h with h | h
          · right; rw [h]
          · left; rw [h, neg_neg]
        obtain ⟨hL, -⟩ := (hR j).2.2 (conj s') hcim (by simp; rw [hre']; linarith) (by simp; rw [hre']; linarith)
        have := LFunction_inv_conj h1 (conj s')
        rw [Complex.conj_conj, hL0] at this
        exact hL (by rw [eq_comm, map_eq_zero] at this; exact this)
      have e : ((x : ℂ) + y * I) = 1 - s' := by
        simp only [hs'def]; push_cast; ring
      rw [e, logDeriv_completedLFunction_one_sub hχ h1 s' hne, norm_neg]
      calc ‖Complex.log (N : ℂ) + logDeriv (completedLFunction χ⁻¹) s'‖
          ≤ CN + (K - CN) * Lg j ^ 2 := (norm_add_le _ _).trans (add_le_add le_rfl hb)
        _ ≤ CN * Lg j ^ 2 + (K - CN) * Lg j ^ 2 := by
            have : (1:ℝ) ≤ Lg j ^ 2 := by nlinarith [hLg1 j]
            nlinarith
        _ = K * Lg j ^ 2 := by ring
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * logDeriv (completedLFunction χ) s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    exact mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2]))
      (hall j x y hy hx.1.le hx.2) (norm_nonneg _) (by positivity)
  -- the majorant tends to 0
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hLg_sq : ∀ j : ℕ, Lg j ^ 2 ≤ 4 * ((j : ℝ) + 10) := fun j => by
    have hy0 : (0 : ℝ) ≤ (j : ℝ) + 10 := by positivity
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1/2)
    have hsq : (((j : ℝ) + 10) ^ (1/2 : ℝ)) ^ 2 = (j : ℝ) + 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    have h0 : 0 ≤ Lg j := (zero_le_one.trans (hLg1 j))
    calc Lg j ^ 2 ≤ (((j : ℝ) + 10) ^ (1/2 : ℝ) / (1/2)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 * ((j : ℝ) + 10) := by rw [div_pow, hsq]; ring
  have hb_le : ∀ j : ℕ, b j ≤ (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7) := fun j => by
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1' : Lg j ^ 2 / (1 + R j ^ 2) ≤ 8 / ((j : ℝ) + 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR7 : ((j : ℝ) + 7) ^ 2 ≤ R j ^ 2 := pow_le_pow_left₀ (by positivity) hR1 2
      nlinarith [hLg_sq j, hR7, mul_le_mul_of_nonneg_right (hLg_sq j) (show (0:ℝ) ≤ (j:ℝ) + 7 by positivity),
        sq_nonneg ((j:ℝ) + 7)]
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by
      rw [hbdef]; ring
    rw [e]
    calc CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2))
        ≤ CH * K * |c - (1 - c)| * (8 / ((j : ℝ) + 7)) :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = 8 * CH * K * |c - (1 - c)| / ((j : ℝ) + 7) := by ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

end GRHWeil
end SIDEExplicitFormula
