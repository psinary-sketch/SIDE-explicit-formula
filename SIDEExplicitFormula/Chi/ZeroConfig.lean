/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZeroConfig.lean
THIS PROGRAMME'S WORK (act b564, ruling (R174)(5)(a); W-ORD-GRH-WEIL, act two) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-INSTANCE OF THE ZERO CONFIGURATION. For a Dirichlet character `χ : DirichletCharacter ℂ N`, primitive, `χ ≠ 1`, the
zeros of Mathlib's `LFunction χ` in the open strip, with multiplicity the analytic order, as a `Zeta23.ZeroConfig`
(`chiZeroConfig`). This file is the χ-analogue of the modules that build ζ's instance -- Zeta23/Statement.lean
(`IsNontrivialZero`, `zeroMult`, `zetaZeros`), Zeta23/Statement/Seam.lean (`one_le_mult`, `finite_window`),
Zeta23/ZetaReflect.lean (`reflect_mem`, `mult_reflect`) and Zeta23/Statement/SeamClosed.lean (`zetaZeroConfig`) -- written
beside them by name in the programme's tree; no Zeta23 file is edited or added.

(1) `one_le_mult`: `LFunction χ` is entire for `χ ≠ 1` (`differentiable_LFunction`) and nonzero at `2`
(`LFunction_ne_zero_of_one_le_re`), so by the identity theorem on `ℂ` its order is finite everywhere.
(2) `finite_window`: its zeros are locally finite on `ℂ` (the same identity theorem) and the box `[0,1] × [T₁,T₂]` is
compact.
(3) `reflect_mem`, `mult_reflect`: `ρ ↦ 1 - conj ρ` is `conj (1 - ρ)`. The completion `completedLFunction` equals
`LFunction` times the Gamma factor (`LFunction_eq_completed_div_gammaFactor`), and `1 / gammaFactor` is entire and nonzero
on `re s > 0` (`differentiable_Gammaℝ_inv`, `Gammaℝ_ne_zero_of_re_pos`), so on the strip the zeros and the orders of
`LFunction χ` and of its completion agree. The functional equation `IsPrimitive.completedLFunction_one_sub`, applied to
`χ⁻¹` (primitive, `isPrimitive_inv`), gives `completedLFunction χ⁻¹ (1 - s) = c(s) * completedLFunction χ s` with `c` entire,
hence `ord_{1-w} Λ(χ⁻¹) ≥ ord_w Λ(χ)`; applied to `χ` it gives the other inequality. NO ROOT-NUMBER FACT IS CONSUMED: the
root number enters `c` as a constant, and nothing is assumed about it. b562's pairing (`LFunction_inv_conj`,
`analyticOrderAt_LFunction_inv_conj`) carries `1 - ρ` for `χ⁻¹` to `conj (1 - ρ)` for `χ`.
(4) THE PAIRING ACROSS (χ, χ⁻¹), attached: `ρ` lies in `χ`'s carrier iff `conj ρ` lies in `χ⁻¹`'s, with equal
multiplicity -- the χ-form of b560's conjugation construction for ζ (`conj_mem`, `mult_conj`, LiWeil.lean :42, :53), which
for `χ` not real pairs two configurations rather than stabilising one.

Nothing here proves GRH, RH, or anything about where the zeros of `LFunction χ` lie beyond the open strip's definition.
-/
import SIDEExplicitFormula.GRHWeil

open Complex
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## The carrier and the multiplicity -/

/-- A nontrivial zero of `L(s, χ)`: a zero of `LFunction χ` in the open strip `0 < re s < 1`. -/
def IsNontrivialZeroChi (χ : DirichletCharacter ℂ N) (ρ : ℂ) : Prop :=
  LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The multiplicity: the analytic order of `LFunction χ` at `ρ`, as a natural number. -/
def zeroMultChi (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ := (analyticOrderAt (LFunction χ) ρ).toNat

/-! ## (1) `one_le_mult` -/

/-- `LFunction χ` is analytic on `ℂ` for `χ ≠ 1`. -/
theorem LFunction_analyticOnNhd {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
  (differentiable_LFunction h1).differentiableOn.analyticOnNhd isOpen_univ

/-- `LFunction χ 2 ≠ 0`. -/
theorem LFunction_two_ne_zero {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) : LFunction χ 2 ≠ 0 :=
  LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl h1) (by norm_num)

/-- The order of `LFunction χ` is finite everywhere (the identity theorem on `ℂ`). -/
theorem analyticOrderAt_LFunction_ne_top {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (LFunction χ) s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ (Set.univ : Set ℂ) := Set.mem_univ _
  refine (LFunction_analyticOnNhd h1).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ h2
    (Set.mem_univ s) ?_
  rw [((LFunction_analyticOnNhd h1) 2 h2).analyticOrderAt_eq_zero.mpr (LFunction_two_ne_zero h1)]
  exact ENat.zero_ne_top

/-- At a nontrivial zero the multiplicity is at least one. -/
theorem one_le_zeroMultChi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {ρ : ℂ} (h : IsNontrivialZeroChi χ ρ) :
    1 ≤ zeroMultChi χ ρ := by
  have han : AnalyticAt ℂ (LFunction χ) ρ := LFunction_analyticOnNhd h1 ρ (Set.mem_univ _)
  have hne0 : analyticOrderAt (LFunction χ) ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop := analyticOrderAt_LFunction_ne_top h1 ρ
  unfold zeroMultChi
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

/-! ## (2) `finite_window` -/

/-- The zeros of `LFunction χ` are locally finite on `ℂ`. -/
theorem LFunction_zeros_locallyFinite {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (z : ℂ) :
    ∃ t ∈ nhds z, (t ∩ {ρ : ℂ | LFunction χ ρ = 0}).Finite := by
  rcases (LFunction_analyticOnNhd h1).eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with
    hzero | hcod
  · exfalso
    have : LFunction χ 2 = 0 := hzero (Set.mem_univ 2)
    exact LFunction_two_ne_zero h1 this
  · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
    obtain ⟨t, ht, hfin⟩ := hcod z (Set.mem_univ z)
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro s ⟨hst, hs0⟩
    exact ⟨hst, Set.mem_univ s, by simpa using hs0⟩

/-- Finitely many nontrivial zeros with `T₁ < im ρ ≤ T₂`. -/
theorem finite_window_chi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (T₁ T₂ : ℝ) :
    ({ρ | IsNontrivialZeroChi χ ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  set K : Set ℂ := (Set.Icc 0 1) ×ℂ (Set.Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using LFunction_zeros_locallyFinite h1
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | LFunction χ ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have hρK : ρ ∈ K := ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hρz⟩ := Set.mem_iUnion₂.mp (hcover hρK)
  exact Set.mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ.1⟩

/-! ## (3) `reflect_mem`, `mult_reflect` -/

/-- `s ↦ 1 / gammaFactor ψ s` is entire. -/
theorem gammaFactor_inv_differentiable (ψ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (gammaFactor ψ s)⁻¹) := by
  rcases ψ.even_or_odd with he | ho
  · have e : (fun s => (gammaFactor ψ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ := funext fun s => by rw [he.gammaFactor_def]
    rw [e]
    exact differentiable_Gammaℝ_inv
  · have e : (fun s => (gammaFactor ψ s)⁻¹) = (fun s => (Gammaℝ s)⁻¹) ∘ (fun s : ℂ => s + 1) :=
      funext fun s => by rw [ho.gammaFactor_def]; rfl
    rw [e]
    exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

/-- On `re w > 0` the orders of `LFunction ψ` and of its completion agree, for `ψ ≠ 1`. -/
theorem analyticOrderAt_LFunction_eq_completed {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {w : ℂ} (hw : 0 < w.re) :
    analyticOrderAt (LFunction ψ) w = analyticOrderAt (completedLFunction ψ) w := by
  have hN := ne_one_of_ne_one hψ
  have e : LFunction ψ = completedLFunction ψ * fun s => (gammaFactor ψ s)⁻¹ := by
    funext s
    rw [LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hN), div_eq_mul_inv]
    rfl
  have hΛ : AnalyticAt ℂ (completedLFunction ψ) w := (differentiable_completedLFunction hψ).analyticAt w
  have hg : AnalyticAt ℂ (fun s => (gammaFactor ψ s)⁻¹) w := (gammaFactor_inv_differentiable ψ).analyticAt w
  have hg0 : analyticOrderAt (fun s => (gammaFactor ψ s)⁻¹) w = 0 :=
    hg.analyticOrderAt_eq_zero.mpr (inv_ne_zero (gammaFactor_ne_zero_of_re_pos ψ hw))
  rw [e, analyticOrderAt_mul hΛ hg, hg0, add_zero]

/-- The functional equation at the level of orders, one inequality: `ord_w Λ(χ) ≤ ord_{1-w} Λ(χ⁻¹)`. -/
theorem analyticOrderAt_completed_le_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (w : ℂ) :
    analyticOrderAt (completedLFunction χ) w ≤ analyticOrderAt (completedLFunction χ⁻¹) (1 - w) := by
  set c : ℂ → ℂ := fun s => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ with hc_def
  have hFE : (completedLFunction χ⁻¹ ∘ fun z : ℂ => 1 - z) = c * completedLFunction χ := by
    funext s
    simp only [Function.comp_apply, Pi.mul_apply, hc_def]
    rw [(isPrimitive_inv hχ).completedLFunction_one_sub s, inv_inv]
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    rw [deriv_const_sub]
    simp
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc : AnalyticAt ℂ c w := by
    refine Differentiable.analyticAt (fun s => ?_) w
    exact ((differentiableAt_id.sub_const _).const_cpow (Or.inl hN0)).mul_const _
  have hΛ : AnalyticAt ℂ (completedLFunction χ) w := (differentiable_completedLFunction h1).analyticAt w
  calc analyticOrderAt (completedLFunction χ) w
      ≤ analyticOrderAt c w + analyticOrderAt (completedLFunction χ) w := le_add_self
    _ = analyticOrderAt (c * completedLFunction χ) w := (analyticOrderAt_mul hc hΛ).symm
    _ = analyticOrderAt (completedLFunction χ⁻¹ ∘ fun z : ℂ => 1 - z) w := by rw [hFE]
    _ = analyticOrderAt (completedLFunction χ⁻¹) (1 - w) := analyticOrderAt_comp_of_deriv_ne_zero hg hg'

/-- **The functional equation at the level of orders:** `ord_{1-w} Λ(χ⁻¹) = ord_w Λ(χ)`, both inequalities, no
root-number fact. -/
theorem analyticOrderAt_completed_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (w : ℂ) :
    analyticOrderAt (completedLFunction χ⁻¹) (1 - w) = analyticOrderAt (completedLFunction χ) w := by
  apply le_antisymm
  · have h := analyticOrderAt_completed_le_one_sub (isPrimitive_inv hχ) (inv_ne_one.mpr h1) (1 - w)
    rwa [inv_inv, sub_sub_cancel] at h
  · exact analyticOrderAt_completed_le_one_sub hχ h1 w

/-- `reflect ρ = conj (1 - ρ)`. -/
theorem reflect_eq_conj_one_sub (ρ : ℂ) : Zeta23.reflect ρ = conj (1 - ρ) := by
  unfold Zeta23.reflect
  rw [map_sub, map_one]

/-- **`reflect_mem` for `χ`:** `ρ ↦ 1 - conj ρ` maps nontrivial zeros of `L(s, χ)` to nontrivial zeros. -/
theorem chi_reflect_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {ρ : ℂ}
    (h : IsNontrivialZeroChi χ ρ) : IsNontrivialZeroChi χ (Zeta23.reflect ρ) := by
  obtain ⟨hz, h0, hr1⟩ := h
  have hN := ne_one_of_ne_one h1
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have hΛ : completedLFunction χ ρ = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ ρ (Or.inr hN), div_eq_zero_iff] at hz
    exact hz.resolve_right (gammaFactor_ne_zero_of_re_pos χ h0)
  have hΛ' : completedLFunction χ⁻¹ (1 - ρ) = 0 := by
    rw [(isPrimitive_inv hχ).completedLFunction_one_sub ρ, inv_inv, hΛ, mul_zero]
  have hL' : LFunction χ⁻¹ (1 - ρ) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inr hN), hΛ', zero_div]
  refine ⟨?_, ?_, ?_⟩
  · have h2 := LFunction_inv_conj hinv1 (1 - ρ)
    rw [inv_inv, hL', map_zero] at h2
    rw [reflect_eq_conj_one_sub]
    exact h2
  · unfold Zeta23.reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · unfold Zeta23.reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- **`mult_reflect` for `χ`:** `m_{1 - conj ρ} = m_ρ`. -/
theorem chi_mult_reflect {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {ρ : ℂ}
    (h : IsNontrivialZeroChi χ ρ) : zeroMultChi χ (Zeta23.reflect ρ) = zeroMultChi χ ρ := by
  obtain ⟨_, h0, hr1⟩ := h
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have hw : 0 < (1 - ρ).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have e1 := analyticOrderAt_LFunction_inv_conj hinv1 (1 - ρ)
  rw [inv_inv] at e1
  unfold zeroMultChi
  rw [reflect_eq_conj_one_sub, e1, analyticOrderAt_LFunction_eq_completed hinv1 hw,
    analyticOrderAt_completed_one_sub hχ h1 ρ, ← analyticOrderAt_LFunction_eq_completed h1 h0]

/-! ## The instance -/

/-- **The χ-instance:** the nontrivial zeros of `L(s, χ)`, primitive `χ ≠ 1`, with multiplicity, as a
`Zeta23.ZeroConfig` -- hypothesis-free beyond primitivity and nontriviality. -/
def chiZeroConfig (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) : Zeta23.ZeroConfig where
  carrier := {ρ | IsNontrivialZeroChi χ ρ}
  mult := zeroMultChi χ
  one_le_mult := fun _ h => one_le_zeroMultChi h1 h
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := fun _ h => chi_reflect_zero hχ h1 h
  mult_reflect := fun _ h => chi_mult_reflect hχ h1 h
  finite_window := finite_window_chi h1

theorem chiZeroConfig_carrier (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    (chiZeroConfig χ hχ h1).carrier = {ρ | IsNontrivialZeroChi χ ρ} := rfl

theorem chiZeroConfig_mult (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    (chiZeroConfig χ hχ h1).mult = zeroMultChi χ := rfl

/-! ## (4) The pairing across (χ, χ⁻¹), attached -/

/-- `ρ` is in `χ`'s carrier iff `conj ρ` is in `χ⁻¹`'s. -/
theorem chiZeroConfig_conj_mem {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (ρ : ℂ) :
    ρ ∈ (chiZeroConfig χ hχ h1).carrier ↔
      conj ρ ∈ (chiZeroConfig χ⁻¹ (isPrimitive_inv hχ) (inv_ne_one.mpr h1)).carrier := by
  show IsNontrivialZeroChi χ ρ ↔ IsNontrivialZeroChi χ⁻¹ (conj ρ)
  unfold IsNontrivialZeroChi
  rw [← LFunction_zero_iff_conj h1, Complex.conj_re]

/-- The multiplicities agree across the pair. -/
theorem chiZeroConfig_mult_conj {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (ρ : ℂ) :
    (chiZeroConfig χ⁻¹ (isPrimitive_inv hχ) (inv_ne_one.mpr h1)).mult (conj ρ) = (chiZeroConfig χ hχ h1).mult ρ := by
  show zeroMultChi χ⁻¹ (conj ρ) = zeroMultChi χ ρ
  unfold zeroMultChi
  rw [analyticOrderAt_LFunction_inv_conj h1]

end GRHWeil
end SIDEExplicitFormula
