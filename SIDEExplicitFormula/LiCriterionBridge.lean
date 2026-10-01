/-
SIDE-explicit-formula -- SIDEExplicitFormula/LiCriterionBridge.lean
THIS PROGRAMME'S WORK (act b566, ruling (R176)(3), steps two and three; W-ORD-LI-WEIL-BRIDGE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CONVERSE, COMPOSED. The converse of Li's criterion is consumed BY NAME from the vendored copy of
github.com/nicholasbulka/li-criterion-rh-equivalence-lean at 35df682f (Vendored/Bulka/, byte-identical bodies):
`LiCriterion.positivity_implies_RH` (ReverseDirection.lean :397), the fidelity statement
`LiCriterion.taylorCoeff_eq_li_symmetrized` with its summability `LiCriterion.summable_li_symmetrized` (Fidelity.lean :124,
:139), and the bridge to Mathlib's RH `LiCriterion.rh_equiv_mathlib` (RHBridge.lean :27).

STEP TWO -- THE EQUALITY LEMMA `li_coeff_eq_taylorCoeff : LiCoeff (n + 1) = (taylorCoeff riemannXi n).re`, in four parts:
(E1) the carrier: `zetaZeroConfig.carrier` and `LiCriterion.NontrivialZero` are one subtype of `ℂ` (`carrierEquiv`);
(E2) the multiplicity: on `0 < Re ρ`, `ρ ≠ 1`, the order of ξ equals the order of ζ, since near such `ρ`
     `ξ = (½ s (s − 1)) · Λ` and `ζ = Γℝ⁻¹ · Λ` with both factors beside `Λ` analytic and nonzero there
     (`analyticOrderAt_xi_eq_zeta`, `zeroMult_eq_xiMult`);
(E3) the term: the reflected half of Bulka's summand is `liTerm (n + 1)` at the paired zero (`neg_term_eq`), and the
     reflected sum equals the direct one by the pairing equivalence and the multiplicity's invariance under `ρ ↦ 1 − ρ`;
(E4) the real part of the summable symmetrized sum is the sum of the real parts (`Complex.re_tsum`).

STEP THREE -- `li_nonneg_iff_rh` and `arith_limit_nonneg_iff_rh`.

Nothing here is a statement about the zeros of ζ beyond these theorems' own words.
-/
import SIDEExplicitFormula.LiWeilSym
import Lc.LiCriterion.Fidelity

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace LiCriterionBridge

open Zeta23 LiWeil

/-! ## (E1) the carrier -/

/-- **(E1)** The kernel's carrier (`IsNontrivialZero`, Zeta23/Statement.lean :54) and Bulka's `NontrivialZero`
(Basic.lean :100) are the same subtype of `ℂ`: both predicates are `riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`. -/
def carrierEquiv : zetaZeroConfig.carrier ≃ LiCriterion.NontrivialZero :=
  Equiv.subtypeEquivRight fun _ => Iff.rfl

theorem carrierEquiv_val (ρ : zetaZeroConfig.carrier) : (carrierEquiv ρ).val = ρ.val := rfl

/-! ## (E2) the multiplicity -/

/-- ξ = ½ s (s − 1) Λ(s) off `0` and `1`, for Bulka's `LiCriterion.riemannXi` -- the same body as `XiZeros.riemannXi`,
whose lemma `XiZeros.xi_eq_half_s_sm1_Lambda` is applied after unfolding both. -/
theorem xi_eq_half_Lambda {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    LiCriterion.riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  have h := XiZeros.xi_eq_half_s_sm1_Lambda hs0 hs1
  unfold XiZeros.riemannXi at h
  unfold LiCriterion.riemannXi
  exact h

/-- **(E2), the lemma of substance.** On `0 < Re ρ`, `ρ ≠ 1`, the analytic order of Bulka's ξ at `ρ` is the analytic
order of Mathlib's `riemannZeta`. Near `ρ`: `ξ = (½ s (s − 1)) · Λ` (`xi_eq_half_Lambda`) and `ζ = Γℝ⁻¹ · Λ`
(`riemannZeta_def_of_ne_zero`); `Λ` is analytic off `0, 1` (`differentiableAt_completedZeta`), `½ s (s − 1)` is entire
and nonzero at `ρ`, `Γℝ⁻¹` is entire (`differentiable_Gammaℝ_inv`) and nonzero at `ρ` (`Gammaℝ_ne_zero_of_re_pos`);
`analyticOrderAt_mul` and `analyticOrderAt_congr` finish. -/
theorem analyticOrderAt_xi_eq_zeta {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderAt LiCriterion.riemannXi ρ = analyticOrderAt riemannZeta ρ := by
  have hne0 : ρ ≠ 0 := by
    rintro rfl
    simp at h0
  have hre : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : {s : ℂ | 0 < s.re} ∩ {s | s ≠ 1} ∈ 𝓝 ρ := (hre.inter isOpen_ne).mem_nhds ⟨h0, h1⟩
  have hΛ : AnalyticAt ℂ completedRiemannZeta ρ := by
    refine DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 0} ∩ {s | s ≠ 1}) ?_ ?_
    · intro s hs
      exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
    · exact (isOpen_ne.inter isOpen_ne).mem_nhds ⟨hne0, h1⟩
  have hp : AnalyticAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) ρ := by
    have hd : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
    exact hd.analyticAt ρ
  have hp0 : (1 / 2 : ℂ) * ρ * (ρ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hne0) (sub_ne_zero.mpr h1)
  have hg : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hg0 : (Gammaℝ ρ)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h0)
  have hxi : LiCriterion.riemannXi =ᶠ[𝓝 ρ]
      (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) * completedRiemannZeta := by
    filter_upwards [hU] with s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    rw [Pi.mul_apply, xi_eq_half_Lambda hs0 hs.2]
  have hz : riemannZeta =ᶠ[𝓝 ρ] (fun s : ℂ => (Gammaℝ s)⁻¹) * completedRiemannZeta := by
    filter_upwards [hU] with s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs0, div_eq_inv_mul]
  rw [analyticOrderAt_congr hxi, analyticOrderAt_congr hz, analyticOrderAt_mul hp hΛ, analyticOrderAt_mul hg hΛ,
    hp.analyticOrderAt_eq_zero.mpr hp0, hg.analyticOrderAt_eq_zero.mpr hg0]

/-- Bulka's multiplicity at a zero of the pairing type: the analytic order of ξ. -/
def xiMult (ρ : LiCriterion.NontrivialZero) : ℕ := analyticOrderNatAt LiCriterion.riemannXi ρ.val

/-- **(E2), as the multiplicities.** At a point of the kernel's carrier, Zeta23's `zeroMult` is Bulka's `xiMult`. -/
theorem zeroMult_eq_xiMult (ρ : zetaZeroConfig.carrier) : zeroMult ρ.val = xiMult (carrierEquiv ρ) := by
  have hρ : IsNontrivialZero ρ.val := ρ.2
  obtain ⟨_, h0, _⟩ := hρ
  unfold zeroMult xiMult analyticOrderNatAt
  rw [carrierEquiv_val, analyticOrderAt_xi_eq_zeta h0 (ne_one_of_mem ρ.2)]

/-- The multiplicity is invariant under the pairing `ρ ↦ 1 − ρ` (Bulka's `analyticOrderNatAt_riemannXi_one_sub`). -/
theorem xiMult_pairedZero (ρ : LiCriterion.NontrivialZero) : xiMult (LiCriterion.pairedZero ρ) = xiMult ρ := by
  unfold xiMult
  rw [LiCriterion.pairedZero_val, LiCriterion.analyticOrderNatAt_riemannXi_one_sub]

/-! ## (E3) the term -/

/-- The direct half of Bulka's summand is the kernel's `liTerm (n + 1)`. -/
theorem pos_term_eq (n : ℕ) (z : ℂ) : 1 - (1 - 1 / z) ^ ((n : ℤ) + 1) = liTerm (n + 1) z := by
  unfold liTerm
  rw [one_div, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- **(E3)** The reflected half of Bulka's summand is `liTerm (n + 1)` at the paired zero `1 − ρ`
(Bulka's `liSummand_pairedZero`, applied at the paired zero, and the pairing's involutivity). -/
theorem neg_term_eq (n : ℕ) (ρ : LiCriterion.NontrivialZero) :
    1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1)) = liTerm (n + 1) (LiCriterion.pairedZero ρ).val := by
  have h := LiCriterion.liSummand_pairedZero n (LiCriterion.pairedZero ρ)
  rw [LiCriterion.pairedZero_involutive ρ] at h
  rw [← pos_term_eq n (LiCriterion.pairedZero ρ).val]
  exact h

/-! ## (E4) and the equality lemma -/

/-- The real Li summand over Bulka's zeros, with Bulka's multiplicity. -/
def liReal (n : ℕ) (ρ : LiCriterion.NontrivialZero) : ℝ := (xiMult ρ : ℝ) * (liTerm n ρ.val).re

/-- `LiCoeff n` as the real Li sum over Bulka's zeros with Bulka's multiplicity, by (E1) and (E2). -/
theorem LiCoeff_eq_liReal (n : ℕ) : LiCoeff n = ∑' ρ : LiCriterion.NontrivialZero, liReal n ρ := by
  rw [LiCoeff_eq, ← carrierEquiv.tsum_eq (liReal n)]
  refine tsum_congr fun ρ => ?_
  unfold liReal
  rw [carrierEquiv_val, ← zeroMult_eq_xiMult, zetaZeroConfig_mult]

/-- The real Li sum over Bulka's zeros converges, transported from the kernel's `liTerm_re_summable`. -/
theorem liReal_summable (n : ℕ) : Summable (liReal n) := by
  refine carrierEquiv.summable_iff.mp ((liTerm_re_summable n).congr fun ρ => ?_)
  simp only [Function.comp_apply, liReal, carrierEquiv_val]
  rw [← zeroMult_eq_xiMult, zetaZeroConfig_mult]

/-- **THE EQUALITY LEMMA (R176)(3), STEP TWO.** The programme's Li coefficient at `n + 1`, a sum over the genuine zeros of
Mathlib's `riemannZeta` with multiplicity the analytic order of ζ, is the real part of Bulka's `n`-th Taylor coefficient
of the log-derivative of `ξ(1/(1 − z))` at `0`. -/
theorem li_coeff_eq_taylorCoeff (n : ℕ) :
    LiCoeff (n + 1) = (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re := by
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by norm_num
  have hs := liReal_summable (n + 1)
  have hsp : Summable (fun ρ => liReal (n + 1) (LiCriterion.pairedZero ρ)) :=
    LiCriterion.pairedZeroEquiv.summable_iff.mpr hs
  have hpair : ∑' ρ : LiCriterion.NontrivialZero, liReal (n + 1) (LiCriterion.pairedZero ρ) =
      ∑' ρ : LiCriterion.NontrivialZero, liReal (n + 1) ρ :=
    LiCriterion.pairedZeroEquiv.tsum_eq (liReal (n + 1))
  have hterm : ∀ ρ : LiCriterion.NontrivialZero,
      ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        ((1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1))) + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1)))).re =
        liReal (n + 1) (LiCriterion.pairedZero ρ) + liReal (n + 1) ρ := by
    intro ρ
    rw [neg_term_eq n ρ, pos_term_eq n ρ.val]
    unfold liReal
    rw [xiMult_pairedZero]
    unfold xiMult
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.add_re]
    ring
  rw [LiCriterion.taylorCoeff_eq_li_symmetrized n, h2, Complex.re_ofReal_mul,
    Complex.re_tsum (LiCriterion.summable_li_symmetrized n)]
  rw [tsum_congr hterm, hsp.tsum_add hs, hpair, LiCoeff_eq_liReal]
  ring

/-! ## Step three -- the composed criterion -/

/-- **LI'S CRITERION, COMPOSED (R176)(3), STEP THREE.** The programme's Li coefficients over the genuine zeros of
Mathlib's `riemannZeta` are all nonnegative if and only if Mathlib's `RiemannHypothesis` holds. `←` is the kernel's
`rh_imp_li_nonneg`; `→` is Bulka's `positivity_implies_RH` through the equality lemma and `rh_equiv_mathlib`. -/
theorem li_nonneg_iff_rh : (∀ n : ℕ, 0 ≤ LiCoeff n) ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [LiCriterion.rh_equiv_mathlib]
    refine LiCriterion.positivity_implies_RH fun n => ?_
    rw [← li_coeff_eq_taylorCoeff]
    exact h (n + 1)
  · exact rh_imp_li_nonneg

/-- **THE CRITERION ON THE ARITHMETIC SIDE.** Every limit, as `δ → 0⁺`, of EF_lit's literature right-hand side at the
symmetric members has nonnegative real part, for every `n`, if and only if Mathlib's `RiemannHypothesis` holds. The
limit exists and is `LiCoeff n` (`li_identity_sym`); the composition is `li_nonneg_iff_rh`. -/
theorem arith_limit_nonneg_iff_rh :
    (∀ (n : ℕ) (L : ℂ), Tendsto (fun δ => EF.literatureRHS (symMember n δ)) (𝓝[>] 0) (𝓝 L) → 0 ≤ L.re) ↔
      RiemannHypothesis := by
  rw [← li_nonneg_iff_rh]
  constructor
  · intro h n
    have := h n _ (li_identity_sym n)
    rwa [Complex.ofReal_re] at this
  · intro h n L hL
    rw [tendsto_nhds_unique hL (li_identity_sym n), Complex.ofReal_re]
    exact h n

end LiCriterionBridge
end SIDEExplicitFormula
