/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/LiCfg.lean
THIS PROGRAMME'S WORK (act b669, ruling (R279)(2)-(4); the χ-Li converse, OPEN_TRAILS :11732, :11796) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LI COEFFICIENT OVER A ZERO CONFIGURATION. `liCoeffCfg Z n` is LiWeil.lean's coefficient with `Zeta23.zetaZeroConfig`
replaced by any `Zeta23.ZeroConfig` `Z`: `(1/2) Σ' ρ, m_ρ Re (pairTerm n ρ)`, each point paired with its conjugate inside the
term, so the coefficient is `Σ' ρ, m_ρ Re (1 - (1 - ρ⁻¹) ^ n)` whether or not the carrier is stable under conjugation. Lean's
`tsum` is `0` on an unsummable family; under the configuration's local count `B321.HCount` (the field `count` of
`Schema.WeilConfig`) the family is summable (`liCoeffCfg_summable`, LiWeil.lean's `pair_summable` with
`WeilEF.zero_sum_inv_sq_gen` in place of `WeilEF.zero_sum_inv_sq zetaSeam`). LiWeil's `LiCoeff` is the instance at
`zetaZeroConfig` (`liCoeff_eq_liCoeffCfg`), and the forward half holds over any configuration (`online_imp_liCoeffCfg_nonneg`).
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.LiWeil
import SIDEExplicitFormula.RestBound

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open Zeta23

/-- **The Li coefficient over a configuration:** `(1/2) Σ' ρ ∈ Z, m_ρ Re (pairTerm n ρ)`. -/
def liCoeffCfg (Z : ZeroConfig) (n : ℕ) : ℝ :=
  (1 / 2) * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re

/-- **ζ's coefficient is the configuration's at `zetaZeroConfig`:** `LiCoeff n = liCoeffCfg zetaZeroConfig n`. -/
theorem liCoeff_eq_liCoeffCfg (n : ℕ) : LiWeil.LiCoeff n = liCoeffCfg zetaZeroConfig n := rfl

/-- **The summability, from the configuration's local count:** under `B321.HCount Z A₀`,
`Σ_ρ m_ρ Re (pairTerm n ρ)` converges absolutely -- the finitely many points with `|Im ρ| < 1` excepted. -/
theorem liCoeffCfg_summable (Z : ZeroConfig) {A₀ : ℝ} (hc : B321.HCount Z A₀) (n : ℕ) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (LiWeil.pairTerm n ρ).re) := by
  have hg : Summable (fun ρ : Z.carrier =>
      (9 / 4 * LiWeil.liConst n) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    (WeilEF.zero_sum_inv_sq_gen Z hc.1 hc.2).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : (Z.window (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Z.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hstrip := Z.strip _ hρmem
  have hnorm1 : 1 ≤ ‖(ρ : ℂ)‖ := him.trans (Complex.abs_im_le_norm _)
  have him2 : 1 ≤ (ρ : ℂ).im ^ 2 := by
    have := one_le_pow₀ (n := 2) him
    rwa [sq_abs] at this
  have hρsq : (ρ : ℂ).im ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (ρ : ℂ)) 2
    rwa [sq_abs] at this
  have hγ : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    nlinarith [hstrip.1, hstrip.2]
  have hq0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (gammaOf (ρ : ℂ))
    linarith
  have hn2 : 0 < ‖(ρ : ℂ)‖ ^ 2 := by positivity
  have key : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ (9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    rw [div_le_div_iff₀ hn2 hq0]
    linarith
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hpb := LiWeil.pairTerm_norm_le n hnorm1 hstrip.1 hstrip.2
  have hre_le : |(LiWeil.pairTerm n ρ).re| ≤ ‖LiWeil.pairTerm n ρ‖ := Complex.abs_re_le_norm _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm]
  calc (Z.mult ρ : ℝ) * |(LiWeil.pairTerm n ρ).re|
      ≤ (Z.mult ρ : ℝ) * (LiWeil.liConst n / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hre_le.trans hpb) hm
    _ = (Z.mult ρ : ℝ) * LiWeil.liConst n * (1 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    _ ≤ (Z.mult ρ : ℝ) * LiWeil.liConst n * ((9 / 4) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hm (LiWeil.liConst_nonneg n))
    _ = (9 / 4 * LiWeil.liConst n) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring

/-- **The forward half over a configuration:** if every point of `Z` lies on the line `Re ρ = 1/2`, every `liCoeffCfg Z n`
is nonnegative -- each term's real part is nonnegative there (`LiWeil.pairTerm_re_nonneg_of_re_half`, algebra over `ℂ`), and
`tsum_nonneg` closes it; no summability is needed. -/
theorem online_imp_liCoeffCfg_nonneg (Z : ZeroConfig) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) → ∀ n : ℕ, 0 ≤ liCoeffCfg Z n := by
  intro h n
  unfold liCoeffCfg
  exact mul_nonneg (by norm_num) (tsum_nonneg fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (LiWeil.pairTerm_re_nonneg_of_re_half n (h ρ ρ.2)))

end Schema
end SIDEExplicitFormula
