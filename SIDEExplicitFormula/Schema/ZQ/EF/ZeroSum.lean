/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/ZeroSum.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt rows E9 E10, group E) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ZERO SUM. E9: over a `WideConfig` with the local count the zero side converges absolutely, Zeta23/WeilEF/ZeroSummability.lean's proof with `|Im γ_ρ| ≤ 1` for `≤ 1/2`, so `e^Λ` for `e^{Λ/2}`, over
`Wide.zero_sum_inv_sq_wide`. E10: along heights `R_j ∈ [j+7, j+8]` the finite sums of the rectangle tend to the tsum over `zqZeroConfig`, Chi/ZeroSumLimit.lean's proof. Break point (2): the wide strip.
Generated from the compiled files by named replacements. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.Xi

open Complex Topology Filter Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

open Zeta23 Zeta23.WeilEF MeasureTheory

/-- **E9.** The zero side converges absolutely for every `k ∈ C_c²(ℝ)`, over any `WideConfig` with the local count. -/
theorem wide_zero_sum_summable (Z : WideConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Wide.N Z t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
  classical
  -- support bound
  obtain ⟨r, hr⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  set Λ : ℝ := max r 0 with hΛ
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ Metric.closedBall (0:ℝ) r := hr (subset_tsupport _ (Function.mem_support.mpr hu))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set C₂ : ℝ := ∫ u, ‖deriv (deriv k) u‖ with hC₂
  have hC₂0 : 0 ≤ C₂ := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 2 * Real.exp Λ * C₂ with hC
  -- comparison series
  have hg := (Wide.zero_sum_inv_sq_wide Z hA₀ hloc').mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  -- exceptional finite set: |Im ρ| < 1 (then possibly ‖γ_ρ‖ < 1)
  have hfin : (Wide.window Z (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Wide.window Z (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, Wide.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2
  -- ‖γ_ρ‖ ≥ |Im ρ| ≥ 1
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖gammaOf (ρ : ℂ)‖ := him.trans (abs_im_le_norm_gammaOf _)
  have hz0 : gammaOf (ρ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hstrip := Z.strip _ hρmem
  have himγ : |(gammaOf (ρ : ℂ)).im| ≤ 1 := by
    rw [gammaOf_im, abs_le]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hFT := norm_paperFT_le_div hk hsupp hz0
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  -- assemble
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0:ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hkey : ‖paperFT k (gammaOf (ρ : ℂ))‖ ≤ C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    have hexp : Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) ≤ Real.exp Λ := by
      exact Real.exp_le_exp.mpr (mul_le_of_le_one_left hΛ0 himγ)
    have hnsq : Complex.normSq (gammaOf (ρ : ℂ)) = ‖gammaOf (ρ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have h2 : 1 / ‖gammaOf (ρ : ℂ)‖ ^ 2 ≤ 2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [hnsq, div_le_iff₀ (by positivity)]
      have : 0 < 1 + ‖gammaOf (ρ:ℂ)‖ ^ 2 := by positivity
      rw [show 2 * (1 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2)) * ‖gammaOf (ρ:ℂ)‖ ^ 2
          = 2 * ‖gammaOf (ρ:ℂ)‖ ^ 2 / (1 + ‖gammaOf (ρ:ℂ)‖ ^ 2) by ring, le_div_iff₀ this]
      nlinarith
    calc ‖paperFT k (gammaOf (ρ : ℂ))‖
        ≤ Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ / ‖gammaOf (ρ : ℂ)‖ ^ 2 := hFT
      _ = Real.exp (|(gammaOf (ρ:ℂ)).im| * Λ) * C₂ * (1 / ‖gammaOf (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ Real.exp Λ * C₂ * (2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hexp hC₂0) h2 (by positivity) (by positivity)
      _ = C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by rw [hC]; ring
  calc (Z.mult ρ : ℝ) * ‖paperFT k (gammaOf (ρ : ℂ))‖
      ≤ (Z.mult ρ : ℝ) * (C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = C * ((Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        ring

/-- **E10. The zero-sum limit.** The truncated zero sums over `|Im ρ| < R_j` converge to the full tsum over `zqZeroConfig`. -/
theorem zq_zero_sum_limit {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | ρ ∈ zqZeroConfig.carrier ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ) atTop
      (𝓝 (∑' ρ : zqZeroConfig.carrier, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ)) := by
  classical
  set g : zqZeroConfig.carrier → ℂ := fun ρ => (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ with hg
  -- absolute convergence : Hfn k ρ = paperFT k (gammaOf ρ) definitionally
  have hsum : Summable g := by
    obtain ⟨A₀, hA₀, hloc⟩ := zq_count_holds
    exact wide_zero_sum_summable zqZeroConfig hA₀ hloc hk hkc
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ ρ ∈ zqZeroConfig.carrier ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  -- the finite sets, viewed in the carrier subtype
  set s : ℕ → Finset zqZeroConfig.carrier :=
    fun j => (Z j).subtype (· ∈ zqZeroConfig.carrier) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ s j, g x = ∑ ρ ∈ Z j, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ := by
    intro j
    have h1' := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ zqZeroConfig.carrier)) (fun ρ : ℂ => (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ)
    have h2 : (Z j).filter (· ∈ zqZeroConfig.carrier) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemZ j ρ).mp hρ).1
    rw [h2] at h1'
    rw [← h1']
    rfl
  -- monotone and exhausting
  have hRmono : ∀ i j : ℕ, i ≤ j → R i ≤ R j := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2, (hR j).1]
  have hmono : Monotone s := by
    intro i j hij x hx
    rw [Finset.mem_subtype, hmemZ] at hx ⊢
    obtain ⟨h1'', h2, h3⟩ := hx
    have := hRmono i j hij
    exact ⟨h1'', by linarith, by linarith⟩
  have hexh : ∀ b : Finset zqZeroConfig.carrier, ∃ j, b ≤ s j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : zqZeroConfig.carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have hx0 : (x : ℂ) ∈ zqZeroConfig.carrier := x.2
    have habs := abs_le.mp (hMle x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset zqZeroConfig.carrier => ∑ x ∈ S, g x) atTop
      (𝓝 (∑' x, g x)) := by
    exact hsum.hasSum
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]

end EF
end ZQ
end Schema
end SIDEExplicitFormula
