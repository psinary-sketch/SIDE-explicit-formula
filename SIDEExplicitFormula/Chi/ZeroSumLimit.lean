/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZeroSumLimit.lean
THIS PROGRAMME'S WORK (act b571, ruling (R181)(4)(c); W-ORD-GRH-WEIL, act six) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/ZeroSumLimit.lean: along heights `R_j ∈ [j+7, j+8]` the finite sums `Σ_{|γ_ρ| < R_j} m_ρ H(ρ)`
over the nontrivial zeros of `LFunction χ` (the zero term of `rectangle_identity_chi`) converge to the absolutely convergent
tsum over `chiZeroConfig` (`EF_zero_sum_summable_chi`), the windows increasing and exhausting the carrier. Zeta23's proof with
the carrier changed. Nothing here locates any zero.
-/
import SIDEExplicitFormula.Chi.Contour
import SIDEExplicitFormula.Chi.ZeroSummability

open Complex Topology Filter Set

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter Zeta23 Zeta23.WeilEF

variable {N : ℕ} [NeZero N]

/-- **Zero-sum limit for χ.** The truncated zero sums over `|Im ρ| < R_j` converge to the full tsum over the nontrivial zeros
of `LFunction χ`. -/
theorem zero_sum_limit_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | IsNontrivialZeroChi χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMultChi χ ρ : ℂ) * Hfn k ρ) atTop
      (𝓝 (∑' ρ : (chiZeroConfig χ hχ h1).carrier, ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Hfn k ρ)) := by
  classical
  set g : (chiZeroConfig χ hχ h1).carrier → ℂ := fun ρ => ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Hfn k ρ with hg
  -- absolute convergence : Hfn k ρ = paperFT k (gammaOf ρ) definitionally
  have hsum : Summable g := EF_zero_sum_summable_chi hχ h1 hk hkc
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ IsNontrivialZeroChi χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  -- the finite sets, viewed in the carrier subtype
  set s : ℕ → Finset (chiZeroConfig χ hχ h1).carrier :=
    fun j => (Z j).subtype (· ∈ (chiZeroConfig χ hχ h1).carrier) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ s j, g x = ∑ ρ ∈ Z j, (zeroMultChi χ ρ : ℂ) * Hfn k ρ := by
    intro j
    have h1' := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ (chiZeroConfig χ hχ h1).carrier)) (fun ρ : ℂ => (zeroMultChi χ ρ : ℂ) * Hfn k ρ)
    have h2 : (Z j).filter (· ∈ (chiZeroConfig χ hχ h1).carrier) = Z j := by
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
  have hexh : ∀ b : Finset (chiZeroConfig χ hχ h1).carrier, ∃ j, b ≤ s j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : (chiZeroConfig χ hχ h1).carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have hx0 : IsNontrivialZeroChi χ (x : ℂ) := x.2
    have habs := abs_le.mp (hMle x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset (chiZeroConfig χ hχ h1).carrier => ∑ x ∈ S, g x) atTop
      (𝓝 (∑' x, g x)) := by
    exact hsum.hasSum
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]

end GRHWeil
end SIDEExplicitFormula
