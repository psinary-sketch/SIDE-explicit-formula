/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZeroSummability.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-INSTANCE OF Zeta23/WeilEF/ZeroSummability.lean. Zeta23 proves the zero-side summability for ANY zero configuration
with a two-sided local count (`zero_sum_inv_sq_gen`, `EF_zero_sum_summable_gen`); with `chiZeroConfig_local_count`
(Chi/LocalCount.lean) both apply to `chiZeroConfig`. `EF_zero_sum_summable_chi` is the first conjunct of `EF_lit_chi`
(Chi/Statement.lean): the zero sum `Σ_ρ m_ρ h(γ_ρ)` over the nontrivial zeros of `LFunction χ` converges absolutely for
every `k ∈ C_c²(ℝ)`. The second conjunct, the sum's value, is not proved here.
-/
import SIDEExplicitFormula.Chi.LocalCount
import SIDEExplicitFormula.Chi.Statement
import Zeta23.WeilEF.ZeroSummability

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- `Σ_ρ m_ρ / (1 + |γ_ρ|²)` converges over the nontrivial zeros of `LFunction χ`. -/
theorem chi_zero_sum_inv_sq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    Summable (fun ρ : (chiZeroConfig χ hχ h1).carrier =>
      ((chiZeroConfig χ hχ h1).mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := chiZeroConfig_local_count hχ h1
  exact Zeta23.WeilEF.zero_sum_inv_sq_gen (chiZeroConfig χ hχ h1) hA₀ hloc

/-- **EF_lit_chi's Summable clause.** For every `k ∈ C_c²(ℝ)` the zero sum over the nontrivial zeros of `LFunction χ`,
with multiplicity, converges absolutely. -/
theorem EF_zero_sum_summable_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (chiZeroConfig χ hχ h1).carrier =>
      ((chiZeroConfig χ hχ h1).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := chiZeroConfig_local_count hχ h1
  exact Zeta23.WeilEF.EF_zero_sum_summable_gen (chiZeroConfig χ hχ h1) hA₀ hloc hk hkc

end GRHWeil
end SIDEExplicitFormula
