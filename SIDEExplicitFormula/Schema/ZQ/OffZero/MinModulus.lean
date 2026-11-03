/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/MinModulus.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3), relay data/b737_offlinezero_plan.txt (d) S3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S3, THE MINIMUM MODULUS. Mathlib's maximum modulus principle on a bounded set (`Complex.norm_le_of_forall_mem_frontier_norm_le`,
Mathlib/Analysis/Complex/AbsMax.lean :405) applied to `f⁻¹`: were `f` nonzero on the closure, `‖f⁻¹‖ ≤ 1/m` on the frontier would give
`m ≤ ‖f c‖` at a point `c` of the set. So a point below `m` inside, with `m` at most `‖f‖` on the frontier, forces a zero in the closure.
A statement about any `f`; it locates nothing by itself.
-/
import Mathlib.Analysis.Complex.AbsMax

open Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **S3, `min_modulus_zero`**. -/
theorem min_modulus_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U) (hd : DiffContOnCl ℂ f U)
    {c : ℂ} (hc : c ∈ U) {m : ℝ} (hcm : ‖f c‖ < m) (hfr : ∀ z ∈ frontier U, m ≤ ‖f z‖) :
    ∃ z ∈ closure U, f z = 0 := by
  by_contra h
  push_neg at h
  have hm : 0 < m := lt_of_le_of_lt (norm_nonneg _) hcm
  have hle : ‖f⁻¹ c‖ ≤ m⁻¹ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le hU (hd.inv h) (fun z hz => ?_) (subset_closure hc)
    rw [Pi.inv_apply, norm_inv]
    exact inv_anti₀ hm (hfr z hz)
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (h c (subset_closure hc))
  rw [Pi.inv_apply, norm_inv] at hle
  have hmc : m ≤ ‖f c‖ := (inv_le_inv₀ hfc hm).mp hle
  exact absurd hcm (not_lt.mpr hmc)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
