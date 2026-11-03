/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Main.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3), relay data/b737_offlinezero_plan.txt (d) (e) and :133, STOP POINT SP1) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

SP1, THE CONDITIONAL THEOREM. S3 on box A with S2's differentiability and S4's carrier: a point `c` of box A where `‖zqFn c‖ < m`, with
`m ≤ ‖zqFn‖` on the frontier, gives a member of `zqZeroConfig.carrier` off the line `Re = 1/2`; with `zq_li_nonneg_imp_online_instance`
(EF/Main.lean :205) its contrapositive. Both carry the two numeric hypotheses `hcm` and `hfr`, which nothing here proves: no zero of `zqFn` is
located, and Li nonnegativity is not refuted, by this file.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Diff
import SIDEExplicitFormula.Schema.ZQ.OffZero.MinModulus
import SIDEExplicitFormula.Schema.ZQ.OffZero.Carrier
import SIDEExplicitFormula.Schema.ZQ.EF.Main

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **SP1**: the conditional theorem, its numeric hypotheses `hcm` and `hfr` open. -/
theorem zq_offline_of_box (c : ℂ) (hc : c ∈ boxA) (m : ℝ) (hcm : ‖zqFn c‖ < m)
    (hfr : ∀ z ∈ frontier boxA, m ≤ ‖zqFn z‖) :
    ∃ ρ ∈ zqZeroConfig.carrier, ρ.re ≠ 1 / 2 := by
  obtain ⟨z, hz, h0⟩ := min_modulus_zero boxA_isBounded zqFn_diffContOnCl_boxA hc hcm hfr
  exact ⟨z, carrier_of_box hz h0⟩

/-- **(e)**: the contrapositive of `zq_li_nonneg_imp_online_instance` under SP1's hypotheses, `hcm` and `hfr` open. -/
theorem zq_li_not_nonneg_of_box (c : ℂ) (hc : c ∈ boxA) (m : ℝ) (hcm : ‖zqFn c‖ < m)
    (hfr : ∀ z ∈ frontier boxA, m ≤ ‖zqFn z‖) :
    ¬ ∀ n : ℕ, 0 ≤ Wide.liCoeff zqZeroConfig n := by
  intro hli
  obtain ⟨ρ, hρ, hre⟩ := zq_offline_of_box c hc m hcm hfr
  exact hre (EF.zq_li_nonneg_imp_online_instance hli ρ hρ)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
