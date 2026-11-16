/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/SP4.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (4) G6) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G6, SP4. At the centre `cA = 0.95326 + 16.290216 i` of box A, `‖lamF cA‖ ≤ 6e-13 < 1e-12` (Centre.lean `lamM_centre_encl` through
`lamF_eq_split`); on the frontier `1e-12 ≤ ‖lamF‖` (Frontier.lean `lamF_frontier_ge`). The minimum modulus principle on `lamF` (Frame.lean
`lamF_min_modulus_zero`) gives a member of `zqZeroConfig.carrier` off the critical line, and `lamF_li_not_nonneg` the failure of Li
nonnegativity for `zqZeroConfig`.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Frontier
import SIDEExplicitFormula.Schema.ZQ.OffZero.Centre

open Complex Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

theorem cA_mem_boxA : cA ∈ boxA := by
  rw [boxA, Complex.mem_reProdIm, cA_re, cA_im]
  norm_num [x0, x1, y0, y1]

theorem lamF_cA_lt : ‖lamF cA‖ < 1 / 10 ^ 12 := by
  rw [lamF_eq_split]
  exact lamM_centre_encl.trans_lt (by norm_num)

/-- **SP4 (i)**: `zqZeroConfig` has a member off `Re = 1/2`. -/
theorem zq_offline_zero : ∃ ρ ∈ zqZeroConfig.carrier, ρ.re ≠ 1 / 2 :=
  lamF_min_modulus_zero cA cA_mem_boxA (1 / 10 ^ 12) lamF_cA_lt lamF_frontier_ge

/-- **SP4 (ii)**: Li nonnegativity fails for `zqZeroConfig`. -/
theorem zq_li_nonneg_fails : ¬ (∀ n : ℕ, 0 ≤ Wide.liCoeff zqZeroConfig n) :=
  lamF_li_not_nonneg cA cA_mem_boxA (1 / 10 ^ 12) lamF_cA_lt lamF_frontier_ge

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
