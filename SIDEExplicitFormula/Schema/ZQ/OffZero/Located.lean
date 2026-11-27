/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Located.lean
THIS PROGRAMME'S WORK (act b770, the author's word amending ruling (R380)(4), its (4)(f); relay data/b770_plan.txt (4)(f)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ZERO OF THE CONTROL OFF THE LINE, WITH ITS ENCLOSURE. The control has a zero whose real part lies from x0 = 85326/100000 to
x1 = 105326/100000 and whose height lies from y0 = 16190216/1000000 to y1 = 16390216/1000000, the corners of box A (Box.lean :20-:24)
(`zq_offline_zero_located`). Its route is `zq_offline_zero`'s (SP4.lean :32) read one step further: `min_modulus_zero`
(MinModulus.lean :23) at the centre `cA` with the two bounds `lamF_cA_lt` and `lamF_frontier_ge` gives a zero of `lamF` in the closure
of box A; `zqFn_eq_zero_of_lamF` (Frame.lean :80) and `carrier_of_box` (Carrier.lean :21), as `lamF_min_modulus_zero` has them
(Frame.lean :84-:89), its membership of the carrier; `mem_closure_boxA` (Box.lean :39) the four inequalities. No evaluation is added;
`zq_offline_zero` stands as compiled.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.SP4

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **The zero of the control off the line, with its enclosure**: a member of `zqZeroConfig.carrier` in the closed box
`[x0, x1] × [y0, y1]`. -/
theorem zq_offline_zero_located :
    ∃ ρ ∈ zqZeroConfig.carrier, x0 ≤ ρ.re ∧ ρ.re ≤ x1 ∧ y0 ≤ ρ.im ∧ ρ.im ≤ y1 := by
  obtain ⟨z, hz, h0⟩ :=
    min_modulus_zero boxA_isBounded lamF_diffContOnCl_boxA cA_mem_boxA lamF_cA_lt lamF_frontier_ge
  have hzq : zqFn z = 0 :=
    zqFn_eq_zero_of_lamF (ne_zero_of_mem_closure_boxA hz) (sub_ne_zero.2 (ne_one_of_mem_closure_boxA hz).symm) h0
  exact ⟨z, (carrier_of_box hz hzq).1, mem_closure_boxA hz⟩

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
