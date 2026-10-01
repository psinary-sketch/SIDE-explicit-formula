/-
SIDE-explicit-formula -- SIDEExplicitFormula/ResidueDischarge.lean
THIS PROGRAMME'S WORK (act b567, ruling (R177)(5); W-ORD-LI-WEIL-BRIDGE, the residue chain) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE RESIDUE CHAIN'S LI-CHANNEL PREMISE, DISCHARGED. SIDE-lv-conservation's `residue_irreducible`
(SIDELvConservation/ZeroActingPartial.lean :130 at 2f71068, Lean v4.29.1) and `zeroActingPairing_to_RH`
(ZeroActingPairing.lean :66) take, for their sequence `lam`, the premise
`liCriterion : Register4_positivity lam → RiemannHypothesis`. The two kernels share no toolchain, so lv's
`Register4_positivity` (RegisterPentagon.lean :152) is RESTATED here, verbatim in its body, and not imported; at
`lam := LiCoeff` the premise is then a theorem of this kernel:
(L1) `Register4_positivity`, restated -- `∀ n, 1 ≤ n → 0 ≤ lam n`;
(L2) `LiCoeff 0 = 0`, since `liTerm 0 ρ = 1 − (1 − ρ⁻¹)⁰ = 0`;
(L3) `Register4_positivity LiCoeff → RiemannHypothesis`, from (L2) and `li_nonneg_iff_rh`.

The OTHER premise of `residue_irreducible`, `inequalityToPositivity : Register4_channelInequality lam_A lam_Z →
Register4_positivity lam`, is NOT discharged here; lv's theorem keeps its INTERFACES grade in lv. Nothing here proves RH.
-/
import SIDEExplicitFormula.LiCriterionBridge

noncomputable section

namespace SIDEExplicitFormula
namespace ResidueDischarge

open LiWeil

/-- **(L1)** SIDE-lv-conservation's `RegisterPentagon.Register4_positivity` (RegisterPentagon.lean :152 at 2f71068),
restated with its body unchanged: the coefficients of the stream `lam` are nonnegative from `n = 1` on. -/
def Register4_positivity (lam : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n

/-- **(L2)** The zeroth Li coefficient vanishes: every term `liTerm 0 ρ = 1 − (1 − ρ⁻¹)⁰` is `0`. -/
theorem liCoeff_zero : LiCoeff 0 = 0 := by
  rw [LiCoeff_eq]
  simp [liTerm]

/-- **(L3) THE LI-CHANNEL PREMISE, DISCHARGED.** At `lam := LiCoeff`, residue_irreducible's premise
`liCriterion : Register4_positivity lam → RiemannHypothesis` holds: the missing index `n = 0` is (L2), and the rest is
`li_nonneg_iff_rh`. -/
theorem register4_positivity_liCoeff_imp_rh : Register4_positivity LiCoeff → RiemannHypothesis := by
  intro h
  refine LiCriterionBridge.li_nonneg_iff_rh.mp fun n => ?_
  rcases n with _ | n
  · rw [liCoeff_zero]
  · exact h (n + 1) (Nat.succ_pos n)

end ResidueDischarge
end SIDEExplicitFormula
