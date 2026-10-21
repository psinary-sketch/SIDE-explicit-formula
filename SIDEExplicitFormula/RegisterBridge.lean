/-
SIDE-explicit-formula -- SIDEExplicitFormula/RegisterBridge.lean
THIS PROGRAMME'S WORK (act b701, ruling (R311)(2); W-ORD-H2-BRIDGE-THEOREM, PLACE-papers OPEN_TRAILS.md :15334) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CLAUSE AND THE REGISTER FACE, JOINED THROUGH RH. Two theorems this kernel already compiles meet at Mathlib's
`RiemannHypothesis`: `B321.h2_sign_iff_rh` (Seam.lean :101) -- Weil positivity on classK is RH -- and
`PageConverses.register4_positivity_liCoeff_iff_rh` (PageConverses.lean :32) -- the restated register-four positivity
of the Li coefficients is RH; beneath the second stands `LiCriterionBridge.li_nonneg_iff_rh` through `liCoeff_zero`
(ResidueDischarge.lean :41-:46). `ResidueDischarge.Register4_positivity` restates SIDE-lv-conservation's
`RegisterPentagon.Register4_positivity` (v0.13.0, RegisterPentagon.lean :153-:154) with its body unchanged, read
HOLDS-BY-CORRESPONDENCE at every binder before this file was written (relay data/b701_correspondence_restatement.txt).
(S1) `h2_sign ↔ Register4_positivity LiCoeff` -- the two faces' targets equivalent, joined through RH: a translation of
     propositions, not of objects (no map k ↦ lam stands in either kernel; relay data/b699_bridge_plan.txt, binder 1).
(S2) the face's third conjunct's shape: `h2_sign` gives RH under any pairing predicate on two channels and a ledger.
     SIDE-lv-conservation's `ZeroActingPairing` is a structure over its own Register5 objects (ZeroActingPairing.lean
     :37-:47 at v0.13.0) and is not restated here (the two kernels share no toolchain), so the predicate is left free;
     the implication is (S1)'s forward half and adds nothing beyond it.
(The module H2Bridge.lean of act b5xx, the conservation-hypothesis bridge, stands beside this one untouched.)
No new analysis. Nothing here proves RH or h2_sign: (S1) is an equivalence between open statements.
-/
import SIDEExplicitFormula.Seam
import SIDEExplicitFormula.PageConverses

noncomputable section

namespace SIDEExplicitFormula
namespace RegisterBridge

open B321 LiWeil ResidueDischarge PageConverses

/-- **(S1) THE BRIDGE.** Weil positivity on classK is the restated register-four positivity of the Li coefficients,
through RH: `h2_sign_iff_rh.trans register4_positivity_liCoeff_iff_rh.symm`. -/
theorem h2_sign_iff_register4_positivity_liCoeff : h2_sign ↔ Register4_positivity LiCoeff :=
  h2_sign_iff_rh.trans register4_positivity_liCoeff_iff_rh.symm

/-- **(S2)** The face's third conjunct's shape: under any pairing predicate on two channels and a ledger, `h2_sign` gives
`RiemannHypothesis` -- (S1)'s forward half through `h2_sign_iff_rh`; nothing beyond it. -/
theorem h2_sign_imp_pairing_rh (Pairing : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (lam_A lam_Z : ℕ → ℝ) :
    h2_sign → ∀ ledger : ℕ → ℝ, Pairing lam_A lam_Z ledger → RiemannHypothesis :=
  fun h _ _ => h2_sign_iff_rh.mp h

end RegisterBridge
end SIDEExplicitFormula
