/-
SIDE-explicit-formula -- SIDEExplicitFormula/DetectionRegion.lean
THIS PROGRAMME'S WORK (acts b559 and b560, rulings (R169) and (R170); W-ORD-DETECTION-REGION) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CLEAN PART OF b559's BRANCH, under (R170)(1). The branch `detection-region-b559` (8faf7de) holds these declarations
beside `j₀` and `detection_region`, whose bodies are `sorry`; the no-sorry rule keeps that branch off `main` whole, and
it stays HELD as it is. This file carries only what compiled there with no `sorry`: the finite positivity `h2_sign_upto`
in the kernel's vocabulary and its join to `h2_sign` and to Mathlib's `RiemannHypothesis`. The declarations' bodies are
the branch's, unchanged. `h2_sign_upto_mono`, `ellOf`, `j₀` and `detection_region` are not carried.

WHAT IS COMPILED HERE: positivity on every `classK` window vanishing outside `[-L₀, L₀]`, for every `L₀`, is `h2_sign`,
hence Mathlib's `RiemannHypothesis` through `h2_sign_iff_rh` (Seam.lean:101). Each restriction is a bounded obligation,
finite in support; the conjunction over every `L₀` is the whole clause. Equivalences between open statements: nothing
here proves RH or h2_sign.
-/
import SIDEExplicitFormula.Seam

open Complex
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **(R169)(3)'s finite positivity, in the kernel's vocabulary:** `h2_sign`'s sign on the `classK` windows that vanish
outside `[-L₀, L₀]`. -/
def h2_sign_upto (L₀ : ℝ) : Prop :=
  ∀ k : ℝ → ℂ, classK k → (∀ u : ℝ, L₀ < |u| → k u = 0) → 0 ≤ poleTerm k - primeSum k + archTerm k

/-- `h2_sign` gives the finite positivity at every `L₀`. -/
theorem h2_sign_imp_upto (L₀ : ℝ) : h2_sign → h2_sign_upto L₀ := fun h k hk _ => h k hk

/-- Every `classK` window has compact support, so it vanishes outside some `[-r, r]`: the finite positivity at every
`L₀` is `h2_sign`. -/
theorem upto_all_imp_h2_sign : (∀ L₀ : ℝ, h2_sign_upto L₀) → h2_sign := by
  intro h k hk
  obtain ⟨r, hr⟩ := hk.2.2.1.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine h r k hk (fun u hu => ?_)
  by_contra hne
  have hmem : u ∈ Metric.closedBall (0 : ℝ) r := hr (subset_tsupport k (Function.mem_support.mpr hne))
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith

/-- **The join:** `h2_sign` is the finite positivity at every support bound. -/
theorem h2_sign_iff_forall_upto : h2_sign ↔ ∀ L₀ : ℝ, h2_sign_upto L₀ :=
  ⟨fun h L₀ => h2_sign_imp_upto L₀ h, upto_all_imp_h2_sign⟩

/-- **The join, to Mathlib:** the finite positivity at every support bound is Mathlib's `RiemannHypothesis`, through
`h2_sign_iff_rh` (Seam.lean:101). An equivalence between open statements; it proves neither. -/
theorem forall_upto_iff_rh : (∀ L₀ : ℝ, h2_sign_upto L₀) ↔ RiemannHypothesis :=
  h2_sign_iff_forall_upto.symm.trans h2_sign_iff_rh

end B321
end SIDEExplicitFormula
