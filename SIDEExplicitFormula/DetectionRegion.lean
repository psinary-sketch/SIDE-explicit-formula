/-
SIDE-explicit-formula -- SIDEExplicitFormula/DetectionRegion.lean
THIS PROGRAMME'S WORK (act b559, ruling (R169); W-ORD-DETECTION-REGION) -- NOT VENDORED. SPIRAL_MAP section 7 rule 9
applies here in full: `theorem`, never `lemma`.

HELD ON THE BRANCH `detection-region-b559` (from v0.2 = 5c72cad); NOT MERGED. (R169)(4)'s H9a is REFUTED at this act:
PowerLimit's `zeroSide_eventually_neg` takes its index from `Metric.tendsto_atTop` over a Tannery limit with no rate
(PowerLimit.lean:1092, :1025, :1066), and every constant beneath it is a quantity of the zero configuration beyond the
excluded zero -- the dominant score `M` (PowerWindow.lean:377), the tie and kill sets (`Kp`, `cE`, `Nf`), the
interpolation bound over the tie nodes (PowerWindow.lean:432), and the largest ratio `offScore / M` off those sets (relay
`data/b559_constants.txt`). So `j0` of (R169)(3), a function of `(gamma, delta)` alone, is not written here: it and
`detection_region` are stated with `sorry` bodies on this branch alone, and no `sorry` reaches `main`.

WHAT IS COMPILED HERE: the finite positivity `h2_sign_upto` in the kernel's vocabulary, and its join to `h2_sign`:
positivity on every window vanishing outside `[-L0, L0]`, for every `L0`, is `h2_sign`, hence Mathlib's
`RiemannHypothesis` through `h2_sign_iff_rh` (Seam.lean:101). (R169)(3) types the predicate as
`∀ h ∈ classK, (∀ u, L₀ < |u| → h u = 0) → 0 ≤ weilTest h h`; typed so, it does not elaborate (`classK` is a predicate on
`ℝ → ℂ`, not a set, and `weilTest h h` is a function; relay `data/b559_literal.txt`). The form below states the sign as
`h2_sign` states it (H2Sign.lean:29-31). Nothing here proves RH or h2_sign.
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

/-- A wider support bound asks for more: positivity up to `L₁` gives positivity up to any `L₀ ≤ L₁`. -/
theorem h2_sign_upto_mono {L₀ L₁ : ℝ} (h : L₀ ≤ L₁) : h2_sign_upto L₁ → h2_sign_upto L₀ :=
  fun hL k hk hs => hL k hk (fun u hu => hs u (lt_of_le_of_lt h hu))

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

/-- **The base half-support as the route takes it.** `PWSetup` (PowerLimit.lean:245-251) carries the width `L` as a
parameter and fixes none; the assembly (PowerLimit.lean:1176) takes it from `plateau_dominant`, which takes
`base_nonzero_at`'s witness `1 / (4 (‖z‖ + 1))` (PowerWindow.lean:276) at `z = gammaOf ρ₁`, the excluded zero. The window
of index `j` is supported in `[-(2 ^ (j + 1) * ℓ), 2 ^ (j + 1) * ℓ]` (`power_support`, PowerWindow.lean:129; `weilTest`
doubles it). -/
def ellOf (ρ : ℂ) : ℝ := 1 / (4 * (‖Zeta23.gammaOf ρ‖ + 1))

/-- **HELD -- NOT WRITTEN, (R169)(4) H9a REFUTED.** (R169)(3)'s `j₀ : ℝ → ℝ → ℕ`, to be written from the constants
PowerLimit's lemmas carry. The index of `zeroSide_eventually_neg` is `max J D` (PowerLimit.lean:1093) with `J` from
`Metric.tendsto_atTop` over `rest_tendsto_zero` (:1092), a limit with no rate; `D` and the bound `B` come from
`coeffs_exist` (:683) over the tie nodes and the kill nodes; the tie terms' size `Nf` (:445) and the dominant score `M`
depend on zeros other than the excluded one. The replacing estimate is priced in relay `data/b559_constants.txt`
((E1) a rate given the largest ratio off the tie and kill sets; (E2) those constants bounded by `(γ, δ)` alone, which
needs a separation estimate no compiled lemma carries). The body is `sorry`, on this branch alone. -/
def j₀ (γ δ : ℝ) : ℕ := sorry

/-- **HELD -- STATED, NOT PROVED.** (R169)(3)'s theorem in the kernel's vocabulary: finite positivity up to `L₀` excludes
every zero of zeta in the open strip whose `(γ, δ) = ((gammaOf ρ).re, ρ.re - 1/2)` has `j₀ γ δ * ℓ ≤ L₀`, `ℓ` the base
half-support the route takes (`ellOf`). Its hypothesis is `hL` alone; its conclusion is a fact about `Complex.re` of a zero
of Mathlib's `riemannZeta`. The proof is `sorry`, on this branch alone: `j₀` is not written (H9a). -/
theorem detection_region (L₀ : ℝ) (hL : h2_sign_upto L₀) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (j₀ (Zeta23.gammaOf ρ).re (ρ.re - 1 / 2) : ℝ) * ellOf ρ ≤ L₀ → ρ.re - 1 / 2 = 0 := by
  sorry

end B321
end SIDEExplicitFormula
