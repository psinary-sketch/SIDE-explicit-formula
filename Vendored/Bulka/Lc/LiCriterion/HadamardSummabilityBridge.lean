/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : github.com/nicholasbulka/li-criterion-rh-equivalence-lean
Source path: Lc/LiCriterion/HadamardSummabilityBridge.lean
Pin        : 35df682f3b709ffe5fbcfdd452dfa964bd622b87
Copied     : byte-identical; sha256 of the body below = 6dcd2437505ed6ba99830aceee02c07103aef9fa7b907bbf9ce0bed04f72d8f4
Licence    : Apache License 2.0 -- see Vendored/Bulka/LICENSE, carried whole from the source, and NOTICE.

SPIRAL_MAP section 7 rule 7 (composites vendor with attribution) is satisfied by this header.
SPIRAL_MAP section 7 rule 9 (vanilla Lean 4 syntax discipline) is WAIVED for this namespace:
a vendored file is not edited, and the waiver is recorded in SPIRAL_MAP beside rule 9 with
act b495 as its reason. This file was vendored by act b566 under the author's ruling (R176)(3).

NOTHING BELOW THIS BLOCK IS THIS PROGRAMME'S WORK, AND NOTHING BELOW IT HAS BEEN ALTERED.
-/
/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
import Lc.LiCriterion.Basic
import Hadamard.OrderOne.SummabilityMultiplicity

/-!
# Hadamard Summability Bridge

This file builds the clean bridge from Hadamard order-`≤ 1` hypotheses for `riemannXi`
to the genus-one summability statements used by the Li-criterion development.
-/

open Complex
open scoped Topology

namespace LiCriterion

/-- The nontrivial zeros of `ζ` viewed as a `Hadamard.ZeroSet` for `riemannXi`. -/
noncomputable def xiZeroSet : Hadamard.ZeroSet riemannXi where
  Zero := NontrivialZero
  z := fun ρ => ρ.val
  isZero := by
    intro ρ
    exact (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩

/-- Genus-1 summability from the order-`≤ 1` Hadamard hypotheses for `riemannXi`.

This is the clean replacement path for the old zero-counting bridge: use the multiplicity-aware
Hadamard summability theorem and then compare termwise with the unweighted series, noting that every
zero has multiplicity at least `1`. -/
theorem xi_weighted_genus_one_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    Summable (fun ρ : NontrivialZero =>
      (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  let Z : Hadamard.ZeroSet riemannXi := xiZeroSet
  have : Countable Z.Zero := by
    dsimp [Z, xiZeroSet]
    infer_instance
  have h_zeros_only : ∀ s : ℂ, riemannXi s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ := by
    intro s
    simpa [Z, xiZeroSet] using (xi_zeros_are_nontrivial_zeros (s := s))
  have h_inj : Function.Injective Z.z := by
    intro ρ ρ' h
    exact Subtype.ext h
  have h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0 := by
    intro ρ
    simpa [Z, xiZeroSet] using ρ.ne_zero
  have hsum_mult :
      Summable
        (fun ρ : Z.Zero => (analyticOrderNatAt riemannXi (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) :=
    Hadamard.OrderOne.summable_analyticOrderNatAt_div_norm_sq_of_order_le_one
      (f := riemannXi) (hf_entire := xi_entire) (hf_finite := hfinite) (hf_order_le := horder)
      (Z := Z) (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero)
  simpa [Z, xiZeroSet] using hsum_mult

theorem xi_genus_one_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    Summable (fun (ρ : NontrivialZero) => (1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  exact genus_one_of_weighted_genus (xi_weighted_genus_one_of_hadamard_order_one hfinite horder)

end LiCriterion
