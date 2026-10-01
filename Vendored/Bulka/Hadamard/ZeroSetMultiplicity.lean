/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : github.com/nicholasbulka/li-criterion-rh-equivalence-lean
Source path: Hadamard/ZeroSetMultiplicity.lean
Pin        : 35df682f3b709ffe5fbcfdd452dfa964bd622b87
Copied     : byte-identical; sha256 of the body below = 3e1da34ac59ead8b52c4e8750edf9669f324b985bf521fd9d630b16a0372df49
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
/-
Zeros with multiplicity for Hadamard factorization.

This complements `HadamardFactorization.ZeroSet` (which only records an enumeration of distinct
zeros) by also recording a multiplicity for each zero. The primary use is to define a canonical
product where each Weierstrass factor occurs with the appropriate multiplicity.
-/

import Hadamard.ZeroSet

/-!
# Zero sets with multiplicity

`ZeroSetMultiplicity` refines `ZeroSet` with a multiplicity function, and re-indexes the zeros
as a sigma type so that the factorization theorem applies without assuming simple zeros.
-/

open scoped BigOperators

namespace Hadamard

/-- A choice of zeros for `f`, together with a (positive) multiplicity for each zero. -/
structure ZeroSetMultiplicity (f : ℂ → ℂ) extends ZeroSet f where
  /-- Multiplicity attached to each indexed zero. -/
  mult : Zero → ℕ
  /-- Multiplicities are positive. -/
  mult_pos : ∀ ρ : Zero, 0 < mult ρ

namespace ZeroSetMultiplicity

variable {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f)

/-- Repeat each zero according to its multiplicity. -/
def ZeroWithMultiplicity : Type := Σ ρ : Z.Zero, Fin (Z.mult ρ)

/-- The underlying complex value of a repeated zero index. -/
def zWithMultiplicity : Z.ZeroWithMultiplicity → ℂ := fun i => Z.z i.1

@[simp] lemma zWithMultiplicity_mk (ρ : Z.Zero) (k : Fin (Z.mult ρ)) :
    Z.zWithMultiplicity ⟨ρ, k⟩ = Z.z ρ := rfl

/-- The genus‑1 canonical product where each zero occurs with its multiplicity. -/
noncomputable def canonicalProductZeroSetMultiplicity [Countable Z.Zero] (s : ℂ) : ℂ :=
  ∏' i : Z.ZeroWithMultiplicity, weierstrass_E 1 (s / Z.zWithMultiplicity i)

end ZeroSetMultiplicity

end Hadamard
