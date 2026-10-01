/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : github.com/nicholasbulka/li-criterion-rh-equivalence-lean
Source path: Hadamard/ZeroSet.lean
Pin        : 35df682f3b709ffe5fbcfdd452dfa964bd622b87
Copied     : byte-identical; sha256 of the body below = bd0437c14bc7949e7228b357407e832e7a7aa156d51aa6ca8d47ad201040933e
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
Zero sets and canonical products used in the Hadamard factorization development.

This is factored out so downstream files can talk about “a chosen enumeration of zeros”
without importing the (WIP) factorization proof in `FullTheorem.lean`.
-/

import Hadamard.Basic

/-!
# Zero sets of entire functions

The `ZeroSet` structure packaging the zeros of an entire function together with the data the
Hadamard factorization needs, and the associated canonical product.
-/

open scoped BigOperators

namespace Hadamard

/-- A choice of zeros for a function `f`, with explicit enumeration. -/
structure ZeroSet (f : ℂ → ℂ) where
  /-- Index type for the chosen zeros. -/
  Zero : Type
  /-- The underlying complex value of a zero. -/
  z : Zero → ℂ
  /-- Each indexed value is a genuine zero of `f`. -/
  isZero : ∀ ρ : Zero, f (z ρ) = 0

/-- The canonical genus‑1 Weierstrass product over a countable zero set. -/
noncomputable def canonicalProductZeroSet
    {f : ℂ → ℂ} (Z : ZeroSet f) [Countable Z.Zero] (s : ℂ) : ℂ :=
  ∏' ρ : Z.Zero, weierstrass_E 1 (s / Z.z ρ)

end Hadamard
