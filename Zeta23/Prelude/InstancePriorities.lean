/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : anthropics/formal-math, the `zeta23` formalization
Source path: Zeta23/Prelude/InstancePriorities.lean
Pin        : v1.0 = 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
Copied     : byte-identical; sha256 of the body below = 2c9d2ee602987da89bbbe621149fad2b4a2476699f60535706a12b2fe9833f8e
Licence    : Apache License 2.0 -- see LICENSE and NOTICE, carried whole from the source.

SPIRAL_MAP section 7 rule 7 (composites vendor with attribution) is satisfied by this header.
SPIRAL_MAP section 7 rule 9 (vanilla Lean 4 syntax discipline) is WAIVED for this namespace:
a vendored file is not edited, and the waiver is recorded in SPIRAL_MAP beside rule 9 with
act b495 as its reason.

NOTHING BELOW THIS BLOCK IS THIS PROGRAMME'S WORK, AND NOTHING BELOW IT HAS BEEN ALTERED.
-/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Prelude/InstancePriorities.lean — instance-search hygiene shared by the RvM / PNT⁺ layer.

THE PROBLEM (diagnosed with `set_option trace.Meta.synthInstance true`): once
`Mathlib.Algebra.Lie.OfAssociative` is in scope together with the RCLike normed-algebra instances (as happens in
the import closure of Zeta23.RvM.LocalCount / ReZeroCount / Unconditional), the goal `Module ℝ ℂ` that arises
while resolving `IsBoundedSMul ℝ ℂ` is answered first by
  LieAlgebra.toModule ← LieAlgebra.ofAssociativeAlgebra ← RCLike.toNormedAlgebra,
and that `Module ℝ ℂ` term is not definitionally equal, at instance transparency, to the one carried by
`NormedSpace ℝ ℂ` (InnerProductSpace path).  Consequently `NormedSpace.toIsBoundedSMul` and
`NormedSpace.toNormSMulClass` fail to unify, `ContinuousSMul ℝ ℂ` cannot be synthesized, and every statement of
the form `HasDerivAt (f : ℝ → ℂ) _ _` fails to elaborate downstream (deterministically — not a timeout).
A file-local workaround is `attribute [-instance] LieAlgebra.ofAssociativeAlgebra`.

THE FIX: demote `LieAlgebra.toModule` to low priority, so `Complex.instModule` / the NormedSpace path is tried
first.  This is an instance-search-order change only: no definition or theorem statement changes, the Lie
instance remains available, and the re-prioritisation persists to every importer of this file (a
module importing this + Zeta23.RvM.LocalCount, in either order, elaborates the HasDerivAt probe that fails without
it).  Imported by Zeta23/RvM/LocalCount.lean, Zeta23/RvM/BacklundDefs.lean and Zeta23/FromPNTPlus/StrongPNTPrefix.lean.
If a future Mathlib demotes/removes `LieAlgebra.ofAssociativeAlgebra` as a global instance, this file can be
deleted.
-/
import Mathlib.Algebra.Lie.OfAssociative

attribute [instance 10] LieAlgebra.toModule
