/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : github.com/nicholasbulka/li-criterion-rh-equivalence-lean
Source path: Hadamard/General.lean
Pin        : 35df682f3b709ffe5fbcfdd452dfa964bd622b87
Copied     : byte-identical; sha256 of the body below = 4218ddf7b78eef826f696cc9078300bff707b215f096425de125743e1640ab33
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
General finite-order Hadamard factorization — public entry point.

Import this file for the multiplicity-aware, any-finite-order version of
Hadamard's factorization theorem (Conway XI.3.4).
-/

import Hadamard.General.Factorization

/-!
# Genus-1 Hadamard factorization

Aggregator for the general order-`≤ 1` factorization theorem.
-/

namespace Hadamard

export General
  ( canonicalProductZeroSetMultiplicityRank
    canonicalProductZeroSetMultiplicityRank_one
    hadamard_factorization_general )

end Hadamard
