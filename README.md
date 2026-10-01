# SIDE-explicit-formula

**A VENDORED KERNEL. NOTHING IN THIS REPOSITORY IS THIS PROGRAMME'S MATHEMATICS.**

Every `.lean` body here is a byte-identical copy of a file in `anthropics/formal-math`
(the `zeta23` formalization) at the pin recorded below. Each carries a prepended
attribution header and nothing else was changed.

| | |
|:--|:--|
| source | `anthropics/formal-math`, the `zeta23` formalization |
| pin | `v1.0` = `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| modules vendored | 57 -- the local import closure of `Zeta23.WeilEF.Main` |
| of those, derived from PrimeNumberTheoremAnd | 10, under `Zeta23/FromPNTPlus/` |
| toolchain | `leanprover/lean4:v4.33.0-rc2` -- as zeta23 pins it |
| mathlib | `51e6992efd06` -- as zeta23 pins it |
| licence | Apache 2.0; `LICENSE` and `NOTICE` carried whole from the source |

**WHY THE PIN IS `v1.0`.** `EF_lit`'s statement was read at tag `v1.0` and at `fbdc36b` and
the two are byte-identical (sha256 `0255fa699a72c941d7dcb70e0232a0184fb9e0c48c66659a6a237c4022000fe6`), so the order's rule
selects the tag. The comparison is banked at `relay/data/b495_pin.txt`.

**WHAT IS NOT CLAIMED.** This repository has **no profile**. Nothing here has been built or
`#print axioms`'d by this programme at the time of its creation, and **no document of the
corpus cites any terminal in it** until a profile is banked. A vendored copy is not a result,
a push is not a verification, and a launched build is not a built build.

**TOOLCHAIN DIVERGENCE IS EXPECTED.** SPIRAL_MAP section 7 rule 4 pins the federation to one
toolchain "unless stated otherwise"; this kernel states otherwise, and pins what its source
pins, because a vendored body must compile against the library its author compiled it against.

## Amended at act b566 (ruling (R176)(3)) -- the toolchain moved, and a second source vendored

**The two pin rows above are superseded by this section, which is appended; nothing above it is edited.** At b566 the kernel's
toolchain and Mathlib moved to the pins of the second vendored source, after a trial both ways (relay `data/b566_trials.txt`):
the backport of that source to `v4.33.0-rc2` / `51e6992e` stopped on three unknown identifiers (`ite_eq_right`, `ite_eq_left`,
core lemmas that enter Lean at `v4.34.0-rc1`), and the forward move built every module of this kernel with no source edit.

| | |
|:--|:--|
| toolchain | `leanprover/lean4:v4.34.0-rc1` |
| mathlib | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` |
| second source | `github.com/nicholasbulka/li-criterion-rh-equivalence-lean` |
| its pin | `35df682f3b709ffe5fbcfdd452dfa964bd622b87` |
| modules vendored | 33 -- the local import closure of `Lc.LiCriterion.Fidelity`, which contains that of the converse `LiCriterion.positivity_implies_RH`; under `Vendored/Bulka/`, as the library `BulkaVendored` |
| licence | Apache 2.0; its `LICENSE` carried whole at `Vendored/Bulka/LICENSE`; attribution in `NOTICE`; the source carries no NOTICE file |
| bodies | byte-identical to the source at the pin, each under a prepended attribution header carrying its body's sha256 (Zeta23's form) |

**What this programme wrote at b566** is `SIDEExplicitFormula/LiCriterionBridge.lean` (with `AxiomCheckLiCriterion.lean`):
the equality of the kernel's `LiCoeff (n + 1)` with the vendored Taylor coefficient's real part, and from it
`li_nonneg_iff_rh : (∀ n, 0 ≤ LiCoeff n) ↔ RiemannHypothesis` and `arith_limit_nonneg_iff_rh`, the vendored converse consumed
by name. Their prints are banked at relay `data/b566_prints.txt`. A vendored copy is not a result; a print is a print.
