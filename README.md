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

## Appended at act b567 (ruling (R177)(5)-(6)) -- the residue premise, and the representation of L(s, χ) on the strip

**Nothing above this section is edited; the toolchain and pins are b566's.** What this programme wrote at b567:

| module | what it holds |
|:--|:--|
| `SIDEExplicitFormula/ResidueDischarge.lean` | `Register4_positivity`, restated from SIDE-lv-conservation (`RegisterPentagon.lean` :152 at `2f71068`, cited, not imported); `liCoeff_zero`; `register4_positivity_liCoeff_imp_rh : Register4_positivity LiCoeff → RiemannHypothesis` -- the Li-channel premise of lv's `residue_irreducible` at `lam := LiCoeff` |
| `SIDEExplicitFormula/Chi/ZetaBoundsStrip.lean` | for `χ ≠ 1`: `LFunction_eq_mul_integral : L(s, χ) = s ∫_(1,∞) S_χ(t) t^(−s−1) dt` on `0 < re s` (Mathlib's `LSeries_eq_mul_integral`, its Mellin differentiability, the identity theorem); the analogues of Zeta23's `HasDerivAtZeta0`, `Zeta0EqZeta`, `DerivZeta0EqDerivZeta` and `ZetaBnd_aux1b` for `LFunction0` |
| `SIDEExplicitFormula/Chi/Statement.lean` | `literatureRHS_chi` and `EF_lit_chi`, the explicit formula for `χ`, STATED and not proved; the archimedean bracket by parity |

Their prints: `AxiomCheckResidue.lean` and `AxiomCheckChiStrip.lean`, banked at relay `data/b567_residue_prints.txt` and
`data/b567_chi_prints.txt`. Nothing here proves RH or GRH; a print is a print.

## Appended at act b569 (ruling (R179)(2), (6)) -- the page's two converses, and EF_lit's route for χ to its good heights

**Nothing above this section is edited; the toolchain and pins are b566's.** What this programme wrote at b569:

| module | what it holds |
|:--|:--|
| `SIDEExplicitFormula/PageConverses.lean` | `rh_imp_register4_positivity_liCoeff`, `register4_positivity_liCoeff_iff_rh`, `rh_imp_taylorCoeff_nonneg`, `taylorCoeff_nonneg_iff_rh` -- the converses of the two compiled implications the page THE_CLAUSE_AND_ITS_COMPILED_FACES.md carried at v0.10, each a composition of compiled pieces |
| `SIDEExplicitFormula/Chi/ZetaGrowth.lean` | for `χ ≠ 1`: `LFunction χ` entire; `‖L(s, χ)‖ ≤ (N + 1)‖s‖ / Re s` on `0 < Re s`; linear growth and its consumer forms; on `Re s ≥ 2`, `‖L(s, χ) − 1‖ ≤ π²/6 − 1` and the bounds it gives (the analogue of Zeta23's `RvM/ZetaGrowth.lean`) |
| `SIDEExplicitFormula/Chi/LocalCount.lean` | `chiZeroConfig_local_count : N_χ(t, t+1] ≤ A₀ log(|t| + 3)` (the analogue of `RvM/LocalCount.lean`) |
| `SIDEExplicitFormula/Chi/ZeroSummability.lean` | `EF_zero_sum_summable_chi` -- the Summable conjunct of `EF_lit_chi` (Zeta23's generic summability at `chiZeroConfig`) |
| `SIDEExplicitFormula/Chi/XiLogDeriv.lean` | `Λ(·, χ) = gammaFactor χ · L(·, χ)` on `0 < Re s`; `rootNumber_ne_zero`; `Λ'/Λ(1 − s, χ) = −(log N + Λ'/Λ(s, χ⁻¹))` |
| `SIDEExplicitFormula/Chi/CountByIntegral.lean` | the zeros of `Λ(·, χ)` are exactly the nontrivial zeros of `L(·, χ)`; its order on `0 < Re s` |
| `SIDEExplicitFormula/Chi/Landau.lean` | `LFunction_logDeriv_partial_fraction` -- Landau's partial fraction for `L'/L(·, χ)` |
| `SIDEExplicitFormula/Chi/GoodHeights.lean` | `good_heights_chi` -- heights with `L ≠ 0` and `‖L'/L‖ ≪ log²` on the horizontal segments |

`EF_lit_chi`'s proof is HELD at the χ-analogue of Zeta23's `WeilEF/VerticalLine.lean`: for odd `χ` the Γ factor is
`Γℝ(s + 1)`, and Zeta23's `norm_logDeriv_Gammaℝ_le` (from `digamma_growth_strip`, `1/4 ≤ Re w ≤ 1`) does not reach
`σ + 1 ∈ [3/2, 5/2]`; the attempt is on the branch `grh-weil-b569-held` and is not on main. Their prints:
`AxiomCheckConverses.lean` and `AxiomCheckChiRoute.lean`, banked at relay `data/b569_converse_axiomcheck.txt` and
`data/b569_chi_prints.txt`. Nothing here proves RH or GRH; a print is a print.

## Appended at act b570 (ruling (R180)(5)) -- the wider strip, the odd case, the prime and Γ sides for χ, the rectangle

**Nothing above this section is edited; the toolchain and pins are b566's; Zeta23's files are unedited.** What this
programme wrote at b570:

| module | what it holds |
|:--|:--|
| `SIDEExplicitFormula/Chi/GammaWide.lean` | `digamma_growth_strip_wide` (`1/4 ≤ Re s ≤ 2`) and `norm_logDeriv_Gammaℝ_le_wide` (`3/2 ≤ σ ≤ 5/2`): Zeta23's own argument with the interval changed |
| `SIDEExplicitFormula/Chi/VerticalLine.lean` | `norm_logDeriv_gammaFactor_le` (the odd case by the wider strip); the prime side for χ on `Re s = c > 1` (`prime_side_line_chi`: `Σ χ(n)Λ(n) n^(−1/2) k(log n)`, from Mathlib's `LSeries_twist_vonMangoldt_eq`); the Γ side `gamma_line_shift_chi` |
| `SIDEExplicitFormula/Chi/Contour.lean` | `rectangle_identity_chi`: the weighted argument principle for `H·Λ'/Λ(·, χ)`; no pole terms |

`EF_lit_chi`'s proof is HELD at Zeta23's `WeilEF/FullLine.lean`: its fold of the left vertical onto the right line uses
`Λ'/Λ(1 − s) = −Λ'/Λ(s)`, which for χ is `−(log N + Λ'/Λ(s, χ⁻¹))` (`Chi/XiLogDeriv.lean`); FullLine's χ statement carries
χ⁻¹ and the conductor and is not yet stated. Prints: `AxiomCheckChiAct5.lean`, banked at relay `data/b570_chi_prints.txt`.
Nothing here proves RH or GRH; a print is a print.
