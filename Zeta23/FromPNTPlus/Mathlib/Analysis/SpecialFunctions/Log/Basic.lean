/-
VENDORED INTO SIDE-explicit-formula -- NOT WRITTEN HERE.

Source     : anthropics/formal-math, the `zeta23` formalization
Source path: Zeta23/FromPNTPlus/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
Pin        : v1.0 = 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
Copied     : byte-identical; sha256 of the body below = b345f59bff825700221040fb575823d6902383ff1ab340b2ff849d8382460954
Licence    : Apache License 2.0 -- see LICENSE and NOTICE, carried whole from the source.

SPIRAL_MAP section 7 rule 7 (composites vendor with attribution) is satisfied by this header.
SPIRAL_MAP section 7 rule 9 (vanilla Lean 4 syntax discipline) is WAIVED for this namespace:
a vendored file is not edited, and the waiver is recorded in SPIRAL_MAP beside rule 9 with
act b495 as its reason.

NOTHING BELOW THIS BLOCK IS THIS PROGRAMME'S WORK, AND NOTHING BELOW IT HAS BEEN ALTERED.
-/
/-
SECOND ATTRIBUTION -- THIS FILE DERIVES FROM PrimeNumberTheoremAnd.

zeta23's own NOTICE names the files under `Zeta23/FromPNTPlus/` as derived from
PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, Apache License 2.0; and states that some
of those in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License 2.0, with their original headers preserved.

THAT CHAIN IS NOT RESTATED HERE AND IS NOT SUMMARISED: the file's own upstream notice,
immediately below, is the record, and it is carried unaltered.
-/
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint
tooling (import Architect, blueprint_comment blocks, @[blueprint ...] attributes),
redirected intra-project imports to Zeta23.FromPNTPlus.*.  Mathematical content unchanged.
Modified 2026 by Anthropic PBC.
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
