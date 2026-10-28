/-
ChainProbe.lean (act b720, ruling (R330)(5)(ii)) -- run by build-module.yml's probe step above the target's modules
(SIDEExplicitFormula.Challenge.H2SignIffRH and SIDEExplicitFormula.Seam). Imported by no module. It reads whether the kernel's
h2_sign_iff_rh has the challenge's statement, by comparing the two declarations' types as expressions, with two controls made the
same way: the statement built by hand from its two constants must compare EQUAL (the construction is sound), and a planted
statement (h2_sign_aim in h2_sign's place) must compare UNEQUAL (the comparison can fail). Then the term check, and the axioms.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some k := env.find? `SIDEExplicitFormula.B321.h2_sign_iff_rh
    | throwError "PROBE ABSENT: SIDEExplicitFormula.B321.h2_sign_iff_rh"
  let some c := env.find? `h2_sign_iff_rh_challenge
    | throwError "PROBE ABSENT: h2_sign_iff_rh_challenge"
  unless env.contains `SIDEExplicitFormula.B321.h2_sign_aim do
    throwError "PROBE ABSENT: SIDEExplicitFormula.B321.h2_sign_aim"
  logInfo m!"PROBE KERNEL TYPE: {k.type}"
  logInfo m!"PROBE CHALLENGE TYPE: {c.type}"
  if k.type == c.type then
    logInfo "PROBE MATCH: the kernel's h2_sign_iff_rh has the challenge's statement (the two types equal as expressions)"
  else
    logInfo "PROBE DIFFER: the kernel's h2_sign_iff_rh does not have the challenge's statement"
  let built := mkApp2 (mkConst ``Iff) (mkConst `SIDEExplicitFormula.B321.h2_sign) (mkConst `RiemannHypothesis)
  if built == k.type then
    logInfo "PROBE CONTROL 1 EQUAL, as wanted: the statement built from its two constants equals the kernel's type"
  else
    logInfo "PROBE CONTROL 1 FAILED: the statement built from its two constants differs from the kernel's type"
  let planted := mkApp2 (mkConst ``Iff) (mkConst `SIDEExplicitFormula.B321.h2_sign_aim) (mkConst `RiemannHypothesis)
  if planted == k.type then
    logInfo "PROBE CONTROL 2 FAILED: the planted statement compared equal"
  else
    logInfo "PROBE CONTROL 2 UNEQUAL, as wanted: the planted statement (h2_sign_aim in h2_sign's place) differs"

theorem b720_probe_term_check : SIDEExplicitFormula.B321.h2_sign ↔ RiemannHypothesis :=
  SIDEExplicitFormula.B321.h2_sign_iff_rh

#print axioms h2_sign_iff_rh_challenge
#print axioms SIDEExplicitFormula.B321.h2_sign_iff_rh
#print axioms b720_probe_term_check
