import SIDEExplicitFormula.C2Chain

namespace C2Walk

namespace F427

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- (R338)(4), D = -427: the sweep after row 37 of 339. -/
noncomputable def S1 : Tab := lf

theorem stepS1 : tabEq (sweepAll (-427) 14161 169 37 (-169) Tab.leaf) S1 = true := by
  decide +kernel

theorem reachS1 : sweepAll (-427) 14161 169 37 (-169) Tab.leaf = S1 := tabEq_sound _ _ stepS1

end F427

end C2Walk
