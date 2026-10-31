import SIDEExplicitFormula.C2Chain

namespace C2Walk

namespace F403

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- (R338)(4), D = -403: the sweep after row 33 of 375. -/
noncomputable def S1 : Tab := lf

theorem stepS1 : tabEq (sweepAll (-403) 17303 187 33 (-187) Tab.leaf) S1 = true := by
  decide +kernel

theorem reachS1 : sweepAll (-403) 17303 187 33 (-187) Tab.leaf = S1 := tabEq_sound _ _ stepS1

end F403

end C2Walk
