import Mathlib.Data.Real.Basic

/-!
# The strided sum at `n = 1` in four blocks, as data

`k0Blk0` to `k0Blk3` are the strided sum `Kt 1` of KFast.lean over the blocks of `m` from 16, 4112, 8208 and 12304, each a
halving sum of at most `2 ^ 12` places, so that the kernel evaluates each apart; their sum is `k0Num` (ArchData.lean). Written by
relay tools/b766_k0data.py under (R376)(4)(d); edited by no hand.

The bank`s sha256, less its final line end: 4cbe7be1203883a6d2688b32ed3e1994760530a7acc8942560169267a37048f0
The bank`s sha256, the file whole: bd228144d213356c5c010ca969cfbbf0d88ab1438d7e25937b99bf6b2f645dea
The coefficients` sha256, as the bank`s own field coef_sha: 4702881bfa6f928f
-/

namespace SIDEExplicitFormula
namespace Window

/-- The strided sum at `n = 1` over its block 0. -/
def k0Blk0 : ℤ := 103769772406438891760000000000000000000000

/-- The strided sum at `n = 1` over its block 1. -/
def k0Blk1 : ℤ := 220385702993188557576000000000000000000

/-- The strided sum at `n = 1` over its block 2. -/
def k0Blk2 : ℤ := 676535167242035182000000000000000000

/-- The strided sum at `n = 1` over its block 3. -/
def k0Blk3 : ℤ := 229597927839819655474414942335704

end Window
end SIDEExplicitFormula
