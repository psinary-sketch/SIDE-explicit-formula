/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Time.lean
THIS PROGRAMME'S WORK (act b741, ruling (R351)(3)(a), relay data/b741_c7_plan.txt (4)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE TIMING TERM of (c7)'s kernel route: the real part of `S(cA, r) = Σ_{k<92} (−r)^k/(k! (cA + k))` at `r = 2358242464929431/10^14`
(`lam · 18` to sixteen decimals), an exact sum in `ℚ`, bracketed by `decide +kernel`. Imported by no module; its checking time is the plan's `T`.
No value of `incGamma1` is certified here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Elem

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- The real part of `Σ_{k<n} (−r)^k/(k! (w + k))` at `w = wr + wi i`, in `ℚ`: exact. -/
def sRe (r wr wi : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sRe r wr wi n + (-r) ^ n / (n.factorial : ℚ) * ((wr + n) / ((wr + n) ^ 2 + wi ^ 2))

set_option profiler true in
/-- **(T)** The timing term: `Re S(cA, r_18)` within `1/10^20` of `−480417790/10^20`, by the kernel. -/
theorem time_sRe_18 :
    (-480417790 : ℚ) / 10 ^ 20 - 1 / 10 ^ 20 ≤ sRe (2358242464929431 / 10 ^ 14) (95326 / 100000) (16290216 / 1000000) 92 ∧
      sRe (2358242464929431 / 10 ^ 14) (95326 / 100000) (16290216 / 1000000) 92 ≤ (-480417790 : ℚ) / 10 ^ 20 + 1 / 10 ^ 20 := by
  decide +kernel

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
