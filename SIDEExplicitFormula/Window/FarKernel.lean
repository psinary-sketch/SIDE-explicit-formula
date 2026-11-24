import SIDEExplicitFormula.Window.ArchLam

/-!
# The far sum`s kernel

`farK d` is the far sum`s kernel at the lag `d` (`archJ_basis_local`, ArchBandLocal.lean :36-:37), as `lamI_closed`
writes `λ(d)`. Nothing here is evaluated.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The far sum`s kernel at the lag `d`. -/
noncomputable def farK (d : ℤ) : ℝ :=
  ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + d - m)

end Window
end SIDEExplicitFormula
