/-
SIDE-explicit-formula -- SIDEExplicitFormula/SaltCheckNonvacuity.lean
THIS PROGRAMME'S WORK (act b642, ruling (R252)(3)(e), W-ORD-PREMISE-NONVACUITY) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SALT-CHECK OF THE PREMISE TABLE, COMPILED. A premise no object satisfies makes every theorem that takes it true and empty.
For each head of the census's premise table this module can reach -- the heads declared in this kernel, and the library's
predicates the table carries as DOMAIN -- one witness: an object that satisfies it, or the theorem of this kernel that proves it,
restated here so that the witness stands in a Salt module.

A witness marked **DEGENERATE** satisfies the structure at a parameter where the structure says nothing -- the zero base, the zero
function, an empty height range. It shows the structure is not empty; it does not show the premise holds at the parameters its
consumer uses. The heads not witnessed here, with each reason, are in the act's bank (data/b642_nonvacuity.txt), not here.

These are statements about premise structures; nothing here proves RH or GRH or locates any zero. 0 sorry, 0 native_decide.
-/
import SIDEExplicitFormula.PowerLimit
import SIDEExplicitFormula.PairTerm
import SIDEExplicitFormula.PlattRung
import SIDEExplicitFormula.LiWeilSym
import Zeta23.Statement.SeamClosed
import SIDEExplicitFormula.Schema.FamilyPremises
import SIDEExplicitFormula.Schema.WindowProofs
import SIDEExplicitFormula.Schema.DedekindRestated

open Complex MeasureTheory Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace SaltCheckNonvacuity

/-! ### Heads declared in this kernel -/

/-- **PWSetup, DEGENERATE**: the zero base, `L = 0`, `M = 1`, at ζ's zero configuration -- every score is `0`. -/
theorem pwSetup_zero : B321.PWSetup Zeta23.zetaZeroConfig (fun _ => 0) 0 1 where
  hev := fun _ => rfl
  hsm := contDiff_const
  hs := by simp
  hL := le_rfl
  hM := one_pos
  hdom := fun ρ _ _ => by simp [B321.offScore, B321.phiC, Zeta23.paperFT]

/-- **zeroSideNeg**: the kernel's `zeroSideNeg_holds`, restated. -/
theorem zeroSideNeg_witness : B321.zeroSideNeg := B321.zeroSideNeg_holds

/-- **farSmall, DEGENERATE**: the zero base -- the far factor and the near integral both `0`. -/
theorem farSmall_zero (γ₀ δ ε : ℝ) : B321.farSmall γ₀ (fun _ => 0) δ ε := by
  simp [B321.farSmall, B321.farFT, B321.nearInt, B321.phiC, Zeta23.paperFT]

/-- **PlattTrudgianHeight, DEGENERATE**: at the height `-1` no zero has `|γ| ≤ -1`. -/
theorem plattTrudgianHeight_neg_one : PlattRung.PlattTrudgianHeight (-1) :=
  ⟨fun ρ _ h => absurd h (by linarith [abs_nonneg ρ.im])⟩

/-- **SymPairBound**: the kernel's `symPair_bound`, restated, at every `n`. -/
theorem symPairBound_witness (n : ℕ) : LiWeil.SymPairBound n := LiWeil.symPair_bound n

/-- **ZetaSeam**: the kernel's `Zeta23.zetaSeam`, restated. -/
theorem zetaSeam_witness : Zeta23.ZetaSeam := Zeta23.zetaSeam

/-- **IsTrivialPoint**: `-(parity χ)` is a trivial point of every character, at `m = 0`. -/
theorem isTrivialPoint_parity {N : ℕ} (χ : DirichletCharacter ℂ N) :
    GRHWeil.IsTrivialPoint χ (-((2 * 0 + GRHWeil.parity χ : ℕ) : ℂ)) :=
  ⟨0, rfl⟩

/-- **EulerFactorPremise**: at `q = 3`, the kernel's `eulerFactorPremise_three`, restated. -/
theorem eulerFactorPremise_witness : Schema.Family.EulerFactorPremise 3 := Schema.Family.eulerFactorPremise_three

/-- **WindowObligations**: at every `W` and `h`, the kernel's `windowObligations_holds`, restated. -/
theorem windowObligations_witness (W h : ℝ) : Schema.PlateauRamp.WindowObligations W h :=
  Schema.PlateauRamp.windowObligations_holds W h

/-- **TrivialSummandPremise', the head this act adds**: at the constant `1`, the kernel's witness, restated. -/
theorem trivialSummandPremise'_witness' : Schema.Dedekind.TrivialSummandPremise' (fun _ => 1) :=
  Schema.Dedekind.trivialSummandPremise'_witness

/-! ### The library's predicates the table carries as DOMAIN -/

theorem analyticOnNhd_witness : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ := analyticOnNhd_id

theorem continuous_witness : Continuous (fun x : ℝ => x) := continuous_id

theorem eqOn_witness : Set.EqOn (fun x : ℝ => x + 0) (fun x => x) Set.univ := fun x _ => add_zero x

theorem hasCompactSupport_witness : HasCompactSupport (Schema.PlateauRamp.box 1) :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => by
    simp only [Schema.PlateauRamp.box, Set.indicator_of_notMem hx]

theorem hasDerivAt_witness : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0

theorem integrable_witness : Integrable (Schema.PlateauRamp.box 1) := Schema.PlateauRamp.box_integrable 1

theorem isOpen_witness : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi

theorem isRoot_witness : (Polynomial.X - Polynomial.C (1 : ℚ)).IsRoot 1 := by simp

theorem monotone_witness : Monotone (fun x : ℝ => x) := monotone_id

theorem nat_prime_witness : Nat.Prime 2 := Nat.prime_two

theorem prime_witness : Prime (2 : ℕ) := Nat.prime_iff.mp Nat.prime_two

theorem strictMono_witness : StrictMono (fun n : ℕ => n) := strictMono_id

theorem tendsto_witness : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat

end SaltCheckNonvacuity
end SIDEExplicitFormula
