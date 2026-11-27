/-
SIDE-explicit-formula -- SIDEExplicitFormula/SupportPositivity.lean
THIS PROGRAMME'S WORK (act b770, ruling (R380)(4)(c); relay data/b770_plan.txt (4)(c)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

POSITIVITY BY SUPPORT. For a functional `rhs` on test functions, `positiveUpto rhs L` asks `0 ≤ rhs k` at each `k` of classK that
vanishes outside `[-L, L]`. Asked at every `L` it is asked on the whole of classK; asked up to `L'` it is asked up to each `L ≤ L'`;
at zeta's arithmetic side it is `B321.h2_sign_upto` (DetectionRegion.lean :29), by the two definitions. The control's arithmetic side,
`controlSide`, is not positive up to `log 1024`, from `Window.controlFailureExists`, nor up to any `L` at or above it: the control's
critical width, the least support bound at which its arithmetic side takes a value with negative real part, is at most `log 1024`.
Nothing here is computed.
-/
import SIDEExplicitFormula.DetectionRegion
import SIDEExplicitFormula.Window.ArithNeg

open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula

/-- **Positivity up to a support bound**: `0 ≤ rhs k` at each `k` of classK vanishing outside `[-L, L]`. -/
def positiveUpto (rhs : (ℝ → ℂ) → ℂ) (L : ℝ) : Prop :=
  ∀ k, B321.classK k → (∀ u : ℝ, L < |u| → k u = 0) → 0 ≤ rhs k

/-- **Positivity on classK is positivity up to every support bound**, by the proof of `B321.upto_all_imp_h2_sign`
(DetectionRegion.lean :37-:44) with `rhs` in place of zeta's arithmetic side. -/
theorem positive_iff_forall_upto (rhs : (ℝ → ℂ) → ℂ) :
    (∀ k, B321.classK k → 0 ≤ rhs k) ↔ ∀ L, positiveUpto rhs L := by
  constructor
  · intro h L k hk _
    exact h k hk
  · intro h k hk
    have hk' := hk
    obtain ⟨-, -, hcs, -⟩ := hk'
    obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine h r k hk (fun u hu => ?_)
    by_contra hne
    have hmem : u ∈ Metric.closedBall (0 : ℝ) r := hr (subset_tsupport k (Function.mem_support.mpr hne))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    linarith

/-- **From a larger support bound to a smaller.** -/
theorem positiveUpto_mono {rhs : (ℝ → ℂ) → ℂ} {L L' : ℝ} (h : L ≤ L') :
    positiveUpto rhs L' → positiveUpto rhs L := by
  intro hp k hk hz
  exact hp k hk (fun u hu => hz u (lt_of_le_of_lt h hu))

/-- **At zeta's arithmetic side the notion is `B321.h2_sign_upto`**, the two one proposition by their definitions
(DetectionRegion.lean :29-:30). -/
theorem h2_sign_upto_iff (L : ℝ) :
    B321.h2_sign_upto L ↔ positiveUpto (fun k => B321.poleTerm k - B321.primeSum k + B321.archTerm k) L :=
  Iff.rfl

/-- **The control's arithmetic side**: the pole term less the prime-power side with the control's coefficients `cQ` plus
`archTermQ`, the side `B321.ControlFailureExists` names (ControlFailureExists.lean :23-:25). -/
def controlSide (k : ℝ → ℂ) : ℂ :=
  B321.poleTerm k - Schema.primeTermQ Schema.ZQ.cQ k + Schema.archTermQ k

/-- **The control's arithmetic side is not positive up to `log 1024`**, from `Window.controlFailureExists`: at its test function the
side's real part is below `0`. -/
theorem control_not_positiveUpto : ¬ positiveUpto controlSide (Real.log 1024) := by
  intro hp
  obtain ⟨k, hk, hz, hneg⟩ := Window.controlFailureExists
  have h0 := (Complex.le_def.mp (hp k hk hz)).1
  rw [Complex.zero_re] at h0
  exact absurd h0 (not_le.mpr hneg)

/-- **Nor up to any support bound at or above `log 1024`**, by `positiveUpto_mono`. -/
theorem control_not_positiveUpto_of_le {L : ℝ} (h : Real.log 1024 ≤ L) : ¬ positiveUpto controlSide L :=
  fun hp => control_not_positiveUpto (positiveUpto_mono h hp)

end SIDEExplicitFormula
