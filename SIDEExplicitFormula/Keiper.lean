/-
SIDE-explicit-formula -- SIDEExplicitFormula/Keiper.lean
THIS PROGRAMME'S WORK (act b601, ruling (R211)(4); W-ORD-KEIPER-FACE, OPEN_TRAILS :11704, re-priced at :12132) -- NOT
VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE WORK-ORDER'S LEMMA (1), THE KEIPER-TAYLOR IDENTITY, AS A PROP, WITH ITS OBLIGATIONS NAMED. The Li coefficient is Bulka's
Taylor coefficient (`LiCriterionBridge.li_coeff_eq_taylorCoeff`, v0.9: `LiCoeff (n + 1) = (taylorCoeff riemannXi n).re`).

* THE STIELTJES CONSTANTS, DEFINED ON MATHLIB'S OBJECTS AT THE PIN. Mathlib's `riemannZeta₀` is ζ's regular part at 1 --
  `riemannZeta s − (s − 1)⁻¹` off 1, Euler's γ at 1 -- entire (`differentiable_riemannZeta₀`, whose proof consumes
  `tendsto_riemannZeta_sub_one_div`); `stieltjes n` is `(−1)^n` times its `n`-th derivative at 1, so that ζ(s) = 1/(s − 1)
  + Σ (−1)^n γ_n/n! (s − 1)^n and `stieltjes 0 = γ` (`riemannZeta₀_one`), the limit read beside it
  (`stieltjes_zero_limit`). Mathlib's `riemannZeta₁` is (s − 1) ζ(s) with its pole removed; its value 1 at 1 is the residue
  `riemannZeta_residue_one` carries (`tendsto_riemannZeta₁_residue`), its derivative there γ (`deriv_riemannZeta₁_one`).
* THE KEIPER SUM. With ξ = ½ s (s − 1) π^(−s/2) Γ(s/2) ζ(s), the logarithmic derivative of ξ splits at 1 into 1/s, that of
  (s − 1) ζ(s), and that of Γℝ(s) = π^(−s/2) Γ(s/2); its `k`-th Taylor coefficient there is `keiperA k = (−1)^k +
  zetaLogCoeff k + gammaRLogCoeff k`, and the substitution s = 1/(1 − z) turns these into Bulka's coefficient by the binomial
  transform: `keiperSum n = Σ_{k ≤ n} C(n + 1, k + 1) · keiperA k`. `KeiperTaylor` is the identity `taylorCoeff riemannXi n
  = keiperSum n` for every `n`; `KeiperTaylorIdentity` adds the two readings that put it in the constants the work-order
  names -- `StieltjesLog` (the power-series logarithm: the coefficients of (s − 1) ζ(s)'s logarithmic derivative in the
  Stieltjes constants) and `GammaRZetaValues` (Γℝ's coefficients past the first as the zeta values the polygamma values at
  1/2 give).
* CARRIED TO FOUR NAMED OBLIGATIONS (`KeiperObligations`): `BinomialTransform`, `LogDerivSplit`, `StieltjesLog`,
  `GammaRZetaValues`; `keiperTaylorIdentity_of` derives the Prop from them, at INTERFACES. Three of the four are proved here
  at their first index (`binomialTransform_zero`, `logDerivSplit_zero`, `stieltjesLog_zero`), and the identity at `n = 0`
  is proved outright (`keiperTaylor_zero`): Keiper's λ_1 = 1 + γ/2 − ½ log 4π (`liCoeff_one_keiper`), from Mathlib's
  `completedRiemannZeta₀_one`, `Complex.hasDerivAt_Gammaℝ_one` and `tendsto_riemannZeta_sub_one_div`.

The numerical agreement of the sum with the three-way bench (relay data/b589_three_way.txt) is the bench's, not the
kernel's. Nothing here assumes a value of any Stieltjes constant: they enter as defined objects. Nothing here is a
statement about the zeros of ζ beyond these theorems' own words, or proves RH or any sign of any λ_n.
-/
import SIDEExplicitFormula.LiCriterionBridge
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Keiper

/-! ## The Stieltjes constants, defined on Mathlib's `riemannZeta₀` -/

/-- **THE STIELTJES CONSTANTS**: `γ_n = (−1)^n · riemannZeta₀⁽ⁿ⁾(1)`, so that ζ(s) = 1/(s − 1) + Σ (−1)^n γ_n/n! (s − 1)^n. -/
def stieltjes (n : ℕ) : ℂ := (-1) ^ n * iteratedDeriv n riemannZeta₀ 1

/-- `riemannZeta₀` is analytic at 1 (Mathlib's `differentiable_riemannZeta₀`), so the constants are its Taylor coefficients. -/
theorem analyticAt_riemannZeta₀ : AnalyticAt ℂ riemannZeta₀ 1 :=
  differentiable_riemannZeta₀.analyticAt 1

/-- **The zeroth is Euler's γ** (`riemannZeta₀_one`). -/
theorem stieltjes_zero : stieltjes 0 = (Real.eulerMascheroniConstant : ℂ) := by
  simp [stieltjes, iteratedDeriv_zero, riemannZeta₀_one]

/-- **The zeroth by the Mathlib limit**: `ζ(s) − 1/(s − 1) → γ_0` as `s → 1` (`tendsto_riemannZeta_sub_one_div`). -/
theorem stieltjes_zero_limit :
    Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1)) (𝓝[≠] 1) (𝓝 (stieltjes 0)) := by
  rw [stieltjes_zero]
  exact tendsto_riemannZeta_sub_one_div

/-- **The residue, Mathlib's input read at the pin**: `(s − 1) ζ(s) → riemannZeta₁ 1` as `s → 1`
(`riemannZeta_residue_one`). -/
theorem tendsto_riemannZeta₁_residue :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 (riemannZeta₁ 1)) := by
  rw [riemannZeta₁_one]
  exact riemannZeta_residue_one

/-! ## The Keiper sum -/

/-- The `k`-th Taylor coefficient of `f` at `a`. -/
def taylorAt (f : ℂ → ℂ) (a : ℂ) (k : ℕ) : ℂ := iteratedDeriv k f a / (k.factorial : ℂ)

/-- The Taylor coefficients at 1 of ξ'/ξ. -/
def xiLogCoeff (k : ℕ) : ℂ := taylorAt (logDeriv LiCriterion.riemannXi) 1 k

/-- The Taylor coefficients at 1 of the logarithmic derivative of (s − 1) ζ(s). -/
def zetaLogCoeff (k : ℕ) : ℂ := taylorAt (logDeriv riemannZeta₁) 1 k

/-- The Taylor coefficients at 1 of the logarithmic derivative of Γℝ(s) = π^(−s/2) Γ(s/2). -/
def gammaRLogCoeff (k : ℕ) : ℂ := taylorAt (logDeriv Gammaℝ) 1 k

/-- **Keiper's coefficient**: the `k`-th Taylor coefficient at 1 of 1/s, of (s − 1) ζ(s)'s and of Γℝ's logarithmic
derivatives, added. -/
def keiperA (k : ℕ) : ℂ := (-1) ^ k + zetaLogCoeff k + gammaRLogCoeff k

/-- **THE KEIPER SUM**: the binomial transform of Keiper's coefficients. -/
def keiperSum (n : ℕ) : ℂ := ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℂ) * keiperA k

/-- **THE KEIPER-TAYLOR IDENTITY, AS A PROP**: Bulka's `n`-th Taylor coefficient of ξ is the Keiper sum, for every `n`. -/
def KeiperTaylor : Prop := ∀ n : ℕ, LiCriterion.taylorCoeff LiCriterion.riemannXi n = keiperSum n

/-- The Taylor coefficients at 1 of (s − 1) ζ(s): 1, then `(−1)^i γ_i / i!`. -/
def poleCoeff : ℕ → ℂ
  | 0 => 1
  | i + 1 => (-1) ^ i * stieltjes i / (i.factorial : ℂ)

/-- **THE POWER-SERIES LOGARITHM, AS A PROP**: the coefficients of (s − 1) ζ(s)'s logarithmic derivative are fixed by the
Stieltjes constants through `F' = F · (F'/F)`, coefficient by coefficient. -/
def StieltjesLog : Prop :=
  ∀ k : ℕ, ((k + 1 : ℕ) : ℂ) * poleCoeff (k + 1) =
    ∑ i ∈ Finset.range (k + 1), poleCoeff i * zetaLogCoeff (k - i)

/-- **THE POLYGAMMA VALUES AT 1/2, AS A PROP**: Γℝ's coefficients past the first are `(−1)^k (1 − 2^(−(k+2))) ζ(k + 2)`,
since ψ⁽ᵏ⁾(1/2) = (−1)^(k+1) k! (2^(k+1) − 1) ζ(k + 1). -/
def GammaRZetaValues : Prop :=
  ∀ k : ℕ, gammaRLogCoeff (k + 1) = (-1) ^ k * (1 - 1 / (2 : ℂ) ^ (k + 2)) * riemannZeta ((k : ℂ) + 2)

/-- **THE WORK-ORDER'S LEMMA (1), AS A PROP**: the Keiper-Taylor identity, read in the Stieltjes constants, the polygamma
values at 1/2 and log π. -/
def KeiperTaylorIdentity : Prop := KeiperTaylor ∧ StieltjesLog ∧ GammaRZetaValues

/-! ## The obligations, named -/

/-- **(O1) THE BINOMIAL TRANSFORM**: the substitution `s = 1/(1 − z)` in ξ'/ξ. -/
def BinomialTransform : Prop :=
  ∀ n : ℕ, LiCriterion.taylorCoeff LiCriterion.riemannXi n =
    ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℂ) * xiLogCoeff k

/-- **(O2) THE LOGARITHMIC-DERIVATIVE SPLIT AT 1**: ξ = ½ · s · ((s − 1) ζ(s)) · Γℝ(s) near 1. -/
def LogDerivSplit : Prop := ∀ k : ℕ, xiLogCoeff k = keiperA k

/-- **THE OBLIGATIONS WHERE THE PROOF STOPS, NAMED**: (O1) the binomial transform, (O2) the split, (O3) the power-series
logarithm, (O4) the polygamma values at 1/2. -/
structure KeiperObligations : Prop where
  binomial : BinomialTransform
  split : LogDerivSplit
  stieltjesLog : StieltjesLog
  gammaZeta : GammaRZetaValues

/-- **AT INTERFACES ON THE FOUR OBLIGATIONS**: the Keiper-Taylor identity. -/
theorem keiperTaylorIdentity_of (hP : KeiperObligations) : KeiperTaylorIdentity := by
  unfold KeiperTaylorIdentity
  refine ⟨fun n => ?_, hP.stieltjesLog, hP.gammaZeta⟩
  rw [hP.binomial n, keiperSum]
  exact Finset.sum_congr rfl fun k _ => by rw [hP.split k]

/-! ## At the first index: λ_1 -/

/-- ξ'(1) = ½ Λ₀(1). -/
theorem hasDerivAt_xi_one :
    HasDerivAt LiCriterion.riemannXi ((1 / 2 : ℂ) * completedRiemannZeta₀ 1) 1 := by
  have hΛ : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ 1) 1 :=
    (differentiable_completedZeta₀ 1).hasDerivAt
  have h : HasDerivAt (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ))
      (((1 / 2 : ℂ) * 1 * ((1 : ℂ) - 1) + (1 / 2 : ℂ) * 1 * 1) * completedRiemannZeta₀ 1
        + (1 / 2 : ℂ) * 1 * ((1 : ℂ) - 1) * deriv completedRiemannZeta₀ 1) 1 :=
    ((((hasDerivAt_id (1 : ℂ)).const_mul (1 / 2 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).mul hΛ).add_const
      (1 / 2 : ℂ)
  have e : LiCriterion.riemannXi =
      fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ) := by
    funext s
    rfl
  rw [e]
  refine h.congr_deriv ?_
  ring

theorem xi_one : LiCriterion.riemannXi 1 = 1 / 2 := by
  simp [LiCriterion.riemannXi]

/-- **(O1) at its first index's coefficient**: ξ'/ξ at 1 is Λ₀(1). -/
theorem xiLogCoeff_zero : xiLogCoeff 0 = completedRiemannZeta₀ 1 := by
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  simp only [xiLogCoeff, taylorAt, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, logDeriv_apply,
    hasDerivAt_xi_one.deriv, xi_one]
  exact mul_div_cancel_left₀ _ h2

/-- **Bulka's zeroth coefficient is Λ₀(1).** -/
theorem taylorCoeff_xi_zero : LiCriterion.taylorCoeff LiCriterion.riemannXi 0 = completedRiemannZeta₀ 1 := by
  have hm : HasDerivAt (fun z : ℂ => 1 / (1 - z)) 1 0 := by
    have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have h2 := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).div h1 (by norm_num : (1 : ℂ) - 0 ≠ 0)
    refine h2.congr_deriv ?_
    norm_num
  have hx : HasDerivAt LiCriterion.riemannXi ((1 / 2 : ℂ) * completedRiemannZeta₀ 1) ((fun z : ℂ => 1 / (1 - z)) 0) := by
    simpa using hasDerivAt_xi_one
  have hphi : HasDerivAt (LiCriterion.phi LiCriterion.riemannXi) ((1 / 2 : ℂ) * completedRiemannZeta₀ 1 * 1) 0 :=
    hx.comp (0 : ℂ) hm
  have hval : LiCriterion.phi LiCriterion.riemannXi 0 = 1 / 2 := by
    simp [LiCriterion.phi, LiCriterion.riemannXi]
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  show LiCriterion.logDeriv (LiCriterion.phi LiCriterion.riemannXi) 0 / ((Nat.factorial 0 : ℕ) : ℂ) = _
  rw [LiCriterion.logDeriv, hphi.deriv, hval]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  exact mul_div_cancel_left₀ _ h2

/-- **(O1) at `n = 0`.** -/
theorem binomialTransform_zero :
    LiCriterion.taylorCoeff LiCriterion.riemannXi 0 =
      ∑ k ∈ Finset.range (0 + 1), ((0 + 1).choose (k + 1) : ℂ) * xiLogCoeff k := by
  simp [taylorCoeff_xi_zero, xiLogCoeff_zero]

/-- **(O3) at `k = 0`**: the first coefficient of (s − 1) ζ(s)'s logarithmic derivative is γ_0 (`deriv_riemannZeta₁_one`). -/
theorem zetaLogCoeff_zero : zetaLogCoeff 0 = stieltjes 0 := by
  rw [stieltjes_zero]
  simp only [zetaLogCoeff, taylorAt, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, logDeriv_apply,
    deriv_riemannZeta₁_one, riemannZeta₁_one]

theorem stieltjesLog_zero :
    ((0 + 1 : ℕ) : ℂ) * poleCoeff (0 + 1) = ∑ i ∈ Finset.range (0 + 1), poleCoeff i * zetaLogCoeff (0 - i) := by
  simp [poleCoeff, zetaLogCoeff_zero]

/-- **Γℝ's first coefficient** (`Complex.hasDerivAt_Gammaℝ_one`, `Complex.Gammaℝ_one`): −(γ + log 4π)/2, which is
½ ψ(1/2) − ½ log π. -/
theorem gammaRLogCoeff_zero :
    gammaRLogCoeff 0 = -((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * (Real.pi : ℂ))) / 2 := by
  simp only [gammaRLogCoeff, taylorAt, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, logDeriv_apply,
    Complex.hasDerivAt_Gammaℝ_one.deriv, Complex.Gammaℝ_one]

theorem keiperA_zero :
    keiperA 0 = 1 + (Real.eulerMascheroniConstant : ℂ)
      - ((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * (Real.pi : ℂ))) / 2 := by
  rw [keiperA, zetaLogCoeff_zero, stieltjes_zero, gammaRLogCoeff_zero, pow_zero]
  ring

/-- **(O2) at `k = 0`.** -/
theorem logDerivSplit_zero : xiLogCoeff 0 = keiperA 0 := by
  rw [xiLogCoeff_zero, completedRiemannZeta₀_one, keiperA_zero]
  ring

/-- **THE IDENTITY AT `n = 0`, PROVED.** -/
theorem keiperTaylor_zero : LiCriterion.taylorCoeff LiCriterion.riemannXi 0 = keiperSum 0 := by
  rw [taylorCoeff_xi_zero, completedRiemannZeta₀_one]
  simp only [keiperSum, zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul, keiperA_zero]
  ring

/-- log 4π, on the real line. -/
theorem log_four_pi_ofReal : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
  have e : (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by
    first
    | (push_cast; ring)
    | push_cast
    | simp
  rw [e, Complex.ofReal_log (x := 4 * Real.pi) (by positivity)]

/-- **KEIPER'S λ_1, IN γ AND log 4π**: the programme's Li coefficient at 1 is `1 + γ/2 − ½ log 4π`. -/
theorem liCoeff_one_keiper :
    LiWeil.LiCoeff 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 := by
  have h : LiWeil.LiCoeff 1 = (LiCriterion.taylorCoeff LiCriterion.riemannXi 0).re :=
    LiCriterionBridge.li_coeff_eq_taylorCoeff 0
  rw [taylorCoeff_xi_zero, completedRiemannZeta₀_one, log_four_pi_ofReal] at h
  have hc : ((Real.eulerMascheroniConstant : ℂ) - ((Real.log (4 * Real.pi) : ℝ) : ℂ)) / 2 + 1
      = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ) : ℂ) := by
    first
    | (push_cast; ring)
    | push_cast
  rw [hc, Complex.ofReal_re] at h
  rw [h]
  ring

end Keiper
end SIDEExplicitFormula
