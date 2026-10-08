/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperIdentities.lean
THIS PROGRAMME'S WORK (act b642, ruling (R252)(3)(a); W-ORD-KEIPER-FACE's lemma (1), OPEN_TRAILS :12380) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THREE OF KEIPER'S FOUR OBLIGATIONS (`Keiper.KeiperObligations`), PROVED AT EVERY INDEX FROM THE KERNEL'S DEFINITIONS -- v0.25 proved
each at its first index only (`binomialTransform_zero`, `logDerivSplit_zero`, `stieltjesLog_zero`):

* (O1) `binomialTransform_holds : BinomialTransform`. With `w(z) = (1 - z)⁻¹`, `logDeriv (phi riemannXi)` is `w² · L(w)` (`L` the
  logarithmic derivative of ξ) away from `z = 1`; by induction its `n`-th derivative near 0 is `∑ⱼ β(n,j) w^(n+j+2) L^(j)(w)` with
  `β(n,j) = C(n+1, j+1) n!/j!` (`iterate_deriv_eventually`, the recurrence `binomBeta_succ_succ`), and at `z = 0` that is the
  transform. ξ(1) = 1/2, so `L` is holomorphic on the open set where ξ does not vanish (`xiNe`), 1 in it.
* (O2) `logDerivSplit_holds : LogDerivSplit`. ξ = ½ · s · riemannZeta₁(s) · Γℝ(s) on `re s > 0` (`riemannXi_eq_split`, from
  Mathlib's `completedRiemannZeta_eq`, `riemannZeta_def_of_ne_zero` and `riemannZeta_eq_inv_sub_mul`), so near 1 the logarithmic
  derivative splits into `s⁻¹`, riemannZeta₁'s and Γℝ's (`logDeriv_riemannXi_eventually`), and the Taylor coefficients add; those of
  `s⁻¹` at 1 are `(-1)^k` (Mathlib's `iter_deriv_inv`).
* (O3) `stieltjesLog_holds : StieltjesLog`. `poleCoeff` are riemannZeta₁'s Taylor coefficients at 1 (`poleCoeff_eq`, riemannZeta₁ =
  1 + (s - 1) riemannZeta₀), and `F' = F · (F'/F)` near 1, read coefficient by coefficient by Leibniz's rule (`iteratedDeriv_mul`).

The fourth, (O4) `GammaRZetaValues`, is not proved here: it is DLMF 5.15.3 carried through a derivation the kernel does not hold
(relay data/b641_keiper_status.txt, K4), and `KeiperObligations` stays carried. Nothing here assumes a value of any Stieltjes constant,
is a statement about the zeros of ζ, or proves RH or any sign of any λ_n.
-/
import SIDEExplicitFormula.Keiper

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Keiper

/-! ## (O1) The binomial transform -/

/-- The coefficient of `w^(n+j+2) L^(j)(w)` in the `n`-th derivative: `C(n+1, j+1) n! / j!`. -/
def binomBeta (n j : ℕ) : ℂ := ((n + 1).choose (j + 1) : ℂ) * (n.factorial : ℂ) / (j.factorial : ℂ)

theorem binomBeta_zero_zero : binomBeta 0 0 = 1 := by simp [binomBeta]

theorem binomBeta_top (n : ℕ) : binomBeta n (n + 1) = 0 := by
  simp [binomBeta]

theorem binomBeta_succ_zero (n : ℕ) : binomBeta (n + 1) 0 = ((n + 2 : ℕ) : ℂ) * binomBeta n 0 := by
  simp only [binomBeta, zero_add, Nat.choose_one_right, Nat.factorial_zero, Nat.cast_one, div_one, Nat.factorial_succ]
  push_cast
  ring

theorem choose_key (n j : ℕ) :
    (n + 1) * (n + 2).choose (j + 2) = (n + j + 3) * (n + 1).choose (j + 2) + (j + 1) * (n + 1).choose (j + 1) := by
  rw [show (n + 2).choose (j + 2) = (n + 1).choose (j + 1) + (n + 1).choose (j + 2) from Nat.choose_succ_succ' (n + 1) (j + 1)]
  rcases le_or_gt j n with hjn | hjn
  · obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
    have h := Nat.choose_succ_right_eq (j + d + 1) (j + 1)
    rw [show j + d + 1 - (j + 1) = d by omega] at h
    zify at h ⊢
    linear_combination (-1 : ℤ) * h
  · rw [Nat.choose_eq_zero_of_lt (show n + 1 < j + 1 by omega), Nat.choose_eq_zero_of_lt (show n + 1 < j + 2 by omega)]
    simp

theorem binomBeta_succ_succ (n j : ℕ) :
    binomBeta (n + 1) (j + 1) = ((n + j + 3 : ℕ) : ℂ) * binomBeta n (j + 1) + binomBeta n j := by
  have hk := choose_key n j
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  simp only [binomBeta, Nat.factorial_succ]
  push_cast
  field_simp
  have hk' : ((n : ℂ) + 1) * ((n + 2).choose (j + 2) : ℂ) =
      ((n : ℂ) + j + 3) * ((n + 1).choose (j + 2) : ℂ) + ((j : ℂ) + 1) * ((n + 1).choose (j + 1) : ℂ) := by
    exact_mod_cast hk
  linear_combination (n.factorial : ℂ) * hk'

theorem binomSum_step_algebra (n : ℕ) (w : ℂ) (Lv : ℕ → ℂ) :
    ∑ j ∈ Finset.range (n + 1), binomBeta n j * (((n + j + 2 : ℕ) : ℂ) * w ^ (n + j + 1) * w ^ 2 * Lv j
      + w ^ (n + j + 2) * (Lv (j + 1) * w ^ 2))
      = ∑ j ∈ Finset.range (n + 1 + 1), binomBeta (n + 1) j * (w ^ (n + 1 + j + 2) * Lv j) := by
  let g : ℕ → ℂ := fun j => match j with
    | 0 => 0
    | i + 1 => binomBeta n i * w ^ (n + i + 4) * Lv (i + 1)
  have hR : ∀ j ∈ Finset.range (n + 1 + 1), binomBeta (n + 1) j * (w ^ (n + 1 + j + 2) * Lv j)
      = binomBeta n j * ((n + j + 2 : ℕ) : ℂ) * w ^ (n + j + 3) * Lv j + g j := by
    intro j _
    cases j with
    | zero => simp only [g, binomBeta_succ_zero]; push_cast; ring
    | succ i =>
      simp only [g, binomBeta_succ_succ]
      push_cast
      ring
  rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, Finset.sum_range_succ' g]
  rw [Finset.sum_range_succ (fun j => binomBeta n j * ((n + j + 2 : ℕ) : ℂ) * w ^ (n + j + 3) * Lv j), binomBeta_top]
  simp only [g, zero_mul, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `w(z) = (1 - z)⁻¹`, the substitution `s = 1/(1 - z)`. -/
def wInv (z : ℂ) : ℂ := (1 - z)⁻¹

/-- The iterated derivatives of ξ'/ξ. -/
def Lj (j : ℕ) : ℂ → ℂ := deriv^[j] (logDeriv LiCriterion.riemannXi)

/-- The `n`-th formula: `∑ⱼ β(n,j) w^(n+j+2) L^(j)(w)`. -/
def binomSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), binomBeta n j * (wInv z ^ (n + j + 2) * Lj j (wInv z))

theorem differentiable_riemannXi : Differentiable ℂ LiCriterion.riemannXi := by
  have h : LiCriterion.riemannXi = fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ) := by
    funext s; rfl
  rw [h]
  exact ((((differentiable_id.const_mul (1 / 2 : ℂ)).mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const _)

/-- The open set where ξ does not vanish, 1 in it. -/
def xiNe : Set ℂ := {s | LiCriterion.riemannXi s ≠ 0}

theorem isOpen_xiNe : IsOpen xiNe := isOpen_ne_fun differentiable_riemannXi.continuous continuous_const

theorem one_mem_xiNe : (1 : ℂ) ∈ xiNe := by
  show LiCriterion.riemannXi 1 ≠ 0
  rw [xi_one]; norm_num

theorem differentiableOn_Lj (j : ℕ) : DifferentiableOn ℂ (Lj j) xiNe := by
  induction j with
  | zero =>
    have hd : Differentiable ℂ (deriv LiCriterion.riemannXi) := by
      have := (differentiable_riemannXi.differentiableOn (s := Set.univ)).deriv isOpen_univ
      exact fun x => (this x (Set.mem_univ x)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ x))
    have e : Lj 0 = fun s => deriv LiCriterion.riemannXi s / LiCriterion.riemannXi s := by
      funext s; simp [Lj, logDeriv_apply]
    rw [e]
    exact hd.differentiableOn.div differentiable_riemannXi.differentiableOn fun s hs => hs
  | succ j ih =>
    have e : Lj (j + 1) = deriv (Lj j) := by
      simp only [Lj]; rw [Function.iterate_succ_apply']
    rw [e]
    exact ih.deriv isOpen_xiNe

theorem hasDerivAt_wInv {z : ℂ} (hz : z ≠ 1) : HasDerivAt wInv (wInv z ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => 1 - y) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 := h1.inv hne
  have e : -(-1 : ℂ) / (1 - z) ^ 2 = wInv z ^ 2 := by simp [wInv, inv_pow]
  rw [e] at h2
  exact h2

theorem logDeriv_phi_xi {z : ℂ} (hz : z ≠ 1) :
    LiCriterion.logDeriv (LiCriterion.phi LiCriterion.riemannXi) z = wInv z ^ 2 * Lj 0 (wInv z) := by
  have e : LiCriterion.phi LiCriterion.riemannXi = LiCriterion.riemannXi ∘ wInv := by
    funext y; simp [LiCriterion.phi, wInv, Function.comp]
  rw [LiCriterion.logDeriv_eq_rootLogDeriv, e,
    logDeriv_comp (differentiable_riemannXi _) (hasDerivAt_wInv hz).differentiableAt, (hasDerivAt_wInv hz).deriv]
  simp [Lj]
  ring

/-- **The `n`-th derivative of `logDeriv (phi ξ)` near 0 is the `n`-th formula.** -/
theorem iterate_deriv_eventually (n : ℕ) :
    deriv^[n] (LiCriterion.logDeriv (LiCriterion.phi LiCriterion.riemannXi)) =ᶠ[nhds 0] binomSum n := by
  have hw0 : ContinuousAt wInv 0 := by
    unfold wInv
    exact (continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)
  have hV : ∀ᶠ z in nhds (0 : ℂ), z ≠ 1 ∧ wInv z ∈ xiNe := by
    have h1 : ∀ᶠ z in nhds (0 : ℂ), z ≠ 1 := isOpen_ne.mem_nhds (by norm_num)
    have h2 : ∀ᶠ z in nhds (0 : ℂ), wInv z ∈ xiNe := hw0.preimage_mem_nhds (by
      have : wInv 0 = 1 := by simp [wInv]
      rw [this]; exact isOpen_xiNe.mem_nhds one_mem_xiNe)
    filter_upwards [h1, h2] with z a b using ⟨a, b⟩
  induction n with
  | zero =>
    filter_upwards [hV] with z hz
    simp [binomSum, binomBeta_zero_zero, logDeriv_phi_xi hz.1]
  | succ n ih =>
    rw [Function.iterate_succ']
    refine (ih.deriv).trans ?_
    filter_upwards [hV] with z hz
    apply HasDerivAt.deriv
    have hw := hasDerivAt_wInv hz.1
    have hterm : ∀ j ∈ Finset.range (n + 1), HasDerivAt
        (fun y => binomBeta n j * (wInv y ^ (n + j + 2) * Lj j (wInv y)))
        (binomBeta n j * (((n + j + 2 : ℕ) : ℂ) * wInv z ^ (n + j + 1) * wInv z ^ 2 * Lj j (wInv z)
          + wInv z ^ (n + j + 2) * (Lj (j + 1) (wInv z) * wInv z ^ 2))) z := by
      intro j _
      have hp := hw.pow (n + j + 2)
      have hd : DifferentiableAt ℂ (Lj j) (wInv z) :=
        (differentiableOn_Lj j).differentiableAt (isOpen_xiNe.mem_nhds hz.2)
      have hL : HasDerivAt (Lj j) (Lj (j + 1) (wInv z)) (wInv z) := by
        have e : Lj (j + 1) = deriv (Lj j) := by simp only [Lj]; rw [Function.iterate_succ_apply']
        rw [e]; exact hd.hasDerivAt
      have hc := hL.comp z hw
      have hpm := hp.mul hc
      have := hpm.const_mul (binomBeta n j)
      simp only [show n + j + 2 - 1 = n + j + 1 by omega] at this
      simpa only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] using this
    have hs := HasDerivAt.fun_sum hterm
    unfold binomSum
    rw [← binomSum_step_algebra n (wInv z) (fun j => Lj j (wInv z))]
    exact hs

/-- **(O1), THE BINOMIAL TRANSFORM, AT EVERY INDEX.** -/
theorem binomialTransform_holds : BinomialTransform := by
  intro n
  have h := (iterate_deriv_eventually n).eq_of_nhds
  unfold LiCriterion.taylorCoeff
  rw [h]
  unfold binomSum
  have hw : wInv 0 = 1 := by simp [wInv]
  simp only [hw, one_pow, one_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [xiLogCoeff, taylorAt, binomBeta, Lj, iteratedDeriv_eq_iterate]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  field_simp

/-! ## (O2) The logarithmic-derivative split at 1 -/

/-- Γℝ is differentiable on `re s > 0`. -/
theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun s => (Gammaℝ s)⁻¹) s := differentiable_Gammaℝ_inv.differentiableAt
  have h2 : (Gammaℝ s)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
  have e : Gammaℝ = fun t => ((fun s => (Gammaℝ s)⁻¹) t)⁻¹ := by funext t; simp
  rw [e]
  exact h1.inv h2

/-- ξ = ½ · s · ((s − 1) ζ(s)) · Γℝ(s), on `re s > 0`. -/
theorem riemannXi_eq_split {s : ℂ} (hs : 0 < s.re) :
    LiCriterion.riemannXi s = (1 / 2 : ℂ) * s * riemannZeta₁ s * Gammaℝ s := by
  by_cases h1 : s = 1
  · subst h1
    simp [LiCriterion.riemannXi, riemannZeta₁_one, Gammaℝ_one]
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := riemannZeta_eq_inv_sub_mul h1
  have hd : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero h0
  have hc : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := completedRiemannZeta_eq s
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1s : (1 : ℂ) - s ≠ 0 := by intro h; apply h1; linear_combination -h
  have hz1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [hz]; field_simp
  have hΛ : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [hc]; ring
  simp only [LiCriterion.riemannXi]
  rw [hΛ, hz1, hd]
  field_simp
  ring

/-- `logDeriv` of ξ near 1 splits into the three parts. -/
theorem logDeriv_riemannXi_eventually :
    logDeriv LiCriterion.riemannXi =ᶠ[𝓝 1]
      fun s => s⁻¹ + logDeriv riemannZeta₁ s + logDeriv Gammaℝ s := by
  have hre : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < s.re := by
    have : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact this.mem_nhds (by simp)
  have hz1 := riemannZeta₁_ne_zero_of_near_one
  have hne0 : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 0 := isOpen_ne.mem_nhds one_ne_zero
  have hev : ∀ᶠ s in 𝓝 (1 : ℂ), LiCriterion.riemannXi =ᶠ[𝓝 s]
      fun s => (1 / 2 : ℂ) * s * riemannZeta₁ s * Gammaℝ s := by
    filter_upwards [hre.eventually_nhds] with s hs
    filter_upwards [hs] with t ht using riemannXi_eq_split ht
  filter_upwards [hev, hre, hz1, hne0] with s hs hsre hsz hs0
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsre
  rw [logDeriv_apply, hs.deriv_eq, hs.eq_of_nhds, ← logDeriv_apply]
  have hA : (fun s : ℂ => (1 / 2 : ℂ) * s) s ≠ 0 := by simp [hs0]
  have dA : DifferentiableAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * s) s := by fun_prop
  have dZ : DifferentiableAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁ s
  have dG : DifferentiableAt ℂ Gammaℝ s := differentiableAt_Gammaℝ hsre
  have e1 : logDeriv (fun s => (1 / 2 : ℂ) * s * riemannZeta₁ s * Gammaℝ s) s
      = logDeriv (fun s => (1 / 2 : ℂ) * s * riemannZeta₁ s) s + logDeriv Gammaℝ s :=
    logDeriv_mul (f := fun s => (1 / 2 : ℂ) * s * riemannZeta₁ s) s (mul_ne_zero hA hsz) hG (dA.mul dZ) dG
  have e2 : logDeriv (fun s => (1 / 2 : ℂ) * s * riemannZeta₁ s) s
      = logDeriv (fun s : ℂ => (1 / 2 : ℂ) * s) s + logDeriv riemannZeta₁ s :=
    logDeriv_mul (f := fun s : ℂ => (1 / 2 : ℂ) * s) s hA hsz dA dZ
  have e3 : logDeriv (fun s : ℂ => (1 / 2 : ℂ) * s) s = s⁻¹ := by
    rw [logDeriv_apply]
    have : deriv (fun s : ℂ => (1 / 2 : ℂ) * s) s = 1 / 2 := by
      simpa using (hasDerivAt_id s).const_mul (1 / 2 : ℂ) |>.deriv
    rw [this]; field_simp
  rw [e1, e2, e3]

/-- `logDeriv f` is analytic at a point near which `f` is differentiable and where `f` does not vanish. -/
theorem analyticAt_logDeriv {f : ℂ → ℂ} {x : ℂ} {U : Set ℂ} (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U)
    (hfx : f x ≠ 0) : AnalyticAt ℂ (logDeriv f) x := by
  have ha : AnalyticAt ℂ f x := hf.analyticAt (hU.mem_nhds hx)
  have hd : AnalyticAt ℂ (deriv f) x := ha.deriv
  have : logDeriv f = fun y => deriv f y / f y := by funext y; rw [logDeriv_apply]
  rw [this]
  exact hd.div ha hfx

theorem analyticAt_logDeriv_riemannZeta₁ : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 :=
  analyticAt_logDeriv isOpen_univ (Set.mem_univ _) differentiable_riemannZeta₁.differentiableOn (by simp)

theorem analyticAt_logDeriv_Gammaℝ : AnalyticAt ℂ (logDeriv Gammaℝ) 1 :=
  analyticAt_logDeriv (U := {s : ℂ | 0 < s.re}) (isOpen_lt continuous_const Complex.continuous_re) (by simp)
    (fun s hs => (differentiableAt_Gammaℝ hs).differentiableWithinAt) (by simp [Gammaℝ_one])

/-- **(O2), THE LOGARITHMIC-DERIVATIVE SPLIT AT 1, AT EVERY INDEX.** -/
theorem logDerivSplit_holds : LogDerivSplit := by
  intro k
  unfold xiLogCoeff keiperA zetaLogCoeff gammaRLogCoeff taylorAt
  rw [(logDeriv_riemannXi_eventually.iteratedDeriv k).eq_of_nhds]
  have hinv : ContDiffAt ℂ k (fun s : ℂ => s⁻¹) 1 := contDiffAt_inv ℂ one_ne_zero
  have hZ : ContDiffAt ℂ k (logDeriv riemannZeta₁) 1 := analyticAt_logDeriv_riemannZeta₁.contDiffAt
  have hG : ContDiffAt ℂ k (logDeriv Gammaℝ) 1 := analyticAt_logDeriv_Gammaℝ.contDiffAt
  rw [iteratedDeriv_fun_add (hinv.add hZ) hG, iteratedDeriv_fun_add hinv hZ]
  have h1 : iteratedDeriv k (fun s : ℂ => s⁻¹) 1 = (-1) ^ k * (k.factorial : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
    have := iter_deriv_inv (𝕜 := ℂ) k 1
    simpa using this
  rw [h1]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp

/-! ## (O3) The power-series logarithm -/

theorem contDiff_riemannZeta₀ {n : WithTop ℕ∞} : ContDiff ℂ n riemannZeta₀ :=
  differentiable_riemannZeta₀.contDiff

theorem iteratedDeriv_sub_one (j : ℕ) :
    iteratedDeriv (j + 2) (fun s : ℂ => s - 1) = fun _ => 0 := by
  rw [iteratedDeriv_succ']
  have hd : deriv (fun s : ℂ => s - 1) = fun _ => 1 := by funext s; simp
  rw [iteratedDeriv_succ', hd]
  funext s
  simp

/-- The `(i+1)`-th derivative of `(s - 1) g(s)` at 1 is `(i + 1)` times the `i`-th of `g`. -/
theorem iteratedDeriv_succ_mul_sub_one (g : ℂ → ℂ) (hg : Differentiable ℂ g) (i : ℕ) :
    iteratedDeriv (i + 1) (fun s : ℂ => (s - 1) * g s) 1 = ((i + 1 : ℕ) : ℂ) * iteratedDeriv i g 1 := by
  have hf : ContDiffAt ℂ (i + 1 : ℕ) (fun s : ℂ => s - 1) 1 := by fun_prop
  have hgc : ContDiffAt ℂ (i + 1 : ℕ) g 1 := hg.contDiff.contDiffAt
  have e : (fun s : ℂ => (s - 1) * g s) = (fun s : ℂ => s - 1) * g := rfl
  rw [e, iteratedDeriv_mul hf hgc, Finset.sum_range_succ', Finset.sum_range_succ']
  have h2 : ∀ j ∈ Finset.range i, ((i + 1).choose (j + 1 + 1) : ℂ) * iteratedDeriv (j + 1 + 1) (fun s : ℂ => s - 1) 1 *
      iteratedDeriv (i + 1 - (j + 1 + 1)) g 1 = 0 := by
    intro j _
    rw [show j + 1 + 1 = j + 2 by ring, iteratedDeriv_sub_one]
    simp
  rw [Finset.sum_eq_zero h2]
  have h1 : iteratedDeriv (0 + 1) (fun s : ℂ => s - 1) 1 = 1 := by
    rw [iteratedDeriv_one]; simp
  rw [h1]
  simp [iteratedDeriv_zero]

/-- The coefficients `poleCoeff` are `riemannZeta₁`'s Taylor coefficients at 1. -/
theorem poleCoeff_eq (i : ℕ) : poleCoeff i = iteratedDeriv i riemannZeta₁ 1 / (i.factorial : ℂ) := by
  cases i with
  | zero => simp [poleCoeff, iteratedDeriv_zero, riemannZeta₁_one]
  | succ i =>
    have e : riemannZeta₁ = fun s : ℂ => 1 + (s - 1) * riemannZeta₀ s := rfl
    rw [e, iteratedDeriv_const_add (Nat.succ_pos i), iteratedDeriv_succ_mul_sub_one _ differentiable_riemannZeta₀]
    simp only [poleCoeff, stieltjes]
    have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
    rw [Nat.factorial_succ]
    push_cast
    have hm : ((-1 : ℂ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [hm, one_mul]

/-- **(O3), THE POWER-SERIES LOGARITHM, AT EVERY INDEX.** -/
theorem stieltjesLog_holds : StieltjesLog := by
  intro k
  set F := riemannZeta₁
  set L := logDeriv riemannZeta₁
  have hev : deriv F =ᶠ[𝓝 1] F * L := by
    filter_upwards [riemannZeta₁_ne_zero_of_near_one] with s hs
    simp only [Pi.mul_apply, L, F, logDeriv_apply]
    field_simp
  have hF : ContDiffAt ℂ k F 1 := differentiable_riemannZeta₁.contDiff.contDiffAt
  have hL : ContDiffAt ℂ k L 1 := by
    have ha : AnalyticAt ℂ F 1 := differentiable_riemannZeta₁.differentiableOn.analyticAt Filter.univ_mem
    have : L = fun y => deriv F y / F y := by funext y; simp [L, F, logDeriv_apply]
    rw [this]
    exact (ha.deriv.div ha (by simp [F])).contDiffAt
  have key : iteratedDeriv (k + 1) F 1 = ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) * iteratedDeriv i F 1 * iteratedDeriv (k - i) L 1 := by
    rw [iteratedDeriv_succ', (hev.iteratedDeriv k).eq_of_nhds, iteratedDeriv_mul hF hL]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have lhs : ((k + 1 : ℕ) : ℂ) * poleCoeff (k + 1) = iteratedDeriv (k + 1) F 1 / (k.factorial : ℂ) := by
    rw [poleCoeff_eq, Nat.factorial_succ]
    push_cast
    field_simp
    rfl
  rw [lhs, key, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc := Nat.choose_mul_factorial_mul_factorial hik
  rw [poleCoeff_eq]
  simp only [zetaLogCoeff, taylorAt]
  have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hki : ((k - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (k - i)).ne'
  have hc' : (k.choose i : ℂ) * (i.factorial : ℂ) * ((k - i).factorial : ℂ) = (k.factorial : ℂ) := by exact_mod_cast hc
  field_simp
  rw [← hc']
  ring

end Keiper
end SIDEExplicitFormula
