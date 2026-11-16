/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/Xi.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt rows E2 E3 E4, group A) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE COMPLETED FUNCTION OF `Z_Q`. `lamQ` is `zqPair.Λ`, the product `qBase^(-s) Γ(s) zqFn s` off the poles of `Γ`:
* E2, on `0 < Re s` away from the zeros and `1`: `Λ'/Λ = −log(2π/√23) + ψ + Z'/Z`;
* E3, `Q0` self-dual: `Λ'/Λ(1 − s) = −Λ'/Λ(s)`, no dual function and no root number;
* E4, right of `−1/2` and off `0, 1`: `lamQ s = 0` iff `s` lies in `zqZeroConfig`, the order of `lamQ` the configuration's multiplicity, and `lamQ` free of
  zeros on `Re s ≥ 3/2`, `Re s ≤ −1/2` and a horizontal free of the zeros of `zqFn`.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Count
import SIDEExplicitFormula.Chi.Main

open Complex Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

/-- **`Λ_Q`**, `zqPair.Λ`. -/
def lamQ : ℂ → ℂ := zqPair.Λ

theorem lamQ_eq_mul {s : ℂ} (h0 : s ≠ 0) (hG : Complex.Gamma s ≠ 0) :
    lamQ s = qBase ^ (-s) * Complex.Gamma s * zqFn s :=
  (mul_zqFn_eq h0 hG).symm

theorem lamQ_eq (s : ℂ) : lamQ s = zqPair.Λ₀ s - 1 / s - 1 / (1 - s) := zqPair_Λ_eq s

theorem lamQ_one_sub (s : ℂ) : lamQ (1 - s) = lamQ s := zqPair_Λ_one_sub s

theorem lamQ_analyticAt {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) : AnalyticAt ℂ lamQ z := Lam_analyticAt h0 h1

theorem lamQ_differentiableAt {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) : DifferentiableAt ℂ lamQ z :=
  (lamQ_analyticAt h0 h1).differentiableAt

/-! ### E2: the logarithmic derivative -/

theorem re_pos_ne_zero {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := fun h0 => by
  rw [h0, Complex.zero_re] at hs
  exact lt_irrefl _ hs

/-- On the right half-plane `lamQ` is the product, as germs. -/
theorem lamQ_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    lamQ =ᶠ[𝓝 s] fun u => qBase ^ (-u) * Complex.Gamma u * zqFn u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  exact lamQ_eq_mul (re_pos_ne_zero hu) (Complex.Gamma_ne_zero_of_re_pos hu)

theorem qpow_neg_hasDerivAt (s : ℂ) :
    HasDerivAt (fun u : ℂ => qBase ^ (-u)) (qBase ^ (-s) * Complex.log qBase * (-1)) s :=
  (hasDerivAt_neg' s).const_cpow (Or.inl qBase_ne)

theorem log_qBase : Complex.log qBase = (Real.log lam : ℂ) := by
  rw [qBase_eq, Complex.ofReal_log lam_pos.le]

theorem logDeriv_qpow_neg (s : ℂ) : logDeriv (fun u : ℂ => qBase ^ (-u)) s = -(Real.log lam : ℂ) := by
  have hq := qBase_cpow_ne (-s)
  rw [logDeriv_apply, (qpow_neg_hasDerivAt s).deriv, log_qBase,
    show qBase ^ (-s) * (Real.log lam : ℂ) * (-1) = qBase ^ (-s) * (-(Real.log lam : ℂ)) by ring,
    mul_div_cancel_left₀ _ hq]

theorem Gamma_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gamma s := by
  refine Complex.differentiableAt_Gamma s (fun m hm => ?_)
  have h := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **E2.** `Λ'/Λ = −log(2π/√23) + ψ + Z'/Z`. -/
theorem logDeriv_lamQ {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (hz : zqFn s ≠ 0) :
    logDeriv lamQ s = -(Real.log lam : ℂ) + Complex.digamma s + logDeriv zqFn s := by
  have hev := lamQ_eventuallyEq_mul hs
  have heq : logDeriv lamQ s = logDeriv (fun u => qBase ^ (-u) * Complex.Gamma u * zqFn u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hq : DifferentiableAt ℂ (fun u : ℂ => qBase ^ (-u)) s := (qpow_neg_hasDerivAt s).differentiableAt
  have hG := Gamma_differentiableAt hs
  have hG0 := Complex.Gamma_ne_zero_of_re_pos hs
  have e1 : logDeriv (fun u : ℂ => qBase ^ (-u) * Complex.Gamma u) s
      = logDeriv (fun u : ℂ => qBase ^ (-u)) s + logDeriv Complex.Gamma s :=
    logDeriv_mul s (qBase_cpow_ne _) hG0 hq hG
  have e2 : logDeriv (fun u : ℂ => qBase ^ (-u) * Complex.Gamma u * zqFn u) s
      = logDeriv (fun u : ℂ => qBase ^ (-u) * Complex.Gamma u) s + logDeriv zqFn s :=
    logDeriv_mul s (mul_ne_zero (qBase_cpow_ne _) hG0) hz (hq.mul hG) (zq_differentiableAt h1)
  rw [heq, e2, e1, logDeriv_qpow_neg, Complex.digamma_def]

/-! ### E3: the reflection -/

/-- **E3.** `Λ'/Λ(1 − s) = −Λ'/Λ(s)`. -/
theorem logDeriv_lamQ_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv lamQ (1 - s) = -logDeriv lamQ s := by
  have hcomp : lamQ = lamQ ∘ (fun u : ℂ => 1 - u) := by
    funext u
    exact (lamQ_one_sub u).symm
  have hd : DifferentiableAt ℂ lamQ (1 - s) :=
    lamQ_differentiableAt (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h
      apply hs0
      linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

/-! ### E4: the zeros -/

theorem not_neg_nat {s : ℂ} (hre : -1 / 2 < s.re) (n : ℕ) : s ≠ -((n : ℂ) + 1) := by
  intro e
  have h := congrArg Complex.re e
  simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem Gamma_ne_of_re {s : ℂ} (h0 : s ≠ 0) (hre : -1 / 2 < s.re) : Complex.Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero (fun m => ?_)
  rcases m with _ | n
  · simpa using h0
  · simpa using not_neg_nat hre n

/-- **E4.** Right of `−1/2` and off `0, 1` the zeros of `lamQ` are the configuration. -/
theorem lamQ_eq_zero_iff {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hre : -1 / 2 < s.re) :
    lamQ s = 0 ↔ s ∈ zqZeroConfig.carrier := by
  have hG := Gamma_ne_of_re h0 hre
  have e := lamQ_eq_mul h0 hG
  constructor
  · intro h
    rw [e] at h
    have hz := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (qBase_cpow_ne _) hG)
    show s ≠ 0 ∧ s ≠ 1 ∧ (∀ n : ℕ, s ≠ -((n : ℂ) + 1)) ∧ zqFn s = 0
    exact ⟨h0, h1, not_neg_nat hre, hz⟩
  · intro h
    rw [e, (mem_C h).2.2.2, mul_zero]

/-- **E4.** The order of `lamQ` at a point of the configuration is its multiplicity. -/
theorem analyticOrderNatAt_lamQ {ρ : ℂ} (h : ρ ∈ zqZeroConfig.carrier) :
    analyticOrderNatAt lamQ ρ = zqZeroConfig.mult ρ := by
  obtain ⟨h0, h1, _, _⟩ := mem_C h
  show (analyticOrderAt zqPair.Λ ρ).toNat = (analyticOrderAt zqFn ρ).toNat
  rw [zq_order_eq_Lam h0 h1 (C_gamma_ne h)]

theorem lamQ_ne_zero_of_three_halves_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : lamQ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  rw [lamQ_eq_mul (re_pos_ne_zero hs0) (Complex.Gamma_ne_zero_of_re_pos hs0)]
  exact mul_ne_zero (mul_ne_zero (qBase_cpow_ne _) (Complex.Gamma_ne_zero_of_re_pos hs0))
    (zq_ne_zero_of_three_halves_le s hs)

theorem lamQ_ne_zero_of_re_le {s : ℂ} (hs : s.re ≤ -1 / 2) : lamQ s ≠ 0 := by
  have h : 3 / 2 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  rw [← lamQ_one_sub]
  exact lamQ_ne_zero_of_three_halves_le h

/-- **E4.** `lamQ` is free of zeros on a horizontal where `zqFn` is free of them on `1/2 ≤ Re s ≤ 2`. -/
theorem lamQ_ne_zero_on_horizontals {c R : ℝ} (hc : c ≤ 3 / 2)
    (hL : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 → zqFn s ≠ 0) :
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → lamQ s ≠ 0 := by
  have hright : ∀ w : ℂ, (w.im = R ∨ w.im = -R) → 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → lamQ w ≠ 0 := by
    intro w him h1 h2
    have hw0 : 0 < w.re := by linarith
    rw [lamQ_eq_mul (re_pos_ne_zero hw0) (Complex.Gamma_ne_zero_of_re_pos hw0)]
    exact mul_ne_zero (mul_ne_zero (qBase_cpow_ne _) (Complex.Gamma_ne_zero_of_re_pos hw0))
      (hL w him h1 (by linarith))
  intro s him hr1 hr2
  rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
  · exact hright s him hre (by linarith)
  · rw [← lamQ_one_sub]
    refine hright (1 - s) ?_ ?_ ?_
    · rw [Complex.sub_im, Complex.one_im, zero_sub]
      rcases him with h | h
      · right
        rw [h]
      · left
        rw [h, neg_neg]
    · rw [Complex.sub_re, Complex.one_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re]
      linarith

end EF
end ZQ
end Schema
end SIDEExplicitFormula
