/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Continuation.lean
THIS PROGRAMME'S WORK (act b730, ruling (R340)(4), group D of relay data/b730_continuation_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE CONTINUATION FIELD. For `Re s > 1` the Mellin transform of `thetaC − 1` is `Γ(s) qBase^{−s} Z_Q(s)` by Mathlib's Mellin-equals-Dirichlet
lemma, and it is `zqPair.Λ s` by the FE-pair. `zqFn` is `qBase^s (Γ(s)⁻¹ (Λ₀(s) − 1/(1−s)) − Γ(s+1)⁻¹)`: the pole of `Λ` at `0` is absorbed by
`Γ(s+1)⁻¹`, so `zqFn` is holomorphic off `1`. The five clauses of `ZQContinuation` are then read off. This discharges the premise (Z1) for
`zqFn` and no other premise of the instance; nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.FEPair
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

noncomputable section

open MeasureTheory

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- The base of the gamma factor, as a real number. -/
def lam : ℝ := 2 * Real.pi / Real.sqrt 23

theorem lam_pos : 0 < lam := div_pos (mul_pos two_pos Real.pi_pos) sqrt23_pos

theorem pi_mul_cc : Real.pi * cc = lam := by
  unfold lam cc
  ring

theorem qBase_eq : qBase = (lam : ℂ) := rfl

theorem qBase_ne : qBase ≠ 0 := Complex.ofReal_ne_zero.mpr lam_pos.ne'

theorem qBase_cpow_ne (s : ℂ) : qBase ^ s ≠ 0 := fun h =>
  qBase_ne ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- **The theta as a Dirichlet series of exponentials.** -/
theorem hasSum_theta_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => (rQ k : ℂ) * ((Real.exp (-(lam * (k : ℝ)) * t) : ℝ) : ℂ)) (thetaC t - 1) := by
  have hc : 0 < Real.pi * (cc * t) := mul_pos Real.pi_pos (mul_pos cc_pos ht)
  have h := hasSum_fiber (fun k : ℕ => Real.exp (-(Real.pi * (cc * t)) * (k : ℝ)))
    ((lattice_summable hc).congr (fun p => by simp only [qN_cast]))
  have e : ∑' p : ℤ × ℤ, Real.exp (-(Real.pi * (cc * t)) * ((qN p : ℕ) : ℝ)) = thetaU (cc * t) := by
    unfold thetaU
    exact tsum_congr (fun p => by simp only [qN_cast])
  rw [e] at h
  have h0 : HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have h3 : HasSum (fun k : ℕ => (rQ k : ℝ) * Real.exp (-(Real.pi * (cc * t)) * (k : ℝ))) (thetaU (cc * t) - 1) := by
    have e2 : (fun k : ℕ => (rQ k : ℝ) * Real.exp (-(Real.pi * (cc * t)) * (k : ℝ)))
        = fun k : ℕ => (if k = 0 then Real.exp (-(Real.pi * (cc * t)) * ((0 : ℕ) : ℝ))
            else (rQ k : ℝ) * Real.exp (-(Real.pi * (cc * t)) * (k : ℝ))) - (if k = 0 then (1 : ℝ) else 0) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp [rQ_zero]
      · simp [hk]
    rw [e2]
    exact h.sub h0
  have h4 := Complex.hasSum_ofReal.mpr h3
  have e4 : ((thetaU (cc * t) - 1 : ℝ) : ℂ) = thetaC t - 1 := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    rfl
  rw [e4] at h4
  have e5 : (fun k : ℕ => (rQ k : ℂ) * ((Real.exp (-(lam * (k : ℝ)) * t) : ℝ) : ℂ))
      = fun k : ℕ => (((rQ k : ℝ) * Real.exp (-(Real.pi * (cc * t)) * (k : ℝ)) : ℝ) : ℂ) := by
    funext k
    have hx : -(lam * (k : ℝ)) * t = -(Real.pi * (cc * t)) * (k : ℝ) := by
      rw [← pi_mul_cc]
      ring
    rw [hx, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [e5]
  exact h4

/-- **The Mellin transform of the theta is the gamma factor times `Z_Q`.** -/
theorem zqPair_Λ_eq_of_re {s : ℂ} (hs : 1 < s.re) :
    zqPair.Λ s = Complex.Gamma s * qBase ^ (-s) * ZQ s := by
  have hs0 : 0 < s.re := by linarith
  have hp : ∀ k : ℕ, (rQ k : ℂ) = 0 ∨ 0 < lam * (k : ℝ) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · left
      subst hk
      simp [rQ_zero]
    · right
      exact mul_pos lam_pos (by exact_mod_cast hk)
  have hsum : Summable fun k : ℕ => ‖(rQ k : ℂ)‖ / (lam * (k : ℝ)) ^ s.re := by
    have h := (rQ_term_summable hs).mul_left ((lam ^ s.re)⁻¹)
    refine h.congr (fun k => ?_)
    rw [Complex.norm_natCast, Real.mul_rpow lam_pos.le (Nat.cast_nonneg k)]
    ring
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun k : ℕ => (rQ k : ℂ) * ((Real.exp (-(lam * (k : ℝ)) * t) : ℝ) : ℂ))
      ((fun x : ℝ => zqPair.f x - zqPair.f₀) t) := fun _ ht => hasSum_theta_sub_one (Set.mem_Ioi.mp ht)
  have h : HasSum (fun k : ℕ => Complex.Gamma s * (rQ k : ℂ) / ((lam * (k : ℝ) : ℝ) : ℂ) ^ s)
      (mellin (fun x : ℝ => zqPair.f x - zqPair.f₀) s) :=
    hasSum_mellin (a := fun k : ℕ => (rQ k : ℂ)) (p := fun k : ℕ => lam * (k : ℝ))
      (F := fun x : ℝ => zqPair.f x - zqPair.f₀) hp hs0 hF hsum
  have hΛ : mellin (fun x : ℝ => zqPair.f x - zqPair.f₀) s = zqPair.Λ s :=
    (zqPair.hasMellin (show zqPair.k < s.re from hs)).2
  have hterm : ∀ k : ℕ, Complex.Gamma s * (rQ k : ℂ) / ((lam * (k : ℝ) : ℝ) : ℂ) ^ s
      = Complex.Gamma s * qBase ^ (-s) * LSeries.term (fun k => (rQ k : ℂ)) s k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [LSeries.term_zero, rQ_zero]
      simp
    · rw [LSeries.term_of_ne_zero hk, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg lam_pos.le (Nat.cast_nonneg k), Complex.ofReal_natCast, qBase_eq,
        Complex.cpow_neg]
      try beta_reduce
      ring
  rw [hΛ, funext hterm] at h
  exact h.unique ((Summable.hasSum (zq_summable s hs)).mul_left _)

/-- `Λ` written out for the pair. -/
theorem zqPair_Λ_eq (s : ℂ) : zqPair.Λ s = zqPair.Λ₀ s - 1 / s - 1 / (1 - s) := by
  show zqPair.Λ₀ s - (1 / s) • (1 : ℂ) - ((1 : ℂ) / (((1 : ℝ) : ℂ) - s)) • (1 : ℂ) = _
  rw [Complex.ofReal_one]
  simp only [smul_eq_mul, mul_one]

/-- **The continuation.** The pole of `Λ` at `0` is absorbed by `Γ(s + 1)⁻¹`. -/
def zqFn (s : ℂ) : ℂ :=
  qBase ^ s * ((Complex.Gamma s)⁻¹ * (zqPair.Λ₀ s - 1 / (1 - s)) - (Complex.Gamma (s + 1))⁻¹)

theorem zqFn_aux (Q G X s : ℂ) (hQ : Q ≠ 0) (hG : G ≠ 0) :
    Q⁻¹ * G * (Q * (G⁻¹ * X - (s * G)⁻¹)) = X - s⁻¹ := by
  have e : Q⁻¹ * G * (Q * (G⁻¹ * X - (s * G)⁻¹)) = (Q⁻¹ * Q) * (G * G⁻¹) * (X - s⁻¹) := by
    ring
  rw [e, inv_mul_cancel₀ hQ, mul_inv_cancel₀ hG, one_mul, one_mul]

/-- `zqFn` with its gamma factor is `Λ`, off the zeros of `Γ⁻¹` and off `0`. -/
theorem mul_zqFn_eq {s : ℂ} (hs : s ≠ 0) (hG : Complex.Gamma s ≠ 0) :
    qBase ^ (-s) * Complex.Gamma s * zqFn s = zqPair.Λ s := by
  unfold zqFn
  rw [Complex.Gamma_add_one s hs, Complex.cpow_neg, zqFn_aux _ _ _ _ (qBase_cpow_ne s) hG, zqPair_Λ_eq]
  ring

theorem zqFn_agrees (s : ℂ) (hs : 1 < s.re) : zqFn s = ZQ s := by
  have hs0 : 0 < s.re := by linarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hs0
  have h := mul_zqFn_eq (Complex.ne_zero_of_re_pos hs0) hG
  rw [zqPair_Λ_eq_of_re hs] at h
  apply mul_left_cancel₀ (mul_ne_zero (qBase_cpow_ne (-s)) hG)
  rw [h]
  ring

theorem zqFn_holomorphic : DifferentiableOn ℂ zqFn {s : ℂ | s ≠ 1} := by
  intro s hs
  have hs' : s ≠ 1 := hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => qBase ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl qBase_ne)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) s := Complex.differentiable_one_div_Gamma s
  have h3 : DifferentiableAt ℂ zqPair.Λ₀ s := zqPair.differentiable_Λ₀ s
  have h4 : DifferentiableAt ℂ (fun s : ℂ => 1 / (1 - s)) s := by
    have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs'.symm
    have h40 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s := by fun_prop
    simp only [one_div]
    exact h40.inv hne
  have hd : Differentiable ℂ (fun s : ℂ => s + 1) := by fun_prop
  have h5 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp hd) s
  have h6 := h1.mul ((h2.mul (h3.sub h4)).sub h5)
  exact DifferentiableAt.differentiableWithinAt (f := zqFn) h6

theorem zqFn_functional_equation (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    qBase ^ (-s) * Complex.Gamma s * zqFn s = qBase ^ (-(1 - s)) * Complex.Gamma (1 - s) * zqFn (1 - s) := by
  have h0' : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [mul_zqFn_eq (Complex.ne_zero_of_re_pos h0) (Complex.Gamma_ne_zero_of_re_pos h0),
    mul_zqFn_eq (Complex.ne_zero_of_re_pos h0') (Complex.Gamma_ne_zero_of_re_pos h0'), zqPair_Λ_one_sub]

/-- The modified theta of the pair, as a real function. -/
def thetaFr (t : ℝ) : ℝ :=
  (Set.Ioi (1 : ℝ)).indicator (fun x => thetaU (cc * x) - 1) t +
    (Set.Ioo (0 : ℝ) 1).indicator (fun x => thetaU (cc * x) - x ^ (-(1 : ℝ))) t

theorem f_modif_real (t : ℝ) : zqPair.f_modif t = ((thetaFr t : ℝ) : ℂ) := by
  rw [WeakFEPair.f_modif, Pi.add_apply]
  unfold thetaFr
  rw [Complex.ofReal_add]
  congr 1
  · by_cases h : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_sub, Complex.ofReal_one]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]
  · by_cases h : t ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_sub]
      show thetaC t - ((1 : ℂ) * ((t ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ) = _
      rw [smul_eq_mul, one_mul, mul_one]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]

/-- **`Λ₀` is real on the real line.** -/
theorem zqPair_Λ₀_real (x : ℝ) : ∃ L : ℝ, zqPair.Λ₀ (x : ℂ) = (L : ℂ) := by
  refine ⟨∫ t in Set.Ioi (0 : ℝ), t ^ (x - 1) * thetaFr t, ?_⟩
  show mellin zqPair.f_modif (x : ℂ) = _
  rw [mellin]
  refine Eq.trans (b := ∫ t in Set.Ioi (0 : ℝ), ((t ^ (x - 1) * thetaFr t : ℝ) : ℂ))
    (setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)) integral_complex_ofReal
  have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
  show (t : ℂ) ^ ((x : ℂ) - 1) • zqPair.f_modif t = ((t ^ (x - 1) * thetaFr t : ℝ) : ℂ)
  rw [f_modif_real, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht0, Complex.ofReal_sub,
    Complex.ofReal_one]

theorem zqFn_real (x : ℝ) (_ : x ≠ 1) : (zqFn (x : ℂ)).im = 0 := by
  obtain ⟨L, hL⟩ := zqPair_Λ₀_real x
  have a1 : (lam : ℂ) ^ (x : ℂ) = ((lam ^ x : ℝ) : ℂ) := (Complex.ofReal_cpow lam_pos.le x).symm
  have a2 : Complex.Gamma (x : ℂ) = ((Real.Gamma x : ℝ) : ℂ) := Complex.Gamma_ofReal x
  have a3 : Complex.Gamma ((x : ℂ) + 1) = ((Real.Gamma (x + 1) : ℝ) : ℂ) := by
    have h := Complex.Gamma_ofReal (x + 1)
    rwa [Complex.ofReal_add, Complex.ofReal_one] at h
  have e : zqFn (x : ℂ) = ((lam ^ x * ((Real.Gamma x)⁻¹ * (L - 1 / (1 - x)) - (Real.Gamma (x + 1))⁻¹) : ℝ) : ℂ) := by
    unfold zqFn
    rw [qBase_eq, a1, a2, a3, hL]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_one]
  rw [e]
  exact Complex.ofReal_im _

/-- **(Z1) DISCHARGED FOR `zqFn`.** -/
theorem zq_continuation : ZQContinuation zqFn where
  summable := zq_summable
  agrees := zqFn_agrees
  holomorphic := zqFn_holomorphic
  functional_equation := zqFn_functional_equation
  real_on_real := zqFn_real

theorem exists_zq_continuation : ∃ zq : ℂ → ℂ, ZQContinuation zq := ⟨zqFn, zq_continuation⟩

end ZQ
end Schema
end SIDEExplicitFormula
