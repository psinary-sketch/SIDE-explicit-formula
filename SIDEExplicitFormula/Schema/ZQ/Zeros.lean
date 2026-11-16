/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Zeros.lean
THIS PROGRAMME'S WORK (act b731, ruling (R341)(4), relay data/b731_zeros_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ZEROS FIELD. The zeros of `Λ_Q` as a `WideConfig`: `zqFn` is real on the real line, so Schwarz reflection holds off `1`; the functional equation carries
`Re s ≥ 3/2`, where `zq_ne_zero_of_three_halves_le` keeps `zqFn` nonzero, to `Re s ≤ −1/2`; `(1 − s) zqFn` extends to an entire function not vanishing at `1`,
so the zeros in a compact set are finite; the order of `zqFn` is the order of `Λ` at each zero, and `Λ(1 − s) = Λ(s)` gives `mult_reflect`. This discharges the
premise (Z2) for `zqFn` and no other premise of the instance; nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.LogDeriv
import Zeta23.ZetaReflect

open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-! ### Schwarz reflection -/

theorem zq_differentiableAt {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ zqFn z :=
  (zqFn_holomorphic z hz).differentiableAt (isOpen_ne.mem_nhds hz)

theorem zq_analyticOnNhd : AnalyticOnNhd ℂ zqFn ({(1 : ℂ)}ᶜ) := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
  exact (zq_differentiableAt (by simpa using hz)).differentiableWithinAt

theorem compl_one_preconnected : IsPreconnected ({(1 : ℂ)}ᶜ) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected

theorem two_mem_compl : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have h1 := congrArg Complex.re h
  norm_num at h1

/-- `r_Q` is real, so the series is reflected termwise. -/
theorem zq_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : conj (zqFn (conj s)) = zqFn s := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [zqFn_agrees _ hs', zqFn_agrees _ hs]
  show conj (LSeries aQ (conj s)) = LSeries aQ s
  unfold LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    rw [LSeries.term_zero, LSeries.term_zero, map_zero]
  · have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Ne.symm Real.pi_ne_zero
    have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
      have h := Complex.cpow_conj (n : ℂ) s harg
      rwa [Complex.conj_natCast] at h
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    show conj (((rQ n : ℕ) : ℂ) / (n : ℂ) ^ (conj s)) = ((rQ n : ℕ) : ℂ) / (n : ℂ) ^ s
    rw [map_div₀, hpow, Complex.conj_conj, Complex.conj_natCast]

/-- **Schwarz reflection for `zqFn`** off the pole. -/
theorem zq_conj {s : ℂ} (hs : s ≠ 1) : zqFn (conj s) = conj (zqFn s) := by
  have hζt : AnalyticOnNhd ℂ (fun z => conj (zqFn (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have h3 := (zq_differentiableAt hz1).conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : (fun z => conj (zqFn (conj z))) =ᶠ[nhds (2 : ℂ)] zqFn := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zq_conj_of_one_lt_re hz
  have heq := hζt.eqOn_of_preconnected_of_eventuallyEq zq_analyticOnNhd compl_one_preconnected two_mem_compl hagree
  have h3 : conj (zqFn (conj s)) = zqFn s := heq (by simpa using hs)
  calc zqFn (conj s) = conj (conj (zqFn (conj s))) := (Complex.conj_conj _).symm
    _ = conj (zqFn s) := by rw [h3]

/-! ### The functional equation off the poles -/

/-- `Λ_Q(s) = Λ_Q(1 − s)` read through `zqFn`, off the poles of the gamma factors. -/
theorem zq_fe {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (hG : Complex.Gamma z ≠ 0) (hG' : Complex.Gamma (1 - z) ≠ 0) :
    qBase ^ (-z) * Complex.Gamma z * zqFn z = qBase ^ (-(1 - z)) * Complex.Gamma (1 - z) * zqFn (1 - z) := by
  rw [mul_zqFn_eq h0 hG, mul_zqFn_eq (sub_ne_zero.mpr h1.symm) hG', zqPair_Λ_one_sub]

/-! ### The entire function `(1 − s) zqFn s` -/

/-- `(1 − s) zqFn s`, extended over the pole. -/
def aE (s : ℂ) : ℂ :=
  qBase ^ s * ((Complex.Gamma s)⁻¹ * ((1 - s) * zqPair.Λ₀ s - 1) - (1 - s) * (Complex.Gamma (s + 1))⁻¹)

theorem qpow_differentiable : Differentiable ℂ (fun s : ℂ => qBase ^ s) := fun _ =>
  DifferentiableAt.const_cpow differentiableAt_id (Or.inl qBase_ne)

theorem aE_differentiable : Differentiable ℂ aE := by
  intro s
  have h1 : DifferentiableAt ℂ (fun s : ℂ => qBase ^ s) s := qpow_differentiable s
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) s := Complex.differentiable_one_div_Gamma s
  have h3 : DifferentiableAt ℂ zqPair.Λ₀ s := zqPair.differentiable_Λ₀ s
  have h4 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s := by fun_prop
  have hd : Differentiable ℂ (fun s : ℂ => s + 1) := by fun_prop
  have h5 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp hd) s
  have h6 := h1.mul ((h2.mul ((h4.mul h3).sub_const 1)).sub (h4.mul h5))
  exact h6

theorem aE_aux (Q G H L u : ℂ) (hu : u ≠ 0) :
    Q * (G * (u * L - 1) - u * H) = u * (Q * (G * (L - 1 / u) - H)) := by
  have e : u * (Q * (G * (L - 1 / u) - H)) = Q * (G * (u * L - u * (1 / u)) - u * H) := by ring
  rw [e, mul_one_div_cancel hu]

theorem aE_eq {s : ℂ} (hs : s ≠ 1) : aE s = (1 - s) * zqFn s := by
  unfold aE zqFn
  exact aE_aux _ _ _ _ _ (sub_ne_zero.mpr hs.symm)

theorem aE_one : aE 1 = -qBase := by
  have e : (1 : ℂ) - 1 = 0 := sub_self 1
  unfold aE
  rw [e, zero_mul, zero_mul, sub_zero, Complex.Gamma_one, inv_one, one_mul, zero_sub, Complex.cpow_one,
    mul_neg, mul_one]

/-- **The zeros of the entire function in a compact set are finite**: an accumulation point would make it vanish at `1`. -/
theorem aE_zero_finite {K : Set ℂ} (hK : IsCompact K) : (K ∩ {ρ : ℂ | aE ρ = 0}).Finite := by
  by_contra hinf
  obtain ⟨x, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_left
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, aE z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun z hz => hz.2)
  have han : AnalyticOnNhd ℂ aE Set.univ := fun z _ => aE_differentiable.analyticAt z
  have h0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x) hfreq
  have h1 : aE 1 = 0 := h0 (Set.mem_univ 1)
  rw [aE_one] at h1
  exact qBase_ne (neg_eq_zero.mp h1)

/-! ### The carrier -/

theorem mem_C {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) :
    ρ ≠ 0 ∧ ρ ≠ 1 ∧ (∀ n : ℕ, ρ ≠ -((n : ℂ) + 1)) ∧ zqFn ρ = 0 := h

theorem C_gamma_ne {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : Complex.Gamma ρ ≠ 0 := by
  obtain ⟨h1, _, h3, _⟩ := mem_C h
  refine Complex.Gamma_ne_zero (fun m => ?_)
  rcases m with _ | n
  · simpa using h1
  · simpa using h3 n

theorem C_re_lt {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : ρ.re < 3 / 2 := by
  by_contra hn
  exact zq_ne_zero_of_three_halves_le ρ (not_lt.mp hn) (mem_C h).2.2.2

theorem C_gamma_one_sub {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : Complex.Gamma (1 - ρ) ≠ 0 := by
  obtain ⟨_, h2, _, _⟩ := mem_C h
  refine Complex.Gamma_ne_zero (fun m hm => ?_)
  have hρ : ρ = 1 + (m : ℂ) := by linear_combination -hm
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact h2 (by simpa using hρ)
  · have hre : ρ.re = 1 + (m : ℝ) := by
      rw [hρ]
      simp
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hlt := C_re_lt h
    linarith

/-- **No zero left of `−1/2`**: the functional equation reflects it past `3/2`. -/
theorem C_re_gt {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : -1 / 2 < ρ.re := by
  by_contra hn
  obtain ⟨h1, h2, _, h4⟩ := mem_C h
  have hre : 3 / 2 ≤ (1 - ρ).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [not_lt.mp hn]
  have fe := zq_fe h1 h2 (C_gamma_ne h) (C_gamma_one_sub h)
  rw [h4, mul_zero] at fe
  exact (mul_ne_zero (mul_ne_zero (qBase_cpow_ne _) (C_gamma_one_sub h))
    (zq_ne_zero_of_three_halves_le _ hre)) fe.symm

theorem C_conj {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : conj ρ ∈ LambdaQZeros zqFn := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_C h
  show conj ρ ≠ 0 ∧ conj ρ ≠ 1 ∧ (∀ n : ℕ, conj ρ ≠ -((n : ℂ) + 1)) ∧ zqFn (conj ρ) = 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    have e2 := congrArg (starRingEnd ℂ) e
    rw [Complex.conj_conj, map_zero] at e2
    exact h1 e2
  · intro e
    have e2 := congrArg (starRingEnd ℂ) e
    rw [Complex.conj_conj, map_one] at e2
    exact h2 e2
  · intro n e
    have e2 := congrArg (starRingEnd ℂ) e
    simp only [Complex.conj_conj, map_neg, map_add, map_one, Complex.conj_natCast] at e2
    exact h3 n e2
  · rw [zq_conj h2, h4, map_zero]

theorem C_one_sub {σ : ℂ} (h : σ ∈ LambdaQZeros zqFn) : 1 - σ ∈ LambdaQZeros zqFn := by
  obtain ⟨h1, h2, _, h4⟩ := mem_C h
  show 1 - σ ≠ 0 ∧ 1 - σ ≠ 1 ∧ (∀ n : ℕ, 1 - σ ≠ -((n : ℂ) + 1)) ∧ zqFn (1 - σ) = 0
  refine ⟨sub_ne_zero.mpr h2.symm, ?_, ?_, ?_⟩
  · intro e
    exact h1 (by linear_combination -e)
  · intro n e
    have hσ : σ = (n : ℂ) + 2 := by linear_combination -e
    have hre : σ.re = (n : ℝ) + 2 := by
      rw [hσ]
      simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlt := C_re_lt h
    linarith
  · have fe := zq_fe h1 h2 (C_gamma_ne h) (C_gamma_one_sub h)
    rw [h4, mul_zero] at fe
    exact (mul_eq_zero.mp fe.symm).resolve_left (mul_ne_zero (qBase_cpow_ne _) (C_gamma_one_sub h))

/-! ### The order -/

theorem zq_order_ne_top {ρ : ℂ} (h1 : ρ ≠ 1) : analyticOrderAt zqFn ρ ≠ ⊤ := by
  intro ht
  have hρ : ρ ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simpa using h1
  have e := zq_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero compl_one_preconnected hρ
    (analyticOrderAt_eq_top.mp ht)
  have h2 : zqFn 2 = 0 := e two_mem_compl
  exact zq_ne_zero_of_three_halves_le 2 (by norm_num) h2

theorem zq_order_cast {ρ : ℂ} (h1 : ρ ≠ 1) : ((analyticOrderNatAt zqFn ρ : ℕ) : ENat) = analyticOrderAt zqFn ρ :=
  Nat.cast_analyticOrderNatAt (zq_order_ne_top h1)

theorem zq_analyticAt {ρ : ℂ} (h1 : ρ ≠ 1) : AnalyticAt ℂ zqFn ρ :=
  zq_analyticOnNhd ρ (by simpa using h1)

theorem C_one_le_mult {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) : 1 ≤ analyticOrderNatAt zqFn ρ := by
  obtain ⟨_, h2, _, h4⟩ := mem_C h
  refine Nat.one_le_iff_ne_zero.mpr (fun h0 => ?_)
  have e := zq_order_cast h2
  rw [h0, Nat.cast_zero] at e
  exact (zq_analyticAt h2).analyticOrderAt_eq_zero.mp e.symm h4

theorem zq_order_conj {ρ : ℂ} (hc : conj ρ ≠ 1) :
    analyticOrderAt zqFn (conj ρ) = analyticOrderAt zqFn ρ := by
  have ev : ∀ᶠ z in nhds (conj ρ), z ≠ 1 := isOpen_ne.mem_nhds hc
  have e : (fun z => conj (zqFn (conj z))) =ᶠ[nhds (conj ρ)] zqFn := by
    filter_upwards [ev] with z hz
    rw [zq_conj hz, Complex.conj_conj]
  rw [← analyticOrderAt_congr e]
  exact Zeta23.analyticOrderAt_conj_conj zqFn ρ

theorem Lam_analyticAt {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) : AnalyticAt ℂ zqPair.Λ z := by
  have e : zqPair.Λ = fun s => zqPair.Λ₀ s - 1 / s - 1 / (1 - s) := funext zqPair_Λ_eq
  rw [e]
  have h2 : AnalyticAt ℂ zqPair.Λ₀ z := zqPair.differentiable_Λ₀.analyticAt z
  have h3 : AnalyticAt ℂ (fun s : ℂ => 1 / s) z := analyticAt_const.div analyticAt_id h0
  have h4 : AnalyticAt ℂ (fun s : ℂ => 1 / (1 - s)) z :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr h1.symm)
  exact (h2.sub h3).sub h4

theorem zq_mul_aux (Q G X : ℂ) (hQ : Q ≠ 0) (hG : G ≠ 0) : X = Q * G⁻¹ * (Q⁻¹ * G * X) := by
  have e : Q * G⁻¹ * (Q⁻¹ * G * X) = (Q * Q⁻¹) * (G⁻¹ * G) * X := by ring
  rw [e, mul_inv_cancel₀ hQ, inv_mul_cancel₀ hG, one_mul, one_mul]

/-- The order of `zqFn` is the order of `Λ`, off the poles. -/
theorem zq_order_eq_Lam {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (hG : Complex.Gamma z ≠ 0) :
    analyticOrderAt zqFn z = analyticOrderAt zqPair.Λ z := by
  have hq : AnalyticAt ℂ (fun s : ℂ => qBase ^ s) z := qpow_differentiable.analyticAt z
  have hI : AnalyticAt ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) z := Complex.differentiable_one_div_Gamma.analyticAt z
  have hu : AnalyticAt ℂ (fun s : ℂ => qBase ^ s * (Complex.Gamma s)⁻¹) z := hq.mul hI
  have hu0 : analyticOrderAt (fun s : ℂ => qBase ^ s * (Complex.Gamma s)⁻¹) z = 0 :=
    hu.analyticOrderAt_eq_zero.mpr (mul_ne_zero (qBase_cpow_ne z) (inv_ne_zero hG))
  have ev0 : ∀ᶠ s in nhds z, s ≠ 0 := isOpen_ne.mem_nhds h0
  have evG : ∀ᶠ s in nhds z, (Complex.Gamma s)⁻¹ ≠ 0 := hI.continuousAt.eventually_ne (inv_ne_zero hG)
  have e : zqFn =ᶠ[nhds z] ((fun s : ℂ => qBase ^ s * (Complex.Gamma s)⁻¹) * zqPair.Λ) := by
    filter_upwards [ev0, evG] with s hs0 hsG
    have hGs : Complex.Gamma s ≠ 0 := fun e => hsG (by rw [e, inv_zero])
    have m := mul_zqFn_eq hs0 hGs
    show zqFn s = qBase ^ s * (Complex.Gamma s)⁻¹ * zqPair.Λ s
    rw [← m, Complex.cpow_neg]
    exact zq_mul_aux _ _ _ (qBase_cpow_ne s) hGs
  rw [analyticOrderAt_congr e, analyticOrderAt_mul hu (Lam_analyticAt h0 h1), hu0, zero_add]

theorem Lam_order_one_sub (w : ℂ) : analyticOrderAt zqPair.Λ (1 - w) = analyticOrderAt zqPair.Λ w := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    rw [deriv_const_sub]
    simp
  have e : (zqPair.Λ ∘ fun z : ℂ => 1 - z) = zqPair.Λ := funext zqPair_Λ_one_sub
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := zqPair.Λ) hg hg'
  rw [e] at h
  exact h.symm

theorem C_mult_reflect {ρ : ℂ} (h : ρ ∈ LambdaQZeros zqFn) :
    analyticOrderNatAt zqFn (Zeta23.reflect ρ) = analyticOrderNatAt zqFn ρ := by
  have hσ := C_conj h
  have hτ := C_one_sub hσ
  obtain ⟨σ0, σ1, _, _⟩ := mem_C hσ
  obtain ⟨τ0, τ1, _, _⟩ := mem_C hτ
  have e : analyticOrderAt zqFn (1 - conj ρ) = analyticOrderAt zqFn ρ := by
    rw [zq_order_eq_Lam τ0 τ1 (C_gamma_ne hτ), Lam_order_one_sub, ← zq_order_eq_Lam σ0 σ1 (C_gamma_ne hσ)]
    exact zq_order_conj σ1
  show (analyticOrderAt zqFn (1 - conj ρ)).toNat = (analyticOrderAt zqFn ρ).toNat
  rw [e]

/-- Finitely many zeros in an ordinate window. -/
theorem C_finite_window (T₁ T₂ : ℝ) :
    (LambdaQZeros zqFn ∩ {ρ : ℂ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  have hK : IsCompact (Complex.reProdIm (Set.Icc (-1 / 2) (3 / 2)) (Set.Icc T₁ T₂)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine (aE_zero_finite hK).subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  refine ⟨⟨⟨(C_re_gt hρ).le, (C_re_lt hρ).le⟩, ⟨hT₁.le, hT₂⟩⟩, ?_⟩
  obtain ⟨_, h2, _, h4⟩ := mem_C hρ
  show aE ρ = 0
  rw [aE_eq h2, h4, mul_zero]

/-- **THE CONFIGURATION**: the zeros of `Λ_Q` with their orders, a `WideConfig`. -/
def zqZeroConfig : WideConfig where
  carrier := LambdaQZeros zqFn
  mult := analyticOrderNatAt zqFn
  one_le_mult := fun _ h => C_one_le_mult h
  strip := fun _ h => ⟨C_re_gt h, C_re_lt h⟩
  reflect_mem := fun _ h => C_one_sub (C_conj h)
  mult_reflect := fun _ h => C_mult_reflect h
  finite_window := C_finite_window

/-- **THE zeros FIELD**: `ZQZeros zqFn zqZeroConfig`. -/
theorem zq_zeros : ZQZeros zqFn zqZeroConfig where
  carrier_eq := rfl
  mult_order := fun ρ h => by
    have h2 := (mem_C h).2.1
    obtain ⟨g, hg, hg0, hev⟩ := (zq_analyticAt h2).analyticOrderAt_eq_natCast.mp (zq_order_cast h2).symm
    exact ⟨g, hg, hg0, hev.mono (fun z hz => hz.trans (smul_eq_mul _ _))⟩

theorem exists_zq_zeros : ∃ Z : WideConfig, ZQZeros zqFn Z := ⟨zqZeroConfig, zq_zeros⟩

end ZQ
end Schema
end SIDEExplicitFormula
