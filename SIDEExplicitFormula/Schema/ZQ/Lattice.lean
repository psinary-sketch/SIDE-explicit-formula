/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Lattice.lean
THIS PROGRAMME'S WORK (act b730, ruling (R340)(4), group A of relay data/b730_continuation_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LATTICE OF `Q0 = x² + xy + 6y²`. The form on pairs, its two lower bounds, the Gaussian sum over the lattice, the fibres of the form against
the box count `rQ`, and from them the first clause of `ZQContinuation`: the lattice sum converges on `Re s > 1`. Nothing here proves RH or GRH
or locates any zero.
-/
import SIDEExplicitFormula.Schema.EpsteinZQ
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- The form on pairs, as a real number. -/
def qR (p : ℤ × ℤ) : ℝ := ((Q0form p.1 p.2 : ℤ) : ℝ)

/-- The form completed in `m`. -/
theorem qR_eq (m n : ℤ) : qR (m, n) = ((m : ℝ) + (n : ℝ) / 2) ^ 2 + (23 / 4) * (n : ℝ) ^ 2 := by
  simp only [qR, Q0form]
  push_cast
  ring

theorem qR_nonneg (p : ℤ × ℤ) : 0 ≤ qR p := by
  unfold qR
  exact_mod_cast Q0form_nonneg p.1 p.2

/-- `Q0 ≥ (m² + n²)/2`. -/
theorem half_le_qR (p : ℤ × ℤ) : ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 2 ≤ qR p := by
  simp only [qR, Q0form]
  push_cast
  nlinarith [sq_nonneg ((p.1 : ℝ) + p.2), sq_nonneg (p.2 : ℝ)]

/-- The form is at least 1 off the origin. -/
theorem one_le_Q0form {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ Q0form p.1 p.2 := by
  obtain ⟨m, n⟩ := p
  show 1 ≤ Q0form m n
  by_contra h
  have hQ : Q0form m n ≤ 0 := by omega
  have h4 := four_mul_Q0form m n
  have hn : n = 0 := by
    by_contra hn
    have hpos : 0 < n ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * m + n)]
  subst hn
  have hm : m = 0 := by
    by_contra hm
    have hpos : 0 < m ^ 2 := by positivity
    nlinarith
  subst hm
  exact hp rfl

theorem one_le_qR {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ qR p := by
  unfold qR
  exact_mod_cast one_le_Q0form hp

theorem qR_zero : qR 0 = 0 := by
  simp [qR, Q0form]

/-- The one-dimensional Gaussian sum, from Mathlib's even kernel at `a = 0`. -/
theorem gauss_summable {c : ℝ} (hc : 0 < c) : Summable (fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 (t := c / Real.pi) (div_pos hc hπ)).summable
  refine h.congr (fun n => ?_)
  congr 1
  have hc' : Real.pi * (c / Real.pi) = c := by
    field_simp
  linear_combination ((n : ℝ) ^ 2) * hc'

/-- **The Gaussian sum over the lattice.** -/
theorem lattice_summable {c : ℝ} (hc : 0 < c) : Summable (fun p : ℤ × ℤ => Real.exp (-c * qR p)) := by
  have h1 := gauss_summable (c := c / 2) (by positivity)
  have h2 := h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun p => ?_) h2
  show Real.exp (-c * qR p) ≤ Real.exp (-(c / 2) * (p.1 : ℝ) ^ 2) * Real.exp (-(c / 2) * (p.2 : ℝ) ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := half_le_qR p
  nlinarith [mul_le_mul_of_nonneg_left this hc.le]

/-- The form as a natural number. -/
def qN (p : ℤ × ℤ) : ℕ := (Q0form p.1 p.2).toNat

theorem qN_cast (p : ℤ × ℤ) : ((qN p : ℕ) : ℝ) = qR p := by
  have h0 := Q0form_nonneg p.1 p.2
  have h : ((qN p : ℕ) : ℤ) = Q0form p.1 p.2 := by
    unfold qN
    omega
  unfold qR
  rw [← h]
  simp

/-- A point of the form's fibre over `k ≥ 1` lies in `rQ`'s box. -/
theorem mem_box {k : ℕ} (hk : k ≠ 0) {m n : ℤ} (h : Q0form m n = (k : ℤ)) :
    (-(2 * (k : ℤ)) ≤ m ∧ m ≤ 2 * (k : ℤ)) ∧ (-(k : ℤ) ≤ n ∧ n ≤ (k : ℤ)) := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hq : m ^ 2 + m * n + 6 * n ^ 2 = (k : ℤ) := by
    have := h
    unfold Q0form at this
    exact this
  have hk2 : (k : ℤ) ≤ (k : ℤ) ^ 2 := by nlinarith
  have hn1 : n ^ 2 ≤ (k : ℤ) := by nlinarith [sq_nonneg (2 * m + n), sq_nonneg n]
  have hm1 : m ^ 2 ≤ 2 * (k : ℤ) := by nlinarith [sq_nonneg (m + n), sq_nonneg n]
  have hn : n ^ 2 ≤ (k : ℤ) ^ 2 := by linarith
  have hm : m ^ 2 ≤ (2 * (k : ℤ)) ^ 2 := by nlinarith
  exact ⟨abs_le_of_sq_le_sq' hm (by omega), abs_le_of_sq_le_sq' hn (by omega)⟩

/-- `rQ`'s box, filtered. -/
def boxF (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
    (fun p : ℤ × ℤ => Q0form p.1 p.2 = (k : ℤ))

theorem rQ_eq_card {k : ℕ} (hk : k ≠ 0) : rQ k = (boxF k).card := by
  unfold rQ boxF
  rw [if_neg hk]

/-- The fibre over `k ≥ 1` is the box's filter. -/
theorem preimage_boxF {k : ℕ} (hk : k ≠ 0) : (qN ⁻¹' {k} : Set (ℤ × ℤ)) = ↑(boxF k) := by
  ext p
  have h0 := Q0form_nonneg p.1 p.2
  have hiff : qN p = k ↔ Q0form p.1 p.2 = (k : ℤ) := by
    unfold qN
    omega
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hiff, boxF, Finset.mem_coe, Finset.mem_filter, Finset.coe_filter,
    Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨mem_box hk h, h⟩
  · intro h
    exact h.2

/-- The fibre over `0` is the origin. -/
theorem preimage_zero : (qN ⁻¹' {0} : Set (ℤ × ℤ)) = ↑({0} : Finset (ℤ × ℤ)) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_singleton]
  constructor
  · intro h
    by_contra hp
    have h1 := one_le_Q0form hp
    unfold qN at h
    omega
  · rintro rfl
    simp [qN, Q0form]

/-- **The sum over the lattice grouped by the form's value**: the coefficient of `φ k` is `rQ k`, the origin apart. -/
theorem hasSum_fiber (φ : ℕ → ℝ) (hφ : Summable fun p : ℤ × ℤ => φ (qN p)) :
    HasSum (fun k : ℕ => if k = 0 then φ 0 else (rQ k : ℝ) * φ k) (∑' p : ℤ × ℤ, φ (qN p)) := by
  have h := hφ.hasSum.tsum_fiberwise qN
  have e : (fun k : ℕ => if k = 0 then φ 0 else (rQ k : ℝ) * φ k)
      = fun c : ℕ => ∑' b : (qN ⁻¹' {c} : Set (ℤ × ℤ)), φ (qN b) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, preimage_zero, Finset.tsum_subtype' ({0} : Finset (ℤ × ℤ)) (fun p => φ (qN p)),
        Finset.sum_singleton]
      simp [qN, Q0form]
    · rw [if_neg hk, preimage_boxF hk, Finset.tsum_subtype' (boxF k) (fun p => φ (qN p))]
      have hc : ∀ p ∈ boxF k, φ (qN p) = φ k := by
        intro p hp
        have hp' : p ∈ (↑(boxF k) : Set (ℤ × ℤ)) := hp
        rw [← preimage_boxF hk] at hp'
        have : qN p = k := hp'
        rw [this]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, rQ_eq_card hk]
  rw [e]
  exact h

/-- The sum of `Q0^{−σ}` over the lattice, by comparison with the sup norm on `ℤ²`. -/
theorem lattice_rpow_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ℤ × ℤ => ((qN p : ℕ) : ℝ) ^ (-σ)) := by
  have hσ0 : 0 < σ := by linarith
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 2 * σ) (by linarith)
  have h' := ((finTwoArrowEquiv ℤ).symm.summable_iff).mpr h
  have hG := h'.mul_left ((2 : ℝ) ^ σ)
  refine Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun p => ?_) hG
  simp only [Function.comp_apply]
  by_cases hp : p = 0
  · subst hp
    have h0 : ((qN 0 : ℕ) : ℝ) = 0 := by simp [qN, Q0form]
    rw [h0, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne')]
    positivity
  · set x : Fin 2 → ℤ := (finTwoArrowEquiv ℤ).symm p with hx
    have hQ := one_le_qR hp
    have hbound := half_le_qR p
    have hx0 : x 0 = p.1 := by simp [hx, finTwoArrowEquiv]
    have hx1 : x 1 = p.2 := by simp [hx, finTwoArrowEquiv]
    have key : ∀ i : Fin 2, ((x i : ℤ) : ℝ) ^ 2 ≤ 2 * qR p := by
      rw [Fin.forall_fin_two, hx0, hx1]
      constructor
      · nlinarith [sq_nonneg (p.2 : ℝ)]
      · nlinarith [sq_nonneg (p.1 : ℝ)]
    have hr0 : ‖x‖ ≤ Real.sqrt (2 * qR p) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
      rw [Int.norm_eq_abs]
      exact Real.abs_le_sqrt (key i)
    have hxne : x ≠ 0 := by
      intro h0
      apply hp
      apply Prod.ext
      · have h2 := congrFun h0 0
        rw [hx0] at h2
        simpa using h2
      · have h2 := congrFun h0 1
        rw [hx1] at h2
        simpa using h2
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hr2 : ‖x‖ ^ 2 / 2 ≤ qR p := by
      have h1 : ‖x‖ ^ 2 ≤ 2 * qR p := by
        have := pow_le_pow_left₀ hrpos.le hr0 2
        rwa [Real.sq_sqrt (by linarith)] at this
      linarith
    rw [qN_cast]
    have hmono := Real.rpow_le_rpow_of_nonpos (x := ‖x‖ ^ 2 / 2) (y := qR p) (z := -σ)
      (by have := pow_pos hrpos 2; linarith) hr2 (by linarith)
    refine hmono.trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_two ‖x‖, ← Real.rpow_mul hrpos.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ, div_inv_eq_mul, mul_comm]
    have : (2 : ℝ) * -σ = -(2 * σ) := by ring
    rw [this]

/-- The real Dirichlet sum of the coefficients. -/
theorem rQ_term_summable {σ : ℝ} (hσ : 1 < σ) : Summable (fun k : ℕ => (rQ k : ℝ) / (k : ℝ) ^ σ) := by
  have h := (hasSum_fiber (fun k : ℕ => (k : ℝ) ^ (-σ)) (lattice_rpow_summable hσ)).summable
  have hσ0 : σ ≠ 0 := by linarith
  refine h.congr (fun k => ?_)
  show (rQ k : ℝ) / (k : ℝ) ^ σ = if k = 0 then ((0 : ℕ) : ℝ) ^ (-σ) else (rQ k : ℝ) * (k : ℝ) ^ (-σ)
  by_cases hk : k = 0
  · subst hk
    simp [rQ_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0)]
  · rw [if_neg hk, Real.rpow_neg (Nat.cast_nonneg k), div_eq_mul_inv]

/-- **The clause `summable` of `ZQContinuation`.** -/
theorem zq_summable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun k => (rQ k : ℂ)) s := by
  show Summable (LSeries.term (fun k => (rQ k : ℂ)) s)
  refine Summable.of_norm ?_
  refine (rQ_term_summable hs).congr (fun k => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hk : k = 0
  · subst hk
    simp [rQ_zero]
  · rw [if_neg hk]
    simp

end ZQ
end Schema
end SIDEExplicitFormula
