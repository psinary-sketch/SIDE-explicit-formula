/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Omega.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (2) and (4) G5) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G5, THE HAND PART. `ω = exp(2πi/20)`, a primitive 20th root of unity (Mathlib `Complex.isPrimitiveRoot_exp`), with `cos(π/10)` and
`sin(π/10)` in closed form from `cos(π/5) = (1 + √5)/4` (Mathlib `Real.cos_pi_div_five`): `sin(π/10) = (√5 − 1)/4`,
`cos(π/10)^2 = (10 + 2√5)/16`; so `ω` lies in a rational disc from rational bounds on `√5` and `cos(π/10)`. The weights
`((ω^j)⁻¹)^k = ω^m` for `20 ∣ jk + m`. Discs under sums and rational scalings; the interpolant `dcVec` as a polynomial in `u`. The frontier
of box A as its four edges, a grid on an edge, and `‖z − cI‖ ≤ 0.5623` on the closed box. No value of `lamF` is computed here.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Amplify
import SIDEExplicitFormula.Schema.ZQ.OffZero.NodeBase
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex Metric Set Finset
open scoped Real

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- `ω = exp(2πi/20)`. -/
def omg : ℂ := Complex.exp (2 * π * I / ((20 : ℕ) : ℂ))

theorem omg_prim : IsPrimitiveRoot omg 20 := Complex.isPrimitiveRoot_exp 20 (by norm_num)

theorem norm_omg_pow (j : ℕ) : ‖omg ^ j‖ = 1 := by
  rw [norm_pow, omg_prim.norm'_eq_one (by norm_num), one_pow]

theorem omg_eq : omg = ((Real.cos (π / 10) : ℝ) : ℂ) + ((Real.sin (π / 10) : ℝ) : ℂ) * I := by
  unfold omg
  have h : 2 * (π : ℂ) * I / ((20 : ℕ) : ℂ) = ((π / 10 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem sin_pi_div_ten : Real.sin (π / 10) = (√5 - 1) / 4 := by
  rw [← Real.cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 8 : ℝ) * h5

theorem cos_pi_div_ten_sq : Real.cos (π / 10) ^ 2 = (10 + 2 * √5) / 16 := by
  have h := Real.cos_sq_add_sin_sq (π / 10)
  rw [sin_pi_div_ten] at h
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination h - (1 / 16 : ℝ) * h5

theorem cos_pi_div_ten_nonneg : 0 ≤ Real.cos (π / 10) :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- `ω` in a rational disc, from rational bounds on `√5` and on `cos(π/10)`. -/
theorem omg_inD {lo hi clo chi : ℚ} {c : ℚ × ℚ} {r : ℚ} (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi) (h5lo : lo ^ 2 ≤ 5)
    (h5hi : 5 ≤ hi ^ 2) (hclo0 : 0 ≤ clo) (hchi0 : 0 ≤ chi) (hc1 : clo ^ 2 ≤ (10 + 2 * lo) / 16)
    (hc2 : (10 + 2 * hi) / 16 ≤ chi ^ 2)
    (hr : max (chi - c.1) (c.1 - clo) + max ((hi - 1) / 4 - c.2) (c.2 - (lo - 1) / 4) ≤ r) : inD omg c r := by
  have hs0 := Real.sqrt_nonneg 5
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlo0' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo0
  have hhi0' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  have h5lo' : (lo : ℝ) ^ 2 ≤ 5 := by exact_mod_cast h5lo
  have h5hi' : (5 : ℝ) ≤ (hi : ℝ) ^ 2 := by exact_mod_cast h5hi
  have hclo0' : (0 : ℝ) ≤ clo := by exact_mod_cast hclo0
  have hchi0' : (0 : ℝ) ≤ chi := by exact_mod_cast hchi0
  have hc1' : (clo : ℝ) ^ 2 ≤ (10 + 2 * (lo : ℝ)) / 16 := by exact_mod_cast hc1
  have hc2' : (10 + 2 * (hi : ℝ)) / 16 ≤ (chi : ℝ) ^ 2 := by exact_mod_cast hc2
  have hr' : max ((chi : ℝ) - (c.1 : ℝ)) ((c.1 : ℝ) - clo) + max (((hi : ℝ) - 1) / 4 - (c.2 : ℝ)) ((c.2 : ℝ) - ((lo : ℝ) - 1) / 4)
      ≤ (r : ℝ) := by exact_mod_cast hr
  have hsl : (lo : ℝ) ≤ √5 := by nlinarith
  have hsh : √5 ≤ (hi : ℝ) := by nlinarith
  have hcos := cos_pi_div_ten_sq
  have hc0 := cos_pi_div_ten_nonneg
  have hcl : (clo : ℝ) ≤ Real.cos (π / 10) := by nlinarith
  have hch : Real.cos (π / 10) ≤ chi := by nlinarith
  have hsin := sin_pi_div_ten
  have e1 : |Real.cos (π / 10) - (c.1 : ℝ)| ≤ max ((chi : ℝ) - (c.1 : ℝ)) ((c.1 : ℝ) - clo) :=
    abs_sub_le_iff.2 ⟨(by linarith : Real.cos (π / 10) - (c.1 : ℝ) ≤ chi - c.1).trans (le_max_left _ _),
      (by linarith : (c.1 : ℝ) - Real.cos (π / 10) ≤ c.1 - clo).trans (le_max_right _ _)⟩
  have e2 : |Real.sin (π / 10) - (c.2 : ℝ)| ≤ max (((hi : ℝ) - 1) / 4 - (c.2 : ℝ)) ((c.2 : ℝ) - ((lo : ℝ) - 1) / 4) :=
    abs_sub_le_iff.2 ⟨(by rw [hsin]; linarith : Real.sin (π / 10) - (c.2 : ℝ) ≤ ((hi : ℝ) - 1) / 4 - c.2).trans (le_max_left _ _),
      (by rw [hsin]; linarith : (c.2 : ℝ) - Real.sin (π / 10) ≤ c.2 - ((lo : ℝ) - 1) / 4).trans (le_max_right _ _)⟩
  have hre : (omg - qc c).re = Real.cos (π / 10) - (c.1 : ℝ) := by rw [omg_eq]; simp [qc_re]
  have him : (omg - qc c).im = Real.sin (π / 10) - (c.2 : ℝ) := by rw [omg_eq]; simp [qc_im]
  unfold inD
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_trans ?_ hr')
  rw [hre, him]
  exact add_le_add e1 e2

/-- The weights: `((ω^j)⁻¹)^k = ω^m` when `20 ∣ j k + m`. -/
theorem omg_inv_pow {j k m : ℕ} (h : (j * k + m) % 20 = 0) : ((omg ^ j)⁻¹) ^ k = omg ^ m := by
  have h1 : omg ^ (j * k + m) = 1 := by
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
    rw [hq, pow_mul, omg_prim.pow_eq_one, one_pow]
  rw [pow_add] at h1
  rw [inv_pow, ← pow_mul]
  exact inv_eq_of_mul_eq_one_right h1

/-- The weight's exponent: `(20 − jk mod 20) mod 20`. -/
def wexp (j k : ℕ) : ℕ := (20 - (j * k) % 20) % 20

theorem wexp_spec (j k : ℕ) : (j * k + wexp j k) % 20 = 0 := by
  unfold wexp
  generalize j * k = x
  omega

theorem wexp_lt (j k : ℕ) : wexp j k < 20 := by
  unfold wexp
  omega

/-- `qc` as an additive map. -/
def qcHom : ℚ × ℚ →+ ℂ where
  toFun := qc
  map_zero' := by apply Complex.ext <;> simp [qc_re, qc_im]
  map_add' p q := by apply Complex.ext <;> simp [qc_re, qc_im]

theorem qc_sum {ι : Type*} (s : Finset ι) (c : ι → ℚ × ℚ) : qc (∑ i ∈ s, c i) = ∑ i ∈ s, qc (c i) :=
  map_sum qcHom c s

/-- Discs under a finite sum. -/
theorem inD_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ} {c : ι → ℚ × ℚ} {r : ι → ℚ} (h : ∀ i ∈ s, inD (f i) (c i) (r i)) :
    inD (∑ i ∈ s, f i) (∑ i ∈ s, c i) (∑ i ∈ s, r i) := by
  unfold inD at *
  rw [qc_sum, ← Finset.sum_sub_distrib, Rat.cast_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum h)

/-- Discs under a nonnegative rational scaling. -/
theorem inD_qscale {z : ℂ} {c : ℚ × ℚ} {r : ℚ} (s : ℚ) (hs : 0 ≤ s) (h : inD z c r) :
    inD (((s : ℝ) : ℂ) * z) (qscale s c) (s * r) := by
  unfold inD at *
  rw [qc_scale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by exact_mod_cast hs)]
  push_cast
  exact mul_le_mul_of_nonneg_left h (by exact_mod_cast hs)

/-- The interpolant as a polynomial: the coefficient of `u^k` is `(ρ^k)⁻¹ (1/M) Σ_j ((ω^j)⁻¹)^k v_j`. -/
theorem dcVec_eq_sum (v : ℕ → ℂ) (ω : ℂ) (ρ : ℝ) (M : ℕ) (u : ℂ) :
    dcVec v ω ρ M u = ∑ k ∈ range M, (((ρ : ℂ) ^ k)⁻¹ * ((M : ℂ)⁻¹ * ∑ j ∈ range M, ((ω ^ j)⁻¹) ^ k * v j)) * u ^ k := by
  unfold dcVec
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_eq_mul, div_pow]
  ring

/-- A polynomial of degree below 20 with rational coefficients, by its coefficient list, at a rational point. -/
def polyQ (cs : List (ℚ × ℚ)) (u : ℚ × ℚ) : ℚ × ℚ := ∑ k ∈ range 20, qmul (cs.getD k 0) (qpow u k)

/-- The same polynomial at a complex point. -/
def polyC (cs : List (ℚ × ℚ)) (u : ℂ) : ℂ := ∑ k ∈ range 20, qc (cs.getD k 0) * u ^ k

theorem qc_polyQ (cs : List (ℚ × ℚ)) (u : ℚ × ℚ) : qc (polyQ cs u) = polyC cs (qc u) := by
  unfold polyQ polyC
  rw [qc_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qc_mul, qc_pow]

def normSqQ (p : ℚ × ℚ) : ℚ := p.1 ^ 2 + p.2 ^ 2

theorem le_norm_qc {m : ℚ} (hm : 0 ≤ m) {p : ℚ × ℚ} (h : m ^ 2 ≤ normSqQ p) : (m : ℝ) ≤ ‖qc p‖ := by
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have h' : ((m : ℝ)) ^ 2 ≤ ‖qc p‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, qc_re, qc_im]
    have h2 : ((m ^ 2 : ℚ) : ℝ) ≤ ((normSqQ p : ℚ) : ℝ) := by exact_mod_cast h
    push_cast [normSqQ] at h2
    nlinarith
  nlinarith [norm_nonneg (qc p)]

/-- Two polynomials with near coefficients are near on `‖u‖ ≤ r`. -/
theorem norm_poly_sub_poly_le {a b : ℕ → ℂ} {e : ℕ → ℝ} (M : ℕ) {u : ℂ} {r : ℝ} (hu : ‖u‖ ≤ r)
    (h : ∀ k ∈ range M, ‖a k - b k‖ ≤ e k) :
    ‖∑ k ∈ range M, a k * u ^ k - ∑ k ∈ range M, b k * u ^ k‖ ≤ ∑ k ∈ range M, e k * r ^ k := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [← sub_mul, norm_mul, norm_pow]
  exact mul_le_mul (h k hk) (pow_le_pow_left₀ (norm_nonneg _) hu k) (by positivity) ((norm_nonneg _).trans (h k hk))

theorem cI_eq : cI = qc ((1 : ℚ) / 2, (16290216 : ℚ) / 1000000) := by
  apply Complex.ext <;> simp [cI, qc_re, qc_im] <;> norm_num

/-- **The node value at the exact root.** From `lamF` in a disc at the rational node `n` and `ω^j` in a disc: `lamF` at
`cI + ρ ω^j` (`ρ = 49/100`) within `rv + 120·3·η/(3 − 7/10)^2` of the disc's centre, `η` the node's distance (G2 (iii), G3). -/
theorem node_value_le {n v w : ℚ × ℚ} {rv rw D : ℚ} {j : ℕ}
    (hF : inD (lamF (qc n)) v rv) (hW : inD (omg ^ j) w rw)
    (hn : qn (qsub n ((1 : ℚ) / 2, (16290216 : ℚ) / 1000000)) ≤ 7 / 10)
    (hD : rv + 120 * 3 * ((49 / 100) * rw + qn (qsub (qadd ((1 : ℚ) / 2, (16290216 : ℚ) / 1000000) (qscale (49 / 100) w)) n))
      / (3 - 7 / 10) ^ 2 ≤ D) :
    ‖lamF (cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j) - qc v‖ ≤ (D : ℝ) := by
  set d := qsub (qadd ((1 : ℚ) / 2, (16290216 : ℚ) / 1000000) (qscale (49 / 100) w)) n with hd
  have hζ : ‖cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j - cI‖ ≤ 7 / 10 := by
    rw [add_sub_cancel_left, norm_mul, norm_omg_pow, Complex.norm_real]
    norm_num
  have hqn : ‖qc n - cI‖ ≤ 7 / 10 := by
    rw [cI_eq, ← qc_sub]
    exact (norm_qc_le _).trans (by exact_mod_cast hn)
  have hnear : ‖cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j - qc n‖ ≤ 49 / 100 * (rw : ℝ) + (qn d : ℝ) := by
    have e : cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j - qc n = ((49 / 100 : ℝ) : ℂ) * (omg ^ j - qc w) + qc d := by
      rw [hd, qc_sub, qc_add, qc_scale, cI_eq]
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_qc_le d))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left hW (by norm_num)
  have hdiff := DiffContOnCl.norm_sub_le_of_sphere (s := 7 / 10) (by norm_num) (by norm_num) lamF_diffContOnCl_ball
    lamF_sphere_le hζ hqn
  have hD' : (rv : ℝ) + 120 * 3 * ((49 / 100) * (rw : ℝ) + (qn d : ℝ)) / (3 - 7 / 10) ^ 2 ≤ (D : ℝ) := by
    exact_mod_cast hD
  have hF' : ‖lamF (qc n) - qc v‖ ≤ (rv : ℝ) := hF
  have h3 : 120 * 3 * ‖cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j - qc n‖ / (3 - 7 / 10) ^ 2 ≤
      120 * 3 * ((49 / 100) * (rw : ℝ) + (qn d : ℝ)) / (3 - 7 / 10) ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by norm_num)) (by norm_num)
  have h4 := norm_sub_le_norm_sub_add_norm_sub (lamF (cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j)) (lamF (qc n)) (qc v)
  linarith

/-- The frontier of box A is its four edges. -/
theorem frontier_boxA_cases {z : ℂ} (hz : z ∈ frontier boxA) :
    (z.re ∈ Icc x0 x1 ∧ (z.im = y0 ∨ z.im = y1)) ∨ ((z.re = x0 ∨ z.re = x1) ∧ z.im ∈ Icc y0 y1) := by
  rw [boxA, Complex.frontier_reProdIm, closure_Ioo x0_lt_x1.ne, closure_Ioo y0_lt_y1.ne, frontier_Ioo x0_lt_x1,
    frontier_Ioo y0_lt_y1] at hz
  rcases hz with h | h
  · rw [Complex.mem_reProdIm] at h
    exact Or.inl ⟨h.1, h.2⟩
  · rw [Complex.mem_reProdIm] at h
    exact Or.inr ⟨h.1, h.2⟩

/-- A grid on an edge: every `x ∈ [a, a + n h]` is within `h/2` of some `a + h/2 + i h`, `i < n`. -/
theorem exists_near_grid {a h x : ℝ} (hh : 0 < h) {n : ℕ} (hn : 0 < n) (hx1 : a ≤ x) (hx2 : x ≤ a + n * h) :
    ∃ i < n, |x - (a + h / 2 + i * h)| ≤ h / 2 := by
  set t := (x - a) / h with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hh.le
  have e : x = a + t * h := by rw [ht, div_mul_cancel₀ _ hh.ne']; ring
  have htn : t ≤ n := by
    rw [ht, div_le_iff₀ hh]
    linarith
  by_cases hf : ⌊t⌋₊ < n
  · refine ⟨⌊t⌋₊, hf, ?_⟩
    have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le ht0) hh.le
    have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t) hh
    rw [abs_le]
    constructor <;> nlinarith
  · push_neg at hf
    refine ⟨n - 1, by omega, ?_⟩
    have hfl : (n : ℝ) ≤ t := le_trans (by exact_mod_cast hf) (Nat.floor_le ht0)
    have htn' : t = n := le_antisymm htn hfl
    have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hc, e, htn', abs_le]
    constructor <;> nlinarith

/-- On the closed box, `‖z − cI‖ ≤ 0.5623`. -/
theorem norm_sub_cI_le {z : ℂ} (hz : z ∈ closure boxA) : ‖z - cI‖ ≤ 5623 / 10000 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closure_boxA hz
  norm_num [x0, x1, y0, y1] at h1 h2 h3 h4
  have hre : (z - cI).re = z.re - 1 / 2 := by simp [cI]
  have him : (z - cI).im = z.im - 16290216 / 1000000 := by simp [cI]
  have hsq : ‖z - cI‖ ^ 2 ≤ (5623 / 10000) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 105326 / 100000 + z.re - 1),
      mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h4)]
  nlinarith [norm_nonneg (z - cI)]

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
