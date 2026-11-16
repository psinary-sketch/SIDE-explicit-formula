/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Elem.lean
THIS PROGRAMME'S WORK (act b740, ruling (R350)(3), relay data/b740_s5cd_statements.txt S5d) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S5d, THE ELEMENTARY VALUES AND `|Γ(s)|⁻¹`. General: enclosures of `exp`, `cos`, `sin` and `log` by their Taylor remainders, `cpow` at a
positive real base, and `‖Γ(s)⁻¹‖ ≤ ‖(GammaSeq s N)⁻¹‖ · e^(‖s‖²/(2N))` for `Re s ≥ 0` by a certified product (rows (d1)-(d5)). At box A's
centre `cA`: `‖Γ(cA)⁻¹‖ ≤ 16012218800`, `‖qBase^cA‖ ≤ 1.3103`, and `‖zqFn cA‖ ≤ K δ` whenever `δ` bounds
`‖lamM cA + lamM (1 − cA) − 1/(cA (1 − cA))‖` (rows (d6)-(d8)). `δ` is not computed here: no value of `zqFn` is certified by this file
alone and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.IncGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open Set Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- **(d1)** `exp` at `|x| ≤ 1` between its Taylor sum less and plus its remainder. -/
theorem exp_mem_Icc {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ∈ Set.Icc (∑ k ∈ Finset.range n, x ^ k / k.factorial - |x| ^ n * (n.succ / (n.factorial * n)))
      (∑ k ∈ Finset.range n, x ^ k / k.factorial + |x| ^ n * (n.succ / (n.factorial * n))) := by
  have h := Real.exp_bound hx hn
  rw [abs_le] at h
  rw [Set.mem_Icc]
  constructor <;> linarith [h.1, h.2]

/-- **(d2)** `cos` at `|x| ≤ 1` against the real part of the Taylor sum of `exp (I x)`, to any order. -/
theorem cos_sub_sum_le {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.cos x - (∑ k ∈ Finset.range n, (Complex.I * x) ^ k / k.factorial).re| ≤ |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hI : ‖Complex.I * (x : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := Complex.exp_bound hI hn
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
  have hre : Real.cos x = (Complex.exp (Complex.I * x)).re := by
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  rw [hre, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (h.trans_eq (by ring))

/-- **(d2)** `sin` at `|x| ≤ 1` against the imaginary part of the Taylor sum of `exp (I x)`, to any order. -/
theorem sin_sub_sum_le {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.sin x - (∑ k ∈ Finset.range n, (Complex.I * x) ^ k / k.factorial).im| ≤ |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hI : ‖Complex.I * (x : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := Complex.exp_bound hI hn
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
  have him : Real.sin x = (Complex.exp (Complex.I * x)).im := by
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  rw [him, ← Complex.sub_im]
  exact (Complex.abs_im_le_norm _).trans (h.trans_eq (by ring))

/-- **(d3)** `log (1 − x)` at `|x| < 1` against its series, the remainder `|x|^(n+1)/(1 − |x|)`. -/
theorem log_mem_Icc {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |Real.log (1 - x) + ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  rw [add_comm (Real.log (1 - x))]
  exact Real.abs_log_sub_add_sum_range_le hx n

/-- **(d4)** `cpow` at a positive real base, in modulus and argument. -/
theorem ofReal_cpow_eq {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (r : ℂ) ^ w = ((r ^ w.re : ℝ) : ℂ) * (Real.cos (w.im * Real.log r) + Real.sin (w.im * Real.log r) * Complex.I) := by
  have hw : (Real.log r : ℂ) * w = ((Real.log r * w.re : ℝ) : ℂ) + ((w.im * Real.log r : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im w]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.ofReal_log hr.le, Real.rpow_def_of_pos hr, hw,
    Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `‖(GammaSeq s n)⁻¹‖` in closed form, `n ≥ 1`. -/
def invSeqN (s : ℂ) (n : ℕ) : ℝ := (∏ j ∈ Finset.range (n + 1), ‖s + (j : ℂ)‖) / ((n : ℝ) ^ s.re * n.factorial)

theorem invSeqN_nonneg (s : ℂ) (n : ℕ) : 0 ≤ invSeqN s n := by
  unfold invSeqN
  have h1 : 0 ≤ ∏ j ∈ Finset.range (n + 1), ‖s + (j : ℂ)‖ := Finset.prod_nonneg (fun j _ => norm_nonneg _)
  have h2 : 0 ≤ (n : ℝ) ^ s.re := Real.rpow_nonneg (Nat.cast_nonneg n) _
  positivity

theorem norm_inv_GammaSeq {s : ℂ} {n : ℕ} (hn : 0 < n) : ‖(Complex.GammaSeq s n)⁻¹‖ = invSeqN s n := by
  rw [Complex.GammaSeq, inv_div, norm_div, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast]
  rfl

theorem norm_add_ofReal_sq (s : ℂ) (k : ℝ) : ‖s + (k : ℂ)‖ ^ 2 = ‖s‖ ^ 2 + 2 * s.re * k + k ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  ring

/-- One step of the product: `‖1 + s/(x+1)‖ (x/(x+1))^(Re s) ≤ e^(‖s‖²/(2x(x+1)))` for `Re s ≥ 0`, `x > 0`. -/
theorem step_le {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ} (hx : 0 < x) :
    ‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) * (x / (x + 1)) ^ s.re ≤ Real.exp (‖s‖ ^ 2 / (2 * (x * (x + 1)))) := by
  have hk : 0 < x + 1 := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  have hk0 : x + 1 ≠ 0 := hk.ne'
  have hlog : Real.log (x / (x + 1)) ≤ -(1 / (x + 1)) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx hk)
    have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by
      field_simp
      ring
    linarith
  have hpow : (x / (x + 1)) ^ s.re ≤ Real.exp (-(s.re / (x + 1))) := by
    rw [Real.rpow_def_of_pos (div_pos hx hk)]
    apply Real.exp_le_exp.mpr
    calc Real.log (x / (x + 1)) * s.re = s.re * Real.log (x / (x + 1)) := mul_comm _ _
      _ ≤ s.re * (-(1 / (x + 1))) := mul_le_mul_of_nonneg_left hlog hs
      _ = -(s.re / (x + 1)) := by ring
  have hu : 0 ≤ ‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) := by positivity
  have hsq := norm_add_ofReal_sq s (x + 1)
  have hA : (‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) * Real.exp (-(s.re / (x + 1)))) ^ 2
      ≤ (Real.exp (‖s‖ ^ 2 / (2 * (x * (x + 1))))) ^ 2 := by
    have e1 : (‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) * Real.exp (-(s.re / (x + 1)))) ^ 2
        = (1 + (2 * s.re / (x + 1) + ‖s‖ ^ 2 / (x + 1) ^ 2)) * Real.exp (-(2 * s.re / (x + 1))) := by
      rw [mul_pow, div_pow, hsq, ← Real.exp_nat_mul]
      congr 1
      · field_simp
        ring
      · congr 1
        push_cast
        ring
    have e2 : (Real.exp (‖s‖ ^ 2 / (2 * (x * (x + 1))))) ^ 2 = Real.exp (‖s‖ ^ 2 / (x * (x + 1))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [e1, e2]
    have h1 := Real.add_one_le_exp (2 * s.re / (x + 1) + ‖s‖ ^ 2 / (x + 1) ^ 2)
    have h2 : Real.exp (2 * s.re / (x + 1) + ‖s‖ ^ 2 / (x + 1) ^ 2) * Real.exp (-(2 * s.re / (x + 1)))
        = Real.exp (‖s‖ ^ 2 / (x + 1) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : ‖s‖ ^ 2 / (x + 1) ^ 2 ≤ ‖s‖ ^ 2 / (x * (x + 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    calc (1 + (2 * s.re / (x + 1) + ‖s‖ ^ 2 / (x + 1) ^ 2)) * Real.exp (-(2 * s.re / (x + 1)))
        ≤ Real.exp (2 * s.re / (x + 1) + ‖s‖ ^ 2 / (x + 1) ^ 2) * Real.exp (-(2 * s.re / (x + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (‖s‖ ^ 2 / (x + 1) ^ 2) := h2
      _ ≤ Real.exp (‖s‖ ^ 2 / (x * (x + 1))) := Real.exp_le_exp.mpr h3
  calc ‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) * (x / (x + 1)) ^ s.re
      ≤ ‖s + ((x + 1 : ℝ) : ℂ)‖ / (x + 1) * Real.exp (-(s.re / (x + 1))) := mul_le_mul_of_nonneg_left hpow hu
    _ ≤ Real.exp (‖s‖ ^ 2 / (2 * (x * (x + 1)))) := (abs_le_of_sq_le_sq' hA (Real.exp_pos _).le).2

theorem invSeqN_succ_le {s : ℂ} (hs : 0 ≤ s.re) {n : ℕ} (hn : 0 < n) :
    invSeqN s (n + 1) ≤ invSeqN s n * Real.exp (‖s‖ ^ 2 / (2 * ((n : ℝ) * ((n : ℝ) + 1)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
  have hp1 : (0 : ℝ) < ((n : ℝ) + 1) ^ s.re := Real.rpow_pos_of_pos (by linarith) _
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have heq : invSeqN s (n + 1)
      = invSeqN s n * (‖s + (((n : ℝ) + 1 : ℝ) : ℂ)‖ / ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) ^ s.re) := by
    unfold invSeqN
    rw [Finset.prod_range_succ (fun j => ‖s + (j : ℂ)‖) (n + 1), Nat.factorial_succ,
      Real.div_rpow hn0.le (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1) s.re]
    push_cast
    field_simp [hp.ne', hp1.ne', hf.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left (step_le hs hn0) (invSeqN_nonneg s n)

theorem invSeqN_le {s : ℂ} (hs : 0 ≤ s.re) {N : ℕ} (hN : 0 < N) (m : ℕ) (hm : N ≤ m) :
    invSeqN s m ≤ invSeqN s N * Real.exp (‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / (m : ℝ))) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hNm ih =>
    have hm0 : 0 < m := lt_of_lt_of_le hN hNm
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    have h1 := invSeqN_succ_le hs hm0
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : (m : ℝ) ≠ 0 := hm0'.ne'
    have e : ‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / (m : ℝ)) + ‖s‖ ^ 2 / (2 * ((m : ℝ) * ((m : ℝ) + 1)))
        = ‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    calc invSeqN s (m + 1) ≤ invSeqN s m * Real.exp (‖s‖ ^ 2 / (2 * ((m : ℝ) * ((m : ℝ) + 1)))) := h1
      _ ≤ invSeqN s N * Real.exp (‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / (m : ℝ)))
            * Real.exp (‖s‖ ^ 2 / (2 * ((m : ℝ) * ((m : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = invSeqN s N * Real.exp (‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) := by
          rw [mul_assoc, ← Real.exp_add, e]

/-- **(d5)** `‖Γ(s)⁻¹‖ ≤ ‖(GammaSeq s N)⁻¹‖ · e^(‖s‖²/(2N))` for `Re s ≥ 0`, `N ≥ 1`: a certified product. -/
theorem norm_inv_Gamma_le {s : ℂ} (hs : 0 ≤ s.re) {N : ℕ} (hN : 0 < N) :
    ‖(Complex.Gamma s)⁻¹‖ ≤ ‖(Complex.GammaSeq s N)⁻¹‖ * Real.exp (‖s‖ ^ 2 / (2 * N)) := by
  by_cases h0 : s = 0
  · subst h0
    rw [Complex.Gamma_zero, inv_zero, norm_zero]
    positivity
  have hG : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre : s.re = -(m : ℝ) := by
      rw [hm]
      simp
    have hm0 : m = 0 := by
      have h' : (m : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm h' (Nat.cast_nonneg m)
    exact h0 (by rw [hm, hm0]; simp)
  have hlim : Tendsto (fun n => ‖(Complex.GammaSeq s n)⁻¹‖) atTop (𝓝 ‖(Complex.Gamma s)⁻¹‖) :=
    ((Complex.GammaSeq_tendsto_Gamma s).inv₀ hG).norm
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
  show ‖(Complex.GammaSeq s m)⁻¹‖ ≤ ‖(Complex.GammaSeq s N)⁻¹‖ * Real.exp (‖s‖ ^ 2 / (2 * N))
  rw [norm_inv_GammaSeq (lt_of_lt_of_le hN hm), norm_inv_GammaSeq hN]
  have hm' : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have e : ‖s‖ ^ 2 / (2 * (N : ℝ)) = ‖s‖ ^ 2 / 2 * (1 / (N : ℝ)) := by ring
  calc invSeqN s m ≤ invSeqN s N * Real.exp (‖s‖ ^ 2 / 2 * (1 / (N : ℝ) - 1 / (m : ℝ))) := invSeqN_le hs hN m hm
    _ ≤ invSeqN s N * Real.exp (‖s‖ ^ 2 / (2 * N)) := by
        apply mul_le_mul_of_nonneg_left _ (invSeqN_nonneg s N)
        apply Real.exp_le_exp.mpr
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Box A's centre: the midpoint of its corners (Box.lean :21-:24). -/
def cA : ℂ := ⟨95326 / 100000, 16290216 / 1000000⟩

theorem cA_re : cA.re = 95326 / 100000 := rfl

theorem cA_im : cA.im = 16290216 / 1000000 := rfl

theorem prod_sq_centre :
    (∏ j ∈ Finset.range (64 + 1), ‖cA + (j : ℂ)‖) ^ 2
      = ∏ j ∈ Finset.range (64 + 1), (((95326 / 100000 : ℝ) + j) ^ 2 + (16290216 / 1000000) ^ 2) := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cA_re, cA_im, add_zero]
  ring

theorem centre_rpow_ge : (526937 / 10000 : ℝ) ≤ (64 : ℝ) ^ cA.re := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 64), cA_re]
  have hlog : (6931471803 / 10000000000 : ℝ) * 6 ≤ Real.log 64 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  have hy : (6931471803 / 10000000000 : ℝ) * 6 * (95326 / 100000) ≤ Real.log 64 * (95326 / 100000) :=
    mul_le_mul_of_nonneg_right hlog (by norm_num)
  calc (526937 / 10000 : ℝ)
      ≤ ∑ i ∈ Finset.range 22, ((6931471803 / 10000000000 : ℝ) * 6 * (95326 / 100000)) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp ((6931471803 / 10000000000 : ℝ) * 6 * (95326 / 100000)) := Real.sum_le_exp_of_nonneg (by norm_num) 22
    _ ≤ Real.exp (Real.log 64 * (95326 / 100000)) := Real.exp_le_exp.mpr hy

theorem invSeqN_centre_le : invSeqN cA 64 ≤ 1994000000 := by
  have hL := centre_rpow_ge
  have hfac : Nat.factorial 64
      = 126886932185884164103433389335161480802865516174545192198801894375214704230400000000000000 := by decide
  have hsq : invSeqN cA 64 ^ 2 ≤ (1994000000 : ℝ) ^ 2 := by
    unfold invSeqN
    rw [div_pow, prod_sq_centre, mul_pow, hfac]
    simp only [Nat.cast_ofNat]
    rw [div_le_iff₀ (by positivity)]
    calc ∏ j ∈ Finset.range (64 + 1), (((95326 / 100000 : ℝ) + j) ^ 2 + (16290216 / 1000000) ^ 2)
        ≤ (1994000000 : ℝ) ^ 2 * ((526937 / 10000) ^ 2
            * (126886932185884164103433389335161480802865516174545192198801894375214704230400000000000000 : ℝ) ^ 2) := by
          norm_num [Finset.prod_range_succ]
      _ ≤ (1994000000 : ℝ) ^ 2 * (((64 : ℝ) ^ cA.re) ^ 2
            * (126886932185884164103433389335161480802865516174545192198801894375214704230400000000000000 : ℝ) ^ 2) := by
          gcongr
  exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2

theorem exp_le_of_near_two {x : ℝ} (hx : |x - 2| ≤ 1) :
    Real.exp x ≤ 2.7182818286 * 2.7182818286 * (1 + (x - 2) + (x - 2) ^ 2) := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hx
  rw [abs_le] at h1
  have hez : Real.exp (x - 2) ≤ 1 + (x - 2) + (x - 2) ^ 2 := by linarith [h1.2]
  have he1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have e : Real.exp x = Real.exp 1 * Real.exp 1 * Real.exp (x - 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  calc Real.exp 1 * Real.exp 1 * Real.exp (x - 2) ≤ 2.7182818286 * 2.7182818286 * Real.exp (x - 2) := by gcongr
    _ ≤ 2.7182818286 * 2.7182818286 * (1 + (x - 2) + (x - 2) ^ 2) := by gcongr

theorem centre_exp_le : Real.exp (‖cA‖ ^ 2 / (2 * 64)) ≤ 40151 / 5000 := by
  have hn : ‖cA‖ ^ 2 = (95326 / 100000) ^ 2 + (16290216 / 1000000) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, cA_re, cA_im]
    ring
  rw [hn]
  refine (exp_le_of_near_two ?_).trans ?_
  · rw [abs_le]
    constructor <;> norm_num
  · norm_num

/-- **(d6)** At box A's centre, `‖Γ(cA)⁻¹‖ ≤ 16012218800`, from (d5) at `N = 64`. -/
theorem norm_inv_Gamma_centre_le : ‖(Complex.Gamma cA)⁻¹‖ ≤ 16012218800 := by
  have h := norm_inv_Gamma_le (s := cA) (by rw [cA_re]; norm_num) (N := 64) (by norm_num)
  rw [norm_inv_GammaSeq (s := cA) (n := 64) (by norm_num)] at h
  have h1 := invSeqN_centre_le
  have h2 : Real.exp (‖cA‖ ^ 2 / (2 * ((64 : ℕ) : ℝ))) ≤ 40151 / 5000 := by
    simpa only [Nat.cast_ofNat] using centre_exp_le
  calc ‖(Complex.Gamma cA)⁻¹‖ ≤ invSeqN cA 64 * Real.exp (‖cA‖ ^ 2 / (2 * ((64 : ℕ) : ℝ))) := h
    _ ≤ 1994000000 * (40151 / 5000) := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
    _ = 16012218800 := by norm_num

theorem lam_le : lam ≤ 13103 / 10000 := by
  have h23 : (47958 / 10000 : ℝ) < Real.sqrt 23 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  unfold lam
  rw [div_le_iff₀ sqrt23_pos]
  linarith [Real.pi_lt_d6]

/-- **(d7)** At box A's centre, `‖qBase^cA‖ ≤ 1.3103`. -/
theorem norm_qBase_cpow_centre_le : ‖qBase ^ cA‖ ≤ 13103 / 10000 := by
  rw [qBase_eq, Complex.norm_cpow_eq_rpow_re_of_pos lam_pos, cA_re]
  have h1 : (1 : ℝ) ≤ lam := by linarith [lam_gt]
  calc lam ^ (95326 / 100000 : ℝ) ≤ lam ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = lam := Real.rpow_one lam
    _ ≤ 13103 / 10000 := lam_le

theorem cA_ne_zero : cA ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [cA_re, Complex.zero_re] at h'
  norm_num at h'

theorem one_sub_cA_ne_zero : (1 : ℂ) - cA ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [Complex.sub_re, Complex.one_re, cA_re, Complex.zero_re] at h'
  norm_num at h'

/-- `zqFn` at the centre: `qBase^cA · Γ(cA)⁻¹ · (Λ₀ cA − 1/(cA (1 − cA)))`. -/
theorem zqFn_eq_centre :
    zqFn cA = qBase ^ cA * (Complex.Gamma cA)⁻¹ * (lamM cA + lamM (1 - cA) - 1 / (cA * (1 - cA))) := by
  have key : 1 / (1 - cA) + cA⁻¹ = 1 / (cA * (1 - cA)) := by
    field_simp [cA_ne_zero, one_sub_cA_ne_zero]
    try ring
  unfold zqFn
  rw [Complex.Gamma_add_one cA cA_ne_zero, zq_lambda0_split, mul_inv]
  linear_combination (-(qBase ^ cA * (Complex.Gamma cA)⁻¹)) * key

/-- **(d8)** At box A's centre, `‖zqFn cA‖ ≤ K δ`, `K = 1.3103 · 16012218800`, whenever `δ` bounds the one enclosure (c7) wants. -/
theorem zqFn_centre_le {δ : ℝ} (hδ : ‖lamM cA + lamM (1 - cA) - 1 / (cA * (1 - cA))‖ ≤ δ) :
    ‖zqFn cA‖ ≤ 13103 / 10000 * 16012218800 * δ := by
  rw [zqFn_eq_centre, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul norm_qBase_cpow_centre_le norm_inv_Gamma_centre_le (norm_nonneg _) (by norm_num)) hδ
    (norm_nonneg _) (by norm_num)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
