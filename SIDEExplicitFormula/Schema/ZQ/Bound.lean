/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Bound.lean
THIS PROGRAMME'S WORK (act b731, ruling (R341)(3), group A of relay data/b731_logderiv_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

`Z_Q(3/2) < 4`, THE ONE HYPOTHESIS OF THE LOGARITHMIC DERIVATIVE'S SERIES AND OF THE ZERO-FREE HALF-PLANE. The lattice sum is taken row by row. On a
row `n ≠ 0`, with `a = 23 n² / 4`, `G x = x / (a √(x² + a))` has derivative `(x² + a)^{−3/2}`, and the mean value theorem bounds the term at `x` by
`1.38 (G (x + 1/2) − G (x − 1/2))`, which telescopes to `2.76 / a`. The row `n = 0` is `2 ζ(3)`. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Continuation
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- The root of a row. -/
def wR (a x : ℝ) : ℝ := Real.sqrt (x ^ 2 + a)

/-- The primitive of a row's term. -/
def gR (a x : ℝ) : ℝ := x / (a * wR a x)

theorem wR_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < wR a x :=
  Real.sqrt_pos.mpr (by positivity)

theorem wR_sq {a : ℝ} (ha : 0 < a) (x : ℝ) : wR a x ^ 2 = x ^ 2 + a :=
  Real.sq_sqrt (by positivity)

theorem hasDerivAt_wR {a : ℝ} (ha : 0 < a) (x : ℝ) : HasDerivAt (wR a) (x / wR a x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + a) (2 * x) x :=
    ((hasDerivAt_pow 2 x).add_const a).congr_deriv (by norm_num)
  have h2 : HasDerivAt (wR a) (2 * x / (2 * wR a x)) x :=
    h1.sqrt (show x ^ 2 + a ≠ 0 by positivity)
  rwa [mul_div_mul_left x (wR a x) two_ne_zero] at h2

theorem gR_aux (a w x : ℝ) (ha : a ≠ 0) (hw : w ≠ 0) (h : w ^ 2 = x ^ 2 + a) :
    (1 * (a * w) - x * (a * (x / w))) / (a * w) ^ 2 = 1 / w ^ 3 := by
  have hx : x * x = w ^ 2 - a := by
    rw [h]
    ring
  have e1 : 1 * (a * w) - x * (a * (x / w)) = a * (w ^ 2 - x * x) / w := by
    field_simp <;> ring
  have e2 : w ^ 2 - (w ^ 2 - a) = a := by ring
  rw [e1, hx, e2]
  field_simp <;> ring

theorem hasDerivAt_gR {a : ℝ} (ha : 0 < a) (x : ℝ) : HasDerivAt (gR a) (1 / wR a x ^ 3) x := by
  have hw := wR_pos ha x
  have hd : HasDerivAt (fun y => a * wR a y) (a * (x / wR a x)) x := (hasDerivAt_wR ha x).const_mul a
  have h : HasDerivAt (gR a) ((1 * (a * wR a x) - x * (a * (x / wR a x))) / (a * wR a x) ^ 2) x :=
    (hasDerivAt_id' x).fun_div hd (mul_pos ha hw).ne'
  rwa [gR_aux a (wR a x) x ha.ne' hw.ne' (wR_sq ha x)] at h

theorem gR_le {a : ℝ} (ha : 0 < a) (x : ℝ) : gR a x ≤ 1 / a := by
  have hw := wR_pos ha x
  have hx : |x| ≤ wR a x := Real.abs_le_sqrt (show x ^ 2 ≤ x ^ 2 + a by linarith)
  have hx' : x ≤ wR a x := (le_abs_self x).trans hx
  unfold gR
  rw [div_le_div_iff₀ (mul_pos ha hw) ha]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha.le]

theorem neg_gR_le {a : ℝ} (ha : 0 < a) (x : ℝ) : -gR a x ≤ 1 / a := by
  have hw := wR_pos ha x
  have hx : |x| ≤ wR a x := Real.abs_le_sqrt (show x ^ 2 ≤ x ^ 2 + a by linarith)
  have hx' : -x ≤ wR a x := (neg_le_abs x).trans hx
  have e : -gR a x = -x / (a * wR a x) := by
    unfold gR
    ring
  rw [e, div_le_div_iff₀ (mul_pos ha hw) ha]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha.le]

theorem cube_aux {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : u ^ 2 ≤ 1.239 * v ^ 2) :
    1 / v ^ 3 ≤ 1.38 * (1 / u ^ 3) := by
  have h1 : (u ^ 2) ^ 3 ≤ (1.239 * v ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  have hv6 : 0 ≤ v ^ 6 := by positivity
  have h2 : (u ^ 3) ^ 2 ≤ (1.38 * v ^ 3) ^ 2 := by
    calc (u ^ 3) ^ 2 = (u ^ 2) ^ 3 := by ring
      _ ≤ (1.239 * v ^ 2) ^ 3 := h1
      _ = (1.239 : ℝ) ^ 3 * v ^ 6 := by ring
      _ ≤ (1.38 : ℝ) ^ 2 * v ^ 6 := mul_le_mul_of_nonneg_right (by norm_num) hv6
      _ = (1.38 * v ^ 3) ^ 2 := by ring
  have h3 : u ^ 3 ≤ 1.38 * v ^ 3 := (sq_le_sq₀ (by positivity) (by positivity)).mp h2
  have hp : 0 < v ^ 3 := by positivity
  have hq : 0 < u ^ 3 := by positivity
  have h4 : (1 : ℝ) / v ^ 3 ≤ 1.38 / u ^ 3 := by
    rw [div_le_div_iff₀ hp hq]
    linarith
  calc (1 : ℝ) / v ^ 3 ≤ 1.38 / u ^ 3 := h4
    _ = 1.38 * (1 / u ^ 3) := by ring

/-- **The step on a row.** -/
theorem row_step {a : ℝ} (ha : 23 / 4 ≤ a) (x : ℝ) :
    1 / wR a x ^ 3 ≤ 1.38 * (gR a (x + 1 / 2) - gR a (x - 1 / 2)) := by
  have ha0 : 0 < a := by linarith
  have hdG := hasDerivAt_gR ha0
  obtain ⟨c, hc, e⟩ := exists_hasDerivAt_eq_slope (gR a) (fun y => 1 / wR a y ^ 3)
    (show x - 1 / 2 < x + 1 / 2 by linarith) (fun y _ => (hdG y).continuousAt.continuousWithinAt)
    (fun y _ => hdG y)
  have e' : 1 / wR a c ^ 3 = gR a (x + 1 / 2) - gR a (x - 1 / 2) := by
    have hd : x + 1 / 2 - (x - 1 / 2) = 1 := by ring
    rw [hd, div_one] at e
    exact e
  rw [← e']
  have hc2 : c ^ 2 ≤ (|x| + 1 / 2) ^ 2 :=
    sq_le_sq' (by linarith [hc.1, neg_abs_le x]) (by linarith [hc.2, le_abs_self x])
  have hsq : wR a c ^ 2 ≤ 1.239 * wR a x ^ 2 := by
    rw [wR_sq ha0 c, wR_sq ha0 x, ← sq_abs x]
    nlinarith [sq_nonneg (|x| - 500 / 239)]
  exact cube_aux (wR_pos ha0 c) (wR_pos ha0 x) hsq

/-- A row's term. -/
def rowT (a δ : ℝ) (m : ℤ) : ℝ := 1 / wR a ((m : ℝ) + δ) ^ 3

theorem rowT_nonneg {a : ℝ} (ha : 0 < a) (δ : ℝ) (m : ℤ) : 0 ≤ rowT a δ m := by
  have h := wR_pos ha ((m : ℝ) + δ)
  exact div_nonneg zero_le_one (pow_nonneg h.le 3)

theorem telescope_le {t f : ℕ → ℝ} {C : ℝ} (ht : ∀ i, 0 ≤ t i) (h : ∀ i, t i ≤ 1.38 * (f (i + 1) - f i))
    (hC : ∀ N, f N ≤ C) : ∑' i, t i ≤ 1.38 * (C - f 0) := by
  refine Real.tsum_le_of_sum_range_le ht (fun N => ?_)
  calc ∑ i ∈ Finset.range N, t i ≤ ∑ i ∈ Finset.range N, 1.38 * (f (i + 1) - f i) :=
        Finset.sum_le_sum (fun i _ => h i)
    _ = 1.38 * (f N - f 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ 1.38 * (C - f 0) := by linarith [hC N]

/-- **One row, summed.** -/
theorem row_le {a : ℝ} (ha : 23 / 4 ≤ a) (δ : ℝ) (ht : Summable (rowT a δ)) :
    ∑' m : ℤ, rowT a δ m ≤ 2.76 / a := by
  have ha0 : 0 < a := by linarith
  have hp : Summable (fun k : ℕ => rowT a δ (k : ℤ)) :=
    ht.comp_injective (i := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
    intro i j h
    have h' : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega
  have hn : Summable (fun k : ℕ => rowT a δ (-((k : ℤ) + 1))) := ht.comp_injective hinj
  rw [tsum_of_nat_of_neg_add_one (f := rowT a δ) hp hn]
  have h1 : ∑' k : ℕ, rowT a δ (k : ℤ) ≤ 1.38 * (1 / a - gR a (((0 : ℕ) : ℝ) + δ - 1 / 2)) := by
    refine telescope_le (f := fun i : ℕ => gR a ((i : ℝ) + δ - 1 / 2)) (fun k => rowT_nonneg ha0 δ _) (fun i => ?_)
      (fun N => gR_le ha0 _)
    have h := row_step ha ((i : ℝ) + δ)
    have e3 : ((i + 1 : ℕ) : ℝ) + δ - 1 / 2 = (i : ℝ) + δ + 1 / 2 := by
      push_cast <;> ring
    show rowT a δ (i : ℤ) ≤ 1.38 * (gR a (((i + 1 : ℕ) : ℝ) + δ - 1 / 2) - gR a ((i : ℝ) + δ - 1 / 2))
    rw [e3]
    unfold rowT
    rw [Int.cast_natCast]
    exact h
  have h2 : ∑' k : ℕ, rowT a δ (-((k : ℤ) + 1)) ≤ 1.38 * (1 / a - -gR a (-((0 : ℕ) : ℝ) + δ - 1 / 2)) := by
    refine telescope_le (f := fun i : ℕ => -gR a (-(i : ℝ) + δ - 1 / 2)) (fun k => rowT_nonneg ha0 δ _) (fun i => ?_)
      (fun N => neg_gR_le ha0 _)
    have h := row_step ha (-(i : ℝ) - 1 + δ)
    have e1 : -(i : ℝ) - 1 + δ + 1 / 2 = -(i : ℝ) + δ - 1 / 2 := by ring
    have e2 : -(i : ℝ) - 1 + δ - 1 / 2 = -((i + 1 : ℕ) : ℝ) + δ - 1 / 2 := by
      push_cast <;> ring
    have e4 : (((-((i : ℤ) + 1) : ℤ) : ℝ)) = -(i : ℝ) - 1 := by
      push_cast <;> ring
    show rowT a δ (-((i : ℤ) + 1)) ≤ 1.38 * (-gR a (-((i + 1 : ℕ) : ℝ) + δ - 1 / 2) - -gR a (-(i : ℝ) + δ - 1 / 2))
    unfold rowT
    rw [e4]
    rw [e1, e2] at h
    linarith
  have e0 : gR a (-((0 : ℕ) : ℝ) + δ - 1 / 2) = gR a (((0 : ℕ) : ℝ) + δ - 1 / 2) := by
    simp
  rw [e0] at h2
  have e5 : 1.38 * (1 / a - gR a (((0 : ℕ) : ℝ) + δ - 1 / 2)) + 1.38 * (1 / a - -gR a (((0 : ℕ) : ℝ) + δ - 1 / 2)) = 2.76 / a := by
    ring
  linarith

/-- The term of the sum over the lattice. -/
def zF (p : ℤ × ℤ) : ℝ := ((qN p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))

theorem zF_nonneg (p : ℤ × ℤ) : 0 ≤ zF p := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem zF_summable : Summable zF := lattice_rpow_summable (σ := 3 / 2) (by norm_num)

theorem rpow_aux {b : ℝ} (hb : 0 < b) : b ^ (-(3 / 2 : ℝ)) = 1 / Real.sqrt b ^ 3 := by
  rw [Real.rpow_neg hb.le, one_div, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
  have e : (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) = 3 / 2 := by norm_num
  rw [e]

theorem zF_row {n : ℤ} (hn : n ≠ 0) (m : ℤ) : zF (m, n) = rowT ((23 / 4) * (n : ℝ) ^ 2) ((n : ℝ) / 2) m := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  unfold zF rowT wR
  rw [qN_cast, qR_eq, rpow_aux (by positivity)]

theorem row_a_le {n : ℤ} (hn : n ≠ 0) : 23 / 4 ≤ (23 / 4) * (n : ℝ) ^ 2 := by
  have hpos : 0 < n ^ 2 := by positivity
  have h1 : (1 : ℤ) ≤ n ^ 2 := by omega
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
  linarith

/-- **A row off zero.** -/
theorem row_zF_le {n : ℤ} (hn : n ≠ 0) (hs : Summable fun m : ℤ => zF (m, n)) :
    ∑' m : ℤ, zF (m, n) ≤ 0.48 * (1 / (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have e : (fun m : ℤ => zF (m, n)) = rowT ((23 / 4) * (n : ℝ) ^ 2) ((n : ℝ) / 2) := funext (zF_row hn)
  rw [e] at hs ⊢
  refine (row_le (row_a_le hn) _ hs).trans (le_of_eq ?_)
  ring

theorem zF_zero_row (m : ℤ) : zF (m, 0) = 1 / |(m : ℝ)| ^ 3 := by
  have hb : qR (m, 0) = (m : ℝ) ^ 2 := by
    have h0 : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
    rw [qR_eq, h0]
    ring
  unfold zF
  rw [qN_cast, hb]
  by_cases hm : (m : ℝ) = 0
  · rw [hm]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, Real.zero_rpow (by norm_num)]
    simp
  · rw [rpow_aux (by positivity), Real.sqrt_sq_eq_abs]

theorem zeta3_aux (M : ℕ) :
    ∑ i ∈ Finset.range (M + 3), 1 / ((i : ℝ) + 1) ^ 3 + 1 / (2 * ((M : ℝ) + 3) * ((M : ℝ) + 4)) ≤ 65 / 54 := by
  induction M with
  | zero =>
    norm_num [Finset.sum_range_succ]
  | succ M ih =>
    have hy : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    rw [show M + 1 + 3 = (M + 3) + 1 by ring, Finset.sum_range_succ]
    have e1 : ((M + 3 : ℕ) : ℝ) + 1 = (M : ℝ) + 4 := by
      push_cast <;> ring
    have e2 : ((M + 1 : ℕ) : ℝ) + 3 = (M : ℝ) + 4 := by
      push_cast <;> ring
    have e3 : ((M + 1 : ℕ) : ℝ) + 4 = (M : ℝ) + 5 := by
      push_cast <;> ring
    rw [e1, e2, e3]
    have key : 1 / (2 * ((M : ℝ) + 3) * ((M : ℝ) + 4)) - 1 / (2 * ((M : ℝ) + 4) * ((M : ℝ) + 5)) - 1 / ((M : ℝ) + 4) ^ 3
        = 1 / (((M : ℝ) + 3) * ((M : ℝ) + 4) ^ 3 * ((M : ℝ) + 5)) := by
      field_simp <;> ring
    have hp : 0 ≤ 1 / (((M : ℝ) + 3) * ((M : ℝ) + 4) ^ 3 * ((M : ℝ) + 5)) := by positivity
    linarith

theorem zeta3_partial (N : ℕ) : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 3 ≤ 65 / 54 := by
  have h1 : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 3 ≤ ∑ i ∈ Finset.range (N + 3), 1 / ((i : ℝ) + 1) ^ 3 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => by positivity)
  have h2 := zeta3_aux N
  have h3 : 0 ≤ 1 / (2 * ((N : ℝ) + 3) * ((N : ℝ) + 4)) := by positivity
  linarith

/-- **The row `n = 0`.** -/
theorem row_zero_le (hs : Summable fun m : ℤ => zF (m, 0)) : ∑' m : ℤ, zF (m, 0) ≤ 65 / 27 := by
  have hp : Summable (fun k : ℕ => zF ((k : ℤ), 0)) :=
    hs.comp_injective (i := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
    intro i j h
    have h' : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega
  have hn : Summable (fun k : ℕ => zF (-((k : ℤ) + 1), 0)) := hs.comp_injective hinj
  have hs3 : ∑' m : ℤ, zF (m, 0) = ∑' k : ℕ, zF ((k : ℤ), 0) + ∑' k : ℕ, zF (-((k : ℤ) + 1), 0) :=
    tsum_of_nat_of_neg_add_one (f := fun m : ℤ => zF (m, 0)) hp hn
  rw [hs3]
  have ep : ∀ i : ℕ, zF ((i : ℤ), 0) = 1 / (i : ℝ) ^ 3 := by
    intro i
    rw [zF_zero_row, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg i)]
  have en : ∀ i : ℕ, zF (-((i : ℤ) + 1), 0) = 1 / ((i : ℝ) + 1) ^ 3 := by
    intro i
    have e : (((-((i : ℤ) + 1) : ℤ) : ℝ)) = -((i : ℝ) + 1) := by
      push_cast <;> ring
    have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    rw [zF_zero_row, e, abs_neg, abs_of_nonneg hi]
  have h1 : ∑' k : ℕ, zF ((k : ℤ), 0) ≤ 65 / 54 := by
    refine Real.tsum_le_of_sum_range_le (fun k => zF_nonneg _) (fun N => ?_)
    cases N with
    | zero =>
      norm_num
    | succ N =>
      rw [Finset.sum_range_succ']
      have e2 : ∑ i ∈ Finset.range N, zF (((i + 1 : ℕ) : ℤ), 0) = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 3 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ep, Nat.cast_add, Nat.cast_one]
      rw [e2, ep]
      have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 3 = 0 := by norm_num
      rw [h0, add_zero]
      exact zeta3_partial N
  have h2 : ∑' k : ℕ, zF (-((k : ℤ) + 1), 0) ≤ 65 / 54 := by
    refine Real.tsum_le_of_sum_range_le (fun k => zF_nonneg _) (fun N => ?_)
    have e3 : ∑ i ∈ Finset.range N, zF (-((i : ℤ) + 1), 0) = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 3 :=
      Finset.sum_congr rfl (fun i _ => en i)
    rw [e3]
    exact zeta3_partial N
  linarith

/-- The sum of a row. -/
def zR (n : ℤ) : ℝ := ∑' m : ℤ, zF (m, n)

theorem zSwap_summable : Summable (fun q : ℤ × ℤ => zF (q.2, q.1)) :=
  (Equiv.prodComm ℤ ℤ).summable_iff.mpr zF_summable

theorem zq_lattice_eq : ∑' p : ℤ × ℤ, zF p = ∑' n : ℤ, zR n := by
  have h0 : ∑' q : ℤ × ℤ, zF (q.2, q.1) = ∑' p : ℤ × ℤ, zF p := (Equiv.prodComm ℤ ℤ).tsum_eq zF
  rw [← h0]
  exact zSwap_summable.tsum_prod' (fun n => zSwap_summable.prod_factor n)

theorem zR_row_summable (n : ℤ) : Summable (fun m : ℤ => zF (m, n)) := zSwap_summable.prod_factor n

theorem zR_summable : Summable zR := zSwap_summable.prod

theorem zR_le {n : ℤ} (hn : n ≠ 0) : zR n ≤ 0.48 * (1 / (n : ℝ) ^ 2) := row_zF_le hn (zR_row_summable n)

theorem hasSum_zeta_two_succ : HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  have e : ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) i = 0 := by simp
  rw [e, sub_zero] at h
  have f : (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = fun n : ℕ => (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (n + 1) := by
    funext k
    show (1 : ℝ) / ((k : ℝ) + 1) ^ 2 = 1 / (((k + 1 : ℕ) : ℝ)) ^ 2
    rw [Nat.cast_add, Nat.cast_one]
  rw [f]
  exact h

/-- **`Z_Q(3/2) < 4`, the lattice sum.** -/
theorem zq_three_halves_lt : ∑' p : ℤ × ℤ, zF p < 4 := by
  rw [zq_lattice_eq]
  have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
    intro i j h
    have h' : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega
  have hp : Summable (fun k : ℕ => zR (k : ℤ)) :=
    zR_summable.comp_injective (i := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hn : Summable (fun k : ℕ => zR (-((k : ℤ) + 1))) := zR_summable.comp_injective hinj
  have hs : ∑' n : ℤ, zR n = ∑' k : ℕ, zR (k : ℤ) + ∑' k : ℕ, zR (-((k : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one (f := zR) hp hn
  rw [hs]
  have hD1 : HasSum (fun k : ℕ => (if k = 0 then (65 / 27 : ℝ) else 0) + 0.48 * (1 / (k : ℝ) ^ 2))
      (65 / 27 + 0.48 * (Real.pi ^ 2 / 6)) := (hasSum_ite_eq 0 (65 / 27 : ℝ)).add (hasSum_zeta_two.mul_left 0.48)
  have h1 : ∑' k : ℕ, zR (k : ℤ) ≤ 65 / 27 + 0.48 * (Real.pi ^ 2 / 6) := by
    refine hasSum_le (fun k => ?_) hp.hasSum hD1
    by_cases hk : k = 0
    · subst hk
      have h0 := row_zero_le (zR_row_summable 0)
      have e : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
      rw [if_pos rfl, e, mul_zero, add_zero]
      exact h0
    · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have h0 := zR_le hk'
      rw [Int.cast_natCast] at h0
      rw [if_neg hk, zero_add]
      exact h0
  have hD2 : HasSum (fun k : ℕ => 0.48 * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2)) (0.48 * (Real.pi ^ 2 / 6)) :=
    hasSum_zeta_two_succ.mul_left 0.48
  have h2 : ∑' k : ℕ, zR (-((k : ℤ) + 1)) ≤ 0.48 * (Real.pi ^ 2 / 6) := by
    refine hasSum_le (fun k => ?_) hn.hasSum hD2
    have hk' : -((k : ℤ) + 1) ≠ 0 := by omega
    have h0 := zR_le hk'
    have e : (((-((k : ℤ) + 1) : ℤ) : ℝ)) ^ 2 = ((k : ℝ) + 1) ^ 2 := by
      push_cast <;> ring
    rw [e] at h0
    exact h0
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have h9 : Real.pi ^ 2 < 9.87 := by
    nlinarith [mul_pos (sub_pos.mpr hπ) (show (0 : ℝ) < 3.1416 + Real.pi by linarith)]
  linarith

theorem fiber_eq {σ : ℝ} (hσ0 : σ ≠ 0) (k : ℕ) :
    (if k = 0 then ((0 : ℕ) : ℝ) ^ (-σ) else (rQ k : ℝ) * (k : ℝ) ^ (-σ)) = (rQ k : ℝ) / (k : ℝ) ^ σ := by
  by_cases hk : k = 0
  · subst hk
    simp [rQ_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0)]
  · rw [if_neg hk, Real.rpow_neg (Nat.cast_nonneg k), div_eq_mul_inv]

/-- **`Z_Q(3/2) < 4`, the Dirichlet sum.** -/
theorem zq_three_halves_tsum_lt : ∑' k : ℕ, (rQ k : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ) < 4 := by
  have h : HasSum (fun k : ℕ => if k = 0 then ((0 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) else (rQ k : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)))
      (∑' p : ℤ × ℤ, zF p) := hasSum_fiber (fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ))) zF_summable
  rw [funext (fiber_eq (σ := 3 / 2) (by norm_num))] at h
  rw [h.tsum_eq]
  exact zq_three_halves_lt

end ZQ
end Schema
end SIDEExplicitFormula
