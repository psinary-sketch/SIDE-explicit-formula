/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/LogDeriv.lean
THIS PROGRAMME'S WORK (act b731, ruling (R341)(3), groups B and C of relay data/b731_logderiv_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE LOGARITHMIC DERIVATIVE'S SERIES. `Z_Q` has no Euler product; `c` solves `c ⍟ r_Q = log · r_Q` by recursion, `r_Q(1) = 2`, and `Z_Q(3/2) < 4` bounds
its absolute series on the line `Re s = 3/2` itself. The same bound keeps `|Z_Q − 2| < 2` there, so `Z_Q` has no zero in `Re s ≥ 3/2`. Nothing here proves
RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Bound
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convolution

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

/-- The two vectors of norm one. -/
theorem boxF_one : boxF 1 = {(1, 0), (-1, 0)} := by
  ext ⟨m, n⟩
  constructor
  · intro h
    have hq : Q0form m n = ((1 : ℕ) : ℤ) := (Finset.mem_filter.mp h).2
    have hq' : Q0form m n = 1 := by simpa using hq
    have h4 := four_mul_Q0form m n
    rw [hq'] at h4
    have h5 : 23 * n ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * m + n)]
    have h6 : n ^ 2 < 1 := by linarith
    have h7 : n ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg n)
    have hn : n = 0 := (pow_eq_zero_iff two_ne_zero).mp h7
    subst hn
    have hm : (m - 1) * (m + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with h8 | h8
    · have h9 : m = 1 := by omega
      subst h9
      simp
    · have h9 : m = -1 := by omega
      subst h9
      simp
  · intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    unfold boxF
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
        Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩, by norm_num [Q0form]⟩

/-- `r_Q(1) = 2`, the value the recursion divides by. -/
theorem rQ_one : rQ 1 = 2 := by
  rw [rQ_eq_card one_ne_zero, boxF_one]
  refine Finset.card_pair (fun h => ?_)
  have h1 := congrArg Prod.fst h
  norm_num at h1

/-- **The coefficients of `−Z_Q'/Z_Q`**, by recursion from `r_Q`. -/
def cQ (n : ℕ) : ℝ :=
  if _h : n ≤ 1 then 0
  else ((rQ n : ℝ) * Real.log n - ∑ d ∈ n.properDivisors, if _h' : d < n then cQ d * (rQ (n / d) : ℝ) else 0) / 2
termination_by n

theorem cQ_le_one {n : ℕ} (h : n ≤ 1) : cQ n = 0 := by
  rw [cQ.eq_def, dif_pos h]

theorem cQ_eq {n : ℕ} (hn : 2 ≤ n) :
    2 * cQ n = (rQ n : ℝ) * Real.log n - ∑ d ∈ n.properDivisors, cQ d * (rQ (n / d) : ℝ) := by
  have h0 : ¬ n ≤ 1 := by omega
  have e := cQ.eq_def n
  rw [dif_neg h0] at e
  have es : ∑ d ∈ n.properDivisors, (if _h' : d < n then cQ d * (rQ (n / d) : ℝ) else 0)
      = ∑ d ∈ n.properDivisors, cQ d * (rQ (n / d) : ℝ) :=
    Finset.sum_congr rfl (fun d hd => dif_pos (Nat.mem_properDivisors.mp hd).2)
  rw [es] at e
  rw [e]
  ring

/-- **`c ⍟ r_Q = log · r_Q`** off `0`. -/
theorem cQ_conv {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, cQ p.1 * (rQ p.2 : ℝ) = (rQ n : ℝ) * Real.log n := by
  have e : ∑ p ∈ n.divisorsAntidiagonal, cQ p.1 * (rQ p.2 : ℝ) = ∑ d ∈ n.divisors, cQ d * (rQ (n / d) : ℝ) :=
    Nat.sum_divisorsAntidiagonal (fun a b => cQ a * (rQ b : ℝ))
  rw [e]
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h2
  · rw [Nat.divisors_one, Finset.sum_singleton, cQ_le_one le_rfl, Nat.cast_one, Real.log_one]
    ring
  · have h3 := cQ_eq h2
    rw [← Nat.insert_self_properDivisors hn, Finset.sum_insert Nat.self_notMem_properDivisors,
      Nat.div_self (by omega), rQ_one]
    push_cast
    linarith

/-- The term of `Z_Q(3/2)`. -/
def wQ (k : ℕ) : ℝ := (rQ k : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)

/-- The term of the absolute series of `c` at `3/2`. -/
def uQ (k : ℕ) : ℝ := |cQ k| / (k : ℝ) ^ (3 / 2 : ℝ)

/-- The term of `−Z_Q'(3/2)`. -/
def vQ (k : ℕ) : ℝ := (rQ k : ℝ) * Real.log k / (k : ℝ) ^ (3 / 2 : ℝ)

theorem wQ_nonneg (k : ℕ) : 0 ≤ wQ k :=
  div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem uQ_nonneg (k : ℕ) : 0 ≤ uQ k :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem vQ_nonneg (k : ℕ) : 0 ≤ vQ k :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg k)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem wQ_one : wQ 1 = 2 := by
  unfold wQ
  rw [rQ_one, Nat.cast_one, Real.one_rpow]
  norm_num

theorem wQ_summable : Summable wQ :=
  rQ_term_summable (σ := 3 / 2) (by norm_num)

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

/-- One step of the recursion, in absolute value. -/
theorem uQ_step {n : ℕ} (hn : 2 ≤ n) :
    2 * uQ n ≤ vQ n + ∑ d ∈ n.properDivisors, uQ d * wQ (n / d) := by
  have hP : 0 < (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  have hR : 0 ≤ (rQ n : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
  have hS : |∑ d ∈ n.properDivisors, cQ d * (rQ (n / d) : ℝ)|
      ≤ ∑ d ∈ n.properDivisors, |cQ d| * (rQ (n / d) : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ (rQ (n / d) : ℝ))]
  have hab : 2 * |cQ n| ≤ (rQ n : ℝ) * Real.log n + ∑ d ∈ n.properDivisors, |cQ d| * (rQ (n / d) : ℝ) := by
    have e : 2 * |cQ n| = |2 * cQ n| := by rw [abs_mul, abs_two]
    rw [e, cQ_eq hn]
    have h := abs_sub_le_add ((rQ n : ℝ) * Real.log n) (∑ d ∈ n.properDivisors, cQ d * (rQ (n / d) : ℝ))
    rw [abs_of_nonneg hR] at h
    linarith
  have hterm : ∀ d ∈ n.properDivisors,
      |cQ d| * (rQ (n / d) : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) = uQ d * wQ (n / d) := by
    intro d hd
    have hdvd := (Nat.mem_properDivisors.mp hd).1
    have e : (n : ℝ) ^ (3 / 2 : ℝ) = (d : ℝ) ^ (3 / 2 : ℝ) * ((n / d : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg (n / d)), ← Nat.cast_mul,
        Nat.mul_div_cancel' hdvd]
    unfold uQ wQ
    rw [e, div_mul_div_comm]
  calc 2 * uQ n = (2 * |cQ n|) / (n : ℝ) ^ (3 / 2 : ℝ) := by
        unfold uQ
        ring
    _ ≤ ((rQ n : ℝ) * Real.log n + ∑ d ∈ n.properDivisors, |cQ d| * (rQ (n / d) : ℝ)) / (n : ℝ) ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hab hP.le
    _ = vQ n + ∑ d ∈ n.properDivisors, uQ d * wQ (n / d) := by
        unfold vQ
        rw [add_div, Finset.sum_div, Finset.sum_congr rfl hterm]

/-- The indices `2 ≤ n < N`. -/
def tQ (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun n => 2 ≤ n)

/-- A proper divisor and its cofactor. -/
def pairQ (x : Σ _ : ℕ, ℕ) : ℕ × ℕ := (x.2, x.1 / x.2)

/-- The double sum over `n` and its proper divisors injects into the product. -/
theorem double_le (g : ℕ → ℕ → ℝ) (hg : ∀ a b, 0 ≤ g a b) (N : ℕ) :
    ∑ n ∈ tQ N, ∑ d ∈ n.properDivisors, g d (n / d) ≤ ∑ d ∈ Finset.range N, ∑ k ∈ tQ N, g d k := by
  have hinj : Set.InjOn pairQ ((tQ N).sigma (fun n => n.properDivisors) : Finset (Σ _ : ℕ, ℕ)) := by
    rintro ⟨n, d⟩ hx ⟨n', d'⟩ hy h
    have hx1 := Finset.mem_sigma.mp (Finset.mem_coe.mp hx)
    have hy1 := Finset.mem_sigma.mp (Finset.mem_coe.mp hy)
    have hd : d = d' := congrArg Prod.fst h
    have hk : n / d = n' / d' := congrArg Prod.snd h
    subst hd
    have h1 : d ∈ n.properDivisors := hx1.2
    have h2 : d ∈ n'.properDivisors := hy1.2
    have d1 := (Nat.mem_properDivisors.mp h1).1
    have d2 := (Nat.mem_properDivisors.mp h2).1
    have e : n = n' := by
      calc n = n / d * d := (Nat.div_mul_cancel d1).symm
        _ = n' / d * d := by rw [hk]
        _ = n' := Nat.div_mul_cancel d2
    subst e
    rfl
  have hsub : ((tQ N).sigma (fun n => n.properDivisors) : Finset (Σ _ : ℕ, ℕ)).image pairQ
      ⊆ Finset.range N ×ˢ tQ N := by
    intro y hy
    obtain ⟨⟨n, d⟩, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx1 := Finset.mem_sigma.mp hx
    have h1 : n ∈ tQ N := hx1.1
    have h2 : d ∈ n.properDivisors := hx1.2
    have hn := Finset.mem_filter.mp h1
    have hnN : n < N := Finset.mem_range.mp hn.1
    have hn2 : 2 ≤ n := hn.2
    have hd := Nat.mem_properDivisors.mp h2
    have h3 : n / d * d = n := Nat.div_mul_cancel hd.1
    have h4 : n / d ≤ 1 → False := fun h => by
      have h5 : n / d * d ≤ 1 * d := Nat.mul_le_mul_right d h
      rw [h3, one_mul] at h5
      exact absurd hd.2 (not_lt.mpr h5)
    have h6 : 2 ≤ n / d := by
      by_contra hlt
      exact h4 (Nat.le_of_lt_succ (not_le.mp hlt))
    have h7 : n / d ≤ n := Nat.div_le_self n d
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hd.2.trans hnN),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h7.trans_lt hnN), h6⟩⟩
  calc ∑ n ∈ tQ N, ∑ d ∈ n.properDivisors, g d (n / d)
      = ∑ x ∈ (tQ N).sigma (fun n => n.properDivisors), g x.2 (x.1 / x.2) :=
        Finset.sum_sigma' (tQ N) (fun n => n.properDivisors) (fun n d => g d (n / d))
    _ = ∑ y ∈ ((tQ N).sigma (fun n => n.properDivisors) : Finset (Σ _ : ℕ, ℕ)).image pairQ, g y.1 y.2 :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ Finset.range N ×ˢ tQ N, g y.1 y.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hg _ _)
    _ = ∑ d ∈ Finset.range N, ∑ k ∈ tQ N, g d k := Finset.sum_product' (Finset.range N) (tQ N) g

theorem uQ_sum_eq (N : ℕ) : ∑ n ∈ Finset.range N, uQ n = ∑ n ∈ tQ N, uQ n := by
  unfold tQ
  refine (Finset.sum_filter_of_ne (fun x _ hx => ?_)).symm
  show 2 ≤ x
  by_contra h
  have h1 : x ≤ 1 := by omega
  exact hx (by
    unfold uQ
    rw [cQ_le_one h1, abs_zero, zero_div])

/-- The tail of `Z_Q(3/2)` past its first term. -/
theorem tQ_wQ_le (N : ℕ) : ∑ k ∈ tQ N, wQ k ≤ ∑' k, wQ k - 2 := by
  have h1 : 1 ∉ tQ N := fun h => by
    have h2 : 2 ≤ 1 := (Finset.mem_filter.mp h).2
    omega
  have h := wQ_summable.sum_le_tsum (insert 1 (tQ N)) (fun i _ => wQ_nonneg i)
  rw [Finset.sum_insert h1, wQ_one] at h
  linarith

/-- **The partial sums of the absolute series of `c`**, bounded by `Z_Q(3/2) < 4`. -/
theorem uQ_sum_le (hv : Summable vQ) (N : ℕ) :
    ∑ n ∈ Finset.range N, uQ n ≤ (∑' k, vQ k) / (4 - ∑' k, wQ k) := by
  have ht : ∑' k, wQ k < 4 := zq_three_halves_tsum_lt
  have hpos : 0 < 4 - ∑' k, wQ k := by linarith
  rw [le_div_iff₀ hpos]
  have hS : 0 ≤ ∑ n ∈ Finset.range N, uQ n := Finset.sum_nonneg (fun n _ => uQ_nonneg n)
  have hT := tQ_wQ_le N
  have hV : ∑ n ∈ tQ N, vQ n ≤ ∑' k, vQ k := hv.sum_le_tsum _ (fun i _ => vQ_nonneg i)
  have h1 : ∑ n ∈ tQ N, 2 * uQ n ≤ ∑ n ∈ tQ N, (vQ n + ∑ d ∈ n.properDivisors, uQ d * wQ (n / d)) :=
    Finset.sum_le_sum (fun n hn => uQ_step (Finset.mem_filter.mp hn).2)
  have e1 : ∑ n ∈ tQ N, 2 * uQ n = 2 * ∑ n ∈ Finset.range N, uQ n := by
    rw [uQ_sum_eq, Finset.mul_sum]
  have e2 : ∑ n ∈ tQ N, (vQ n + ∑ d ∈ n.properDivisors, uQ d * wQ (n / d))
      = ∑ n ∈ tQ N, vQ n + ∑ n ∈ tQ N, ∑ d ∈ n.properDivisors, uQ d * wQ (n / d) :=
    Finset.sum_add_distrib
  rw [e1, e2] at h1
  have h2 := double_le (fun a b => uQ a * wQ b) (fun a b => mul_nonneg (uQ_nonneg a) (wQ_nonneg b)) N
  have e3 := Finset.sum_mul_sum (Finset.range N) (tQ N) uQ wQ
  have h3 : ∑ n ∈ tQ N, ∑ d ∈ n.properDivisors, uQ d * wQ (n / d)
      ≤ (∑ n ∈ Finset.range N, uQ n) * ∑ k ∈ tQ N, wQ k := by
    rw [e3]
    exact h2
  have h4 := mul_le_mul_of_nonneg_left hT hS
  nlinarith [h1, h3, h4, hV]

/-- **The absolute series of `c` at `3/2`**, on the summability of `−Z_Q'(3/2)`. -/
theorem uQ_summable (hv : Summable vQ) : Summable uQ :=
  summable_of_sum_range_le uQ_nonneg (uQ_sum_le hv)

end ZQ
end Schema
end SIDEExplicitFormula
