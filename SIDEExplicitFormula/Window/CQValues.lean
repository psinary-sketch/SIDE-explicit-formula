import SIDEExplicitFormula.Window.CQData
import SIDEExplicitFormula.Window.KFast
import SIDEExplicitFormula.Schema.ZQ.LogDeriv
import SIDEExplicitFormula.Schema.ZQ.Lattice
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The values of `cQ` to 1023

`r_Q(k)` for `1 ≤ k ≤ 1023` is the length of the list CQData.lean holds at `k` (`rQ_eq_cqR`): every representation of such a `k`
lies in the box `|m| ≤ 38`, `|n| ≤ 13`, each listed pair represents `k` and no pair is listed twice, and the lists together count
the box. `log n` for `1 ≤ n ≤ 1023` is the sum over the primes below 1024 of an exponent times `log p`, the product of the powers
checked (`log_eq_cqEv`). `cQ n` for `n ≤ 1023` is the combination `∑_p z(n, p) log p` the data holds (`cQ_eq_comb`), by strong
induction from `cQ_eq`, the coefficients checked against the recursion at each `n` and each prime dividing it. Each check is an
evaluation by the kernel; no tactic adds an axiom beyond the standard three.
-/

namespace SIDEExplicitFormula
namespace Window

/-- A conjunction by halving, read at one index. -/
theorem allDC_at {p : ℕ → Bool} {d lo len n : ℕ} (hl : len ≤ 2 ^ d) (h : allDC p lo len d = true)
    (h1 : lo ≤ n) (h2 : n < lo + len) : p n = true := by
  have h3 := allDC_spec p d lo len hl h (n - lo) (by omega)
  rwa [show lo + (n - lo) = n by omega] at h3

/-! ## `r_Q` from the representations -/

/-- The box every representation of `1 ≤ k ≤ 1023` lies in. -/
def cqBox : Finset (ℤ × ℤ) := Finset.Icc (-38 : ℤ) 38 ×ˢ Finset.Icc (-13 : ℤ) 13

/-- The representations of `k` the data lists. -/
def cqReps (k : ℕ) : List (ℤ × ℤ) := repTree.get k

/-- Their number. -/
def cqR (k : ℕ) : ℕ := (cqReps k).length

/-- The representations of `k` in the box. -/
def cqFib (k : ℕ) : Finset (ℤ × ℤ) := cqBox.filter (fun q : ℤ × ℤ => Schema.Q0form q.1 q.2 = (k : ℤ))

theorem mem_cqBox {k : ℕ} (hk : k ≤ 1023) {m n : ℤ} (h : Schema.Q0form m n = (k : ℤ)) : (m, n) ∈ cqBox := by
  have h4 := Schema.four_mul_Q0form m n
  rw [h] at h4
  have hk' : (k : ℤ) ≤ 1023 := by exact_mod_cast hk
  have hn1 : n ≤ 13 := by nlinarith [sq_nonneg (2 * m + n)]
  have hn2 : -13 ≤ n := by nlinarith [sq_nonneg (2 * m + n)]
  have ha1 : 2 * m + n ≤ 63 := by nlinarith [sq_nonneg n]
  have ha2 : -63 ≤ 2 * m + n := by nlinarith [sq_nonneg n]
  simp only [cqBox, Finset.mem_product, Finset.mem_Icc]
  omega

theorem boxF_eq_cqFib {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ 1023) : Schema.ZQ.boxF k = cqFib k := by
  ext ⟨m, n⟩
  simp only [Schema.ZQ.boxF, cqFib, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨mem_cqBox hk h, h⟩
  · rintro ⟨-, h⟩
    exact ⟨Schema.ZQ.mem_box hk0 h, h⟩

/-- Each listed pair lies in the box and represents `k`; no pair is listed twice. -/
def cqRepOK (k : ℕ) : Bool :=
  (cqReps k).all (fun q => decide (-38 ≤ q.1 ∧ q.1 ≤ 38 ∧ -13 ≤ q.2 ∧ q.2 ≤ 13) &&
    decide (Schema.Q0form q.1 q.2 = (k : ℤ))) && decide (cqReps k).Nodup

theorem cq_reps_ok : allDC cqRepOK 1 1023 10 = true := by decide +kernel

/-- The representations in the box of `1 ≤ k ≤ 1023`, counted, equal the total of the lists. -/
theorem cq_reps_count :
    (cqBox.filter (fun q : ℤ × ℤ => 1 ≤ Schema.Q0form q.1 q.2 ∧ Schema.Q0form q.1 q.2 ≤ 1023)).card =
      ∑ k ∈ Finset.Icc 1 1023, cqR k := by
  decide +kernel

theorem cqReps_spec {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 1023) :
    (cqReps k).toFinset ⊆ cqFib k ∧ (cqReps k).Nodup := by
  have h := allDC_at (by norm_num) cq_reps_ok hk1 (by omega : k < 1 + 1023)
  simp only [cqRepOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  intro q hq
  obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := h.1 q (List.mem_toFinset.mp hq)
  simp only [cqFib, cqBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨a1, a2⟩, a3, a4⟩, a5⟩

theorem cq_fib_union :
    cqBox.filter (fun q : ℤ × ℤ => 1 ≤ Schema.Q0form q.1 q.2 ∧ Schema.Q0form q.1 q.2 ≤ 1023) =
      (Finset.Icc 1 1023).biUnion cqFib := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc, cqFib]
  constructor
  · rintro ⟨hb, h1, h2⟩
    have e := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ Schema.Q0form q.1 q.2)
    exact ⟨(Schema.Q0form q.1 q.2).toNat, ⟨by omega, by omega⟩, hb, e.symm⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, hb, he⟩
    exact ⟨hb, by omega, by omega⟩

theorem cq_fib_sum :
    (cqBox.filter (fun q : ℤ × ℤ => 1 ≤ Schema.Q0form q.1 q.2 ∧ Schema.Q0form q.1 q.2 ≤ 1023)).card =
      ∑ k ∈ Finset.Icc 1 1023, (cqFib k).card := by
  rw [cq_fib_union]
  apply Finset.card_biUnion
  intro j _ k _ hjk
  show Disjoint (cqFib j) (cqFib k)
  refine Finset.disjoint_left.mpr (fun q hq hq' => hjk ?_)
  simp only [cqFib, Finset.mem_filter] at hq hq'
  have e := hq.2.symm.trans hq'.2
  exact_mod_cast e

/-- **`r_Q(k)` is the length of the list the data holds at `k`**, for `1 ≤ k ≤ 1023`. -/
theorem rQ_eq_cqR {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 1023) : Schema.rQ k = cqR k := by
  have hle : ∀ j ∈ Finset.Icc 1 1023, cqR j ≤ (cqFib j).card := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hs, hnd⟩ := cqReps_spec hj.1 hj.2
    rw [cqR, ← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card hs
  have hsum : ∑ j ∈ Finset.Icc 1 1023, cqR j = ∑ j ∈ Finset.Icc 1 1023, (cqFib j).card := by
    rw [← cq_reps_count, cq_fib_sum]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_Icc.mpr ⟨hk1, hk⟩)
  rw [Schema.ZQ.rQ_eq_card (k := k) (by omega), boxF_eq_cqFib (by omega) hk, ← heq]

/-! ## `log n` over the primes below 1024 -/

/-- The exponent of `p` in `n`, read by at most `f` divisions. -/
def cqEvp (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if 0 < n ∧ n % p = 0 then cqEvp p f (n / p) + 1 else 0

/-- The exponent of `p` in `n`, read by at most ten divisions. -/
def cqEv (p n : ℕ) : ℕ := cqEvp p 10 n

theorem primeList_nodup : primeList.Nodup := by decide +kernel

theorem primeList_two_le : ∀ p ∈ primeList, 2 ≤ p := by decide +kernel

/-- The primes below 1024, as a `Finset`. -/
def cqPF : Finset ℕ := ⟨(primeList : Multiset ℕ), Multiset.coe_nodup.mpr primeList_nodup⟩

theorem mem_cqPF {p : ℕ} : p ∈ cqPF ↔ p ∈ primeList := by
  first
  | exact Iff.rfl
  | simp [cqPF]

/-- The product of the powers at `n` is `n`. -/
def cqProdOK (n : ℕ) : Bool := (∏ p ∈ cqPF, p ^ cqEv p n) == n

theorem cq_prod_ok : allDC cqProdOK 1 1023 10 = true := by decide +kernel

/-- **`log n = ∑_p e(p, n) log p`** over the primes below 1024, for `1 ≤ n ≤ 1023`. -/
theorem log_eq_cqEv {n : ℕ} (h1 : 1 ≤ n) (h : n ≤ 1023) :
    Real.log n = ∑ p ∈ cqPF, (cqEv p n : ℝ) * Real.log p := by
  have hp := allDC_at (by norm_num) cq_prod_ok h1 (by omega : n < 1 + 1023)
  simp only [cqProdOK, beq_iff_eq] at hp
  have hpos : ∀ p ∈ cqPF, (p : ℝ) ≠ 0 := fun p hp' => by
    have h2 := primeList_two_le p (mem_cqPF.mp hp')
    exact_mod_cast (by omega : p ≠ 0)
  have hf : ∀ p ∈ cqPF, ((p ^ cqEv p n : ℕ) : ℝ) ≠ 0 := fun p hp' => by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (hpos p hp')
  calc Real.log n = Real.log ((∏ p ∈ cqPF, p ^ cqEv p n : ℕ) : ℝ) := by rw [hp]
    _ = ∑ p ∈ cqPF, (cqEv p n : ℝ) * Real.log p := by
      rw [Nat.cast_prod, Real.log_prod hf]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Nat.cast_pow, Real.log_pow]

/-! ## `cQ` as the combination the data holds -/

/-- The coefficient of `log p` in a list of pairs. -/
def cqZl : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => 0
  | q :: t, p => if q.1 = p then q.2 else cqZl t p

/-- The coefficient of `log p` in the combination the data holds at `n`, `0` where `p` does not divide `n`. -/
def cqZ (n p : ℕ) : ℤ := if n % p = 0 then cqZl (cqTree.get n) p else 0

theorem cqZ_of_mod {n p : ℕ} (h : n % p ≠ 0) : cqZ n p = 0 := by
  unfold cqZ
  rw [if_neg h]

theorem cqEvp_of_mod (p : ℕ) : ∀ (f n : ℕ), n % p ≠ 0 → cqEvp p f n = 0
  | 0, _, _ => rfl
  | f + 1, n, h => by
    simp only [cqEvp]
    rw [if_neg (show ¬(0 < n ∧ n % p = 0) from fun hh => h hh.2)]

theorem cqEv_of_mod {n p : ℕ} (h : n % p ≠ 0) : cqEv p n = 0 := cqEvp_of_mod p 10 n h

theorem cqTree_zero : cqTree.get 0 = [] := by decide +kernel

theorem cqTree_one : cqTree.get 1 = [] := by decide +kernel

theorem cqZ_zero (p : ℕ) : cqZ 0 p = 0 := by
  unfold cqZ
  rw [cqTree_zero]
  split_ifs <;> rfl

theorem cqZ_one (p : ℕ) : cqZ 1 p = 0 := by
  unfold cqZ
  rw [cqTree_one]
  split_ifs <;> rfl

/-- At `n`, for each prime dividing `n`, twice the coefficient against the recursion of `cQ_eq`. -/
def cqOK (n : ℕ) : Bool :=
  primeList.all (fun p => if n % p = 0 then
    2 * cqZ n p == (cqR n : ℤ) * (cqEv p n : ℤ) - ∑ d ∈ n.properDivisors, cqZ d p * (cqR (n / d) : ℤ) else true)

theorem cq_ok_0 : allDC cqOK 2 128 7 = true := by decide +kernel

theorem cq_ok_1 : allDC cqOK 130 128 7 = true := by decide +kernel

theorem cq_ok_2 : allDC cqOK 258 128 7 = true := by decide +kernel

theorem cq_ok_3 : allDC cqOK 386 128 7 = true := by decide +kernel

theorem cq_ok_4 : allDC cqOK 514 128 7 = true := by decide +kernel

theorem cq_ok_5 : allDC cqOK 642 128 7 = true := by decide +kernel

theorem cq_ok_6 : allDC cqOK 770 128 7 = true := by decide +kernel

theorem cq_ok_7 : allDC cqOK 898 126 7 = true := by decide +kernel

theorem cq_ok {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 1023) : cqOK n = true := by
  by_cases c0 : n < 130
  · exact allDC_at (by norm_num) cq_ok_0 h2 (by omega)
  by_cases c1 : n < 258
  · exact allDC_at (by norm_num) cq_ok_1 (by omega) (by omega)
  by_cases c2 : n < 386
  · exact allDC_at (by norm_num) cq_ok_2 (by omega) (by omega)
  by_cases c3 : n < 514
  · exact allDC_at (by norm_num) cq_ok_3 (by omega) (by omega)
  by_cases c4 : n < 642
  · exact allDC_at (by norm_num) cq_ok_4 (by omega) (by omega)
  by_cases c5 : n < 770
  · exact allDC_at (by norm_num) cq_ok_5 (by omega) (by omega)
  by_cases c6 : n < 898
  · exact allDC_at (by norm_num) cq_ok_6 (by omega) (by omega)
  · exact allDC_at (by norm_num) cq_ok_7 (by omega) (by omega)

theorem cq_holds {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 1023) {p : ℕ} (hp : p ∈ primeList) (hpn : n % p = 0) :
    2 * cqZ n p = (cqR n : ℤ) * (cqEv p n : ℤ) - ∑ d ∈ n.properDivisors, cqZ d p * (cqR (n / d) : ℤ) := by
  have hc := cq_ok h2 hn
  unfold cqOK at hc
  have h := List.all_eq_true.1 hc p hp
  simp only [if_pos hpn, beq_iff_eq] at h
  exact h

/-- **`cQ n = ∑_p z(n, p) log p`** for `n ≤ 1023`, the coefficients `z` those of CQData.lean. -/
theorem cQ_eq_comb : ∀ n : ℕ, n ≤ 1023 → Schema.ZQ.cQ n = ∑ p ∈ cqPF, (cqZ n p : ℝ) * Real.log p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with h0 | h1 | h2
    · subst h0
      rw [Schema.ZQ.cQ_le_one (show (0 : ℕ) ≤ 1 by norm_num)]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [cqZ_zero]
      simp
    · subst h1
      rw [Schema.ZQ.cQ_le_one le_rfl]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [cqZ_one]
      simp
    · have e := Schema.ZQ.cQ_eq h2
      have hlog := log_eq_cqEv (by omega : 1 ≤ n) hn
      have hrn : (Schema.rQ n : ℝ) = (cqR n : ℝ) := by rw [rQ_eq_cqR (by omega) hn]
      have hsum : ∑ d ∈ n.properDivisors, Schema.ZQ.cQ d * (Schema.rQ (n / d) : ℝ) =
          ∑ d ∈ n.properDivisors, (∑ p ∈ cqPF, (cqZ d p : ℝ) * Real.log p) * (cqR (n / d) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd' := Nat.mem_properDivisors.mp hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
        have hdn : d ≤ n := hd'.2.le
        have hq1 : 1 ≤ n / d := Nat.div_pos hdn hdpos
        have hq2 : n / d ≤ 1023 := le_trans (Nat.div_le_self n d) hn
        rw [ih d hd'.2 (le_trans hdn hn), rQ_eq_cqR hq1 hq2]
      have hchk : ∀ p ∈ cqPF, 2 * (cqZ n p : ℝ) =
          (cqR n : ℝ) * (cqEv p n : ℝ) - ∑ d ∈ n.properDivisors, (cqZ d p : ℝ) * (cqR (n / d) : ℝ) := by
        intro p hp
        by_cases hpn : n % p = 0
        · have h3 := cq_holds h2 hn (mem_cqPF.mp hp) hpn
          first
          | exact_mod_cast h3
          | (have h4 := congrArg (Int.cast : ℤ → ℝ) h3
             push_cast at h4
             linarith)
        · have hz : ∀ d ∈ n.properDivisors, cqZ d p = 0 := by
            intro d hd
            apply cqZ_of_mod
            intro hdp
            exact hpn (Nat.mod_eq_zero_of_dvd
              (dvd_trans (Nat.dvd_of_mod_eq_zero hdp) (Nat.mem_properDivisors.mp hd).1))
          have hs : ∑ d ∈ n.properDivisors, (cqZ d p : ℝ) * (cqR (n / d) : ℝ) = 0 :=
            Finset.sum_eq_zero (fun d hd => by rw [hz d hd]; simp)
          rw [hs, cqZ_of_mod hpn, cqEv_of_mod hpn]
          simp
      have key : 2 * Schema.ZQ.cQ n = 2 * ∑ p ∈ cqPF, (cqZ n p : ℝ) * Real.log p := by
        rw [e, hrn, hlog, hsum, Finset.mul_sum, Finset.mul_sum]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        have hc := hchk p hp
        have hm : ∑ d ∈ n.properDivisors, (cqZ d p : ℝ) * Real.log p * (cqR (n / d) : ℝ) =
            (∑ d ∈ n.properDivisors, (cqZ d p : ℝ) * (cqR (n / d) : ℝ)) * Real.log p := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d _
          ring
        have h2z : 2 * ((cqZ n p : ℝ) * Real.log p) = 2 * (cqZ n p : ℝ) * Real.log p := by ring
        rw [hm, h2z, hc]
        ring
      linarith

end Window
end SIDEExplicitFormula
