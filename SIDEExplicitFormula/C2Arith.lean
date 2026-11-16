/-
b729, (R339)(3), (L2)'s ALGEBRA: THE ORDERED-FACTORIZATION SUM OBEYS THE OMEGA RECURSION. On the Dirichlet ring of ArithmeticFunction ℤ, with A the
coefficients a(n) restricted to n ≥ 2, F_k = A^k, b = SUM over k ≤ 15 of (-1)^(k+1) L A^k / k, and n ↦ Omega(n) f(n) a derivation, so that
Db (1 + A) = L DA (1 + A^15), and A^15 DA vanishes below 2^16. Every statement holds for an arbitrary a; a(1) enters nowhere.
-/
import SIDEExplicitFormula.C2Spair
import Mathlib

namespace C2Walk

/-- F with the coefficients a a parameter -/
def Fa (a : Nat → Int) : Nat → Nat → Int
  | 0, n => if n = 1 then 1 else 0
  | k + 1, n => ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).foldl (fun s d => s + a d * Fa a k (n / d)) 0

/-- L · b(n), written out -/
def bLa (a : Nat → Int) (n : Nat) : Int :=
  360360 * Fa a 1 n - 180180 * Fa a 2 n + 120120 * Fa a 3 n - 90090 * Fa a 4 n + 72072 * Fa a 5 n - 60060 * Fa a 6 n + 51480 * Fa a 7 n
    - 45045 * Fa a 8 n + 40040 * Fa a 9 n - 36036 * Fa a 10 n + 32760 * Fa a 11 n - 30030 * Fa a 12 n + 27720 * Fa a 13 n - 25740 * Fa a 14 n
    + 24024 * Fa a 15 n

theorem F_eq (D : Int) : ∀ (k n : Nat), F D k n = Fa (aQ D) k n := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [F, Fa, ih]

theorem bL_eq (D : Int) (n : Nat) : bL D n = bLa (aQ D) n := by
  have hr : List.range 15 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
    first
      | rfl
      | decide
  unfold bL bLa
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil, F_eq]
  norm_num
  try ring

abbrev AF := ArithmeticFunction ℤ

/-- the coefficients restricted to n ≥ 2 -/
def Aof (a : Nat → Int) : AF := ⟨fun n => if 2 ≤ n then a n else 0, by simp⟩

theorem Aof_apply (a : Nat → Int) (n : Nat) : Aof a n = if 2 ≤ n then a n else 0 := rfl

theorem foldl_sum (f : Nat → Int) : ∀ (l : List Nat) (s : Int), l.foldl (fun s d => s + f d) s = s + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons x xs ih =>
    intro s
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem Fa_succ (a : Nat → Int) (k n : Nat) :
    Fa a (k + 1) n = ∑ d ∈ (Finset.range (n + 1)).filter (fun d => 2 ≤ d ∧ n % d = 0), a d * Fa a k (n / d) := by
  have h0 : Fa a (k + 1) n =
      ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).foldl (fun s d => s + a d * Fa a k (n / d)) 0 := by
    first
      | rfl
      | rw [Fa]
  have hnd : ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).Nodup := by
    first
      | exact (List.nodup_range).filter _
      | exact (List.nodup_range _).filter _
  have hset : ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).toFinset =
      (Finset.range (n + 1)).filter (fun d => 2 ≤ d ∧ n % d = 0) := by
    ext d
    simp [List.mem_toFinset, List.mem_filter, Finset.mem_filter, List.mem_range, Finset.mem_range]
  rw [h0, foldl_sum (fun d => a d * Fa a k (n / d)), zero_add, ← List.sum_toFinset _ hnd, hset]

theorem Fa_pow (a : Nat → Int) : ∀ (k n : Nat), Fa a k n = (Aof a ^ k) n := by
  intro k
  induction k with
  | zero =>
    intro n
    have h0 : Fa a 0 n = if n = 1 then 1 else 0 := by
      first
        | rfl
        | simp [Fa]
    rw [pow_zero, ArithmeticFunction.one_apply, h0]
  | succ k ih =>
    intro n
    have hconv : (Aof a * Aof a ^ k) n = ∑ d ∈ n.divisors, Aof a d * (Aof a ^ k) (n / d) := by
      rw [ArithmeticFunction.mul_apply]
      exact Nat.sum_divisorsAntidiagonal (fun x y => Aof a x * (Aof a ^ k) y)
    have hsub : (Finset.range (n + 1)).filter (fun d => 2 ≤ d ∧ n % d = 0) ⊆ n.divisors := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_range] at hd
      rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_of_mod_eq_zero hd.2.2, by omega⟩
    have hzero : ∀ d ∈ n.divisors, d ∉ (Finset.range (n + 1)).filter (fun d => 2 ≤ d ∧ n % d = 0) →
        Aof a d * (Aof a ^ k) (n / d) = 0 := by
      intro d hd hnd
      have hd' := Nat.mem_divisors.mp hd
      have hlt : ¬ 2 ≤ d := by
        intro h2
        apply hnd
        simp only [Finset.mem_filter, Finset.mem_range]
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd'.2) hd'.1
        exact ⟨by omega, h2, Nat.mod_eq_zero_of_dvd hd'.1⟩
      rw [Aof_apply, if_neg hlt, zero_mul]
    rw [Fa_succ, pow_succ', hconv, ← Finset.sum_subset hsub hzero]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    rw [ih, Aof_apply, if_pos hd.2.1]

/-- the Omega derivation -/
def dv (f : AF) : AF := ⟨fun n => (ArithmeticFunction.cardFactors n : ℤ) * f n, by simp⟩

theorem dv_apply (f : AF) (n : Nat) : dv f n = (ArithmeticFunction.cardFactors n : ℤ) * f n := rfl

/-- evaluation at n, additive -/
def ev (n : Nat) : AF →+ ℤ where
  toFun f := f n
  map_zero' := rfl
  map_add' _ _ := ArithmeticFunction.add_apply

theorem sub_ap (f g : AF) (n : Nat) : (f - g) n = f n - g n := map_sub (ev n) f g

theorem natmul_ap (m : Nat) (f : AF) (n : Nat) : ((m : AF) * f) n = (m : ℤ) * f n := by
  rw [← nsmul_eq_mul m f]
  exact (map_nsmul (ev n) m f).trans (nsmul_eq_mul _ _)

theorem dv_add (f g : AF) : dv (f + g) = dv f + dv g := by
  ext n
  rw [ArithmeticFunction.add_apply, dv_apply, dv_apply, dv_apply, ArithmeticFunction.add_apply]
  ring

theorem dv_sub (f g : AF) : dv (f - g) = dv f - dv g := by
  ext n
  rw [sub_ap, dv_apply, dv_apply, dv_apply, sub_ap]
  ring

theorem dv_natmul (m : Nat) (f : AF) : dv ((m : AF) * f) = (m : AF) * dv f := by
  ext n
  rw [natmul_ap, dv_apply, dv_apply, natmul_ap]
  ring

theorem dv_mul (f g : AF) : dv (f * g) = dv f * g + f * dv g := by
  ext n
  rw [ArithmeticFunction.add_apply, dv_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨h, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at h
    exact hn h.symm
  have h2 : p.2 ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at h
    exact hn h.symm
  have hO : (ArithmeticFunction.cardFactors n : ℤ) = ArithmeticFunction.cardFactors p.1 + ArithmeticFunction.cardFactors p.2 := by
    rw [← h, ArithmeticFunction.cardFactors_mul h1 h2]
    exact Nat.cast_add _ _
  rw [dv_apply, dv_apply, hO]
  ring

theorem dv_pow_succ (A : AF) : ∀ j : Nat, dv (A ^ (j + 1)) = ((j + 1 : Nat) : AF) * A ^ j * dv A := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : A ^ (j + 1 + 1) = A ^ (j + 1) * A := pow_succ A (j + 1)
    rw [e, dv_mul, ih]
    push_cast
    ring

theorem dv_pow (A : AF) (c d : Nat) (h : c = d + 1) : dv (A ^ c) = (c : AF) * A ^ d * dv A := by
  subst h
  exact dv_pow_succ A d

/-- b as an element of the ring -/
def bR (A : AF) : AF :=
  ((360360 : Nat) : AF) * A ^ 1 - ((180180 : Nat) : AF) * A ^ 2 + ((120120 : Nat) : AF) * A ^ 3 - ((90090 : Nat) : AF) * A ^ 4
    + ((72072 : Nat) : AF) * A ^ 5 - ((60060 : Nat) : AF) * A ^ 6 + ((51480 : Nat) : AF) * A ^ 7 - ((45045 : Nat) : AF) * A ^ 8
    + ((40040 : Nat) : AF) * A ^ 9 - ((36036 : Nat) : AF) * A ^ 10 + ((32760 : Nat) : AF) * A ^ 11 - ((30030 : Nat) : AF) * A ^ 12
    + ((27720 : Nat) : AF) * A ^ 13 - ((25740 : Nat) : AF) * A ^ 14 + ((24024 : Nat) : AF) * A ^ 15

theorem bR_apply (a : Nat → Int) (n : Nat) : bR (Aof a) n = bLa a n := by
  simp only [bR, ArithmeticFunction.add_apply, sub_ap, natmul_ap, bLa, Fa_pow]
  push_cast
  try ring

theorem dv_bR (A : AF) : dv (bR A) * (1 + A) = ((360360 : Nat) : AF) * dv A + ((360360 : Nat) : AF) * A ^ 15 * dv A := by
  unfold bR
  simp only [dv_add, dv_sub, dv_natmul]
  rw [dv_pow A 1 0 rfl, dv_pow A 2 1 rfl, dv_pow A 3 2 rfl, dv_pow A 4 3 rfl, dv_pow A 5 4 rfl, dv_pow A 6 5 rfl, dv_pow A 7 6 rfl, dv_pow A 8 7 rfl,
    dv_pow A 9 8 rfl, dv_pow A 10 9 rfl, dv_pow A 11 10 rfl, dv_pow A 12 11 rfl, dv_pow A 13 12 rfl, dv_pow A 14 13 rfl, dv_pow A 15 14 rfl]
  push_cast
  ring

theorem pow_low (a : Nat → Int) : ∀ (j n : Nat), n < 2 ^ (j + 1) → (Aof a ^ (j + 1)) n = 0 := by
  intro j
  induction j with
  | zero =>
    intro n hn
    have hlt : n < 2 := by simpa using hn
    rw [zero_add, pow_one, Aof_apply, if_neg (by omega : ¬ 2 ≤ n)]
  | succ j ih =>
    intro n hn
    have e : Aof a ^ (j + 1 + 1) = Aof a * Aof a ^ (j + 1) := pow_succ' _ _
    rw [e, ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨h, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    by_cases h2 : 2 ≤ p.1
    · have hlt : p.2 < 2 ^ (j + 1) := by
        have hmul : 2 * p.2 ≤ p.1 * p.2 := Nat.mul_le_mul_right p.2 h2
        rw [h] at hmul
        have hp2 : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by rw [pow_succ, mul_comm]
        rw [hp2] at hn
        obtain ⟨P, hP⟩ : ∃ P : Nat, P = 2 ^ (j + 1) := ⟨_, rfl⟩
        rw [← hP] at hn ⊢
        omega
      rw [ih p.2 hlt, mul_zero]
    · rw [Aof_apply, if_neg h2, zero_mul]

theorem tail_zero (a : Nat → Int) (n : Nat) (hn : n < 65536) : (Aof a ^ 15 * dv (Aof a)) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨h, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases h2 : 2 ≤ p.2
  · have hmul : p.1 * 2 ≤ p.1 * p.2 := Nat.mul_le_mul_left p.1 h2
    rw [h] at hmul
    have hz : (Aof a ^ 15) p.1 = 0 := pow_low a 14 p.1 (by
      norm_num
      omega)
    rw [hz, zero_mul]
  · rw [dv_apply, Aof_apply, if_neg h2, mul_zero, mul_zero]

/-- w(n) = Omega(n) · L · b(n) -/
def wf (a : Nat → Int) (n : Nat) : Int := (ArithmeticFunction.cardFactors n : ℤ) * bLa a n

theorem convolve_eq (a : Nat → Int) (n : Nat) :
    (dv (bR (Aof a)) * Aof a) n = ∑ p ∈ Spair n 2, wf a p.1 * a p.2 := by
  rw [ArithmeticFunction.mul_apply]
  have hsub : Spair n 2 ⊆ n.divisorsAntidiagonal := Finset.filter_subset _ _
  have hzero : ∀ p ∈ n.divisorsAntidiagonal, p ∉ Spair n 2 → dv (bR (Aof a)) p.1 * Aof a p.2 = 0 := by
    intro p hp hnot
    obtain ⟨h, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    by_cases h2 : 2 ≤ p.2
    · have h1 : ¬ 2 ≤ p.1 := by
        intro h1
        exact hnot (mem_Spair.mpr ⟨⟨h, hn0⟩, h1, h2⟩)
      have hp1 : p.1 = 1 := by
        have hne : p.1 ≠ 0 := by
          intro h0
          rw [h0, Nat.zero_mul] at h
          exact hn0 h.symm
        omega
      rw [dv_apply, hp1, ArithmeticFunction.cardFactors_one]
      simp
    · rw [Aof_apply, if_neg h2, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨_, _, h2⟩ := mem_Spair.mp hp
  rw [dv_apply, bR_apply, Aof_apply, if_pos h2]
  rfl

/-- THE RECURSION: for 2 ≤ n < 2^16, w(n) = Omega(n) · L · a(n) - the sum over x y = n, x, y ≥ 2, of w(x) a(y) -/
theorem wf_rec (a : Nat → Int) (n : Nat) (h2 : 2 ≤ n) (hn : n < 65536) :
    wf a n = (ArithmeticFunction.cardFactors n : ℤ) * 360360 * a n - ∑ p ∈ Spair n 2, wf a p.1 * a p.2 := by
  have h : (dv (bR (Aof a)) * (1 + Aof a)) n =
      (((360360 : Nat) : AF) * dv (Aof a) + ((360360 : Nat) : AF) * Aof a ^ 15 * dv (Aof a)) n := by
    rw [dv_bR]
  rw [mul_add, mul_one, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply, natmul_ap, mul_assoc ((360360 : Nat) : AF), natmul_ap,
    tail_zero a n hn, convolve_eq, dv_apply, dv_apply, bR_apply, Aof_apply, if_pos h2] at h
  have e : (((360360 : Nat) : ℤ)) = 360360 := by norm_num
  rw [e] at h
  have hw : wf a n = (ArithmeticFunction.cardFactors n : ℤ) * bLa a n := rfl
  rw [hw]
  linarith

theorem Fa_congr (a b : Nat → Int) (N : Nat) (h : ∀ m, m ≤ N → a m = b m) :
    ∀ (k n : Nat), n ≤ N → Fa a k n = Fa b k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    rw [Fa_succ, Fa_succ]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    rw [h d (by omega), ih (n / d) (le_trans (Nat.div_le_self n d) hn)]

theorem bLa_congr (a b : Nat → Int) (N n : Nat) (h : ∀ m, m ≤ N → a m = b m) (hn : n ≤ N) : bLa a n = bLa b n := by
  have e := fun k => Fa_congr a b N h k n hn
  simp only [bLa, e]

theorem Fa_low (a : Nat → Int) (n : Nat) (hn : n < 2) : ∀ k, 1 ≤ k → Fa a k n = 0 := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Fa_succ]
  apply Finset.sum_eq_zero
  intro d hd
  simp only [Finset.mem_filter, Finset.mem_range] at hd
  exfalso
  omega

theorem bLa_low (a : Nat → Int) (n : Nat) (hn : n < 2) : bLa a n = 0 := by
  have e := Fa_low a n hn
  unfold bLa
  simp [e]

end C2Walk
