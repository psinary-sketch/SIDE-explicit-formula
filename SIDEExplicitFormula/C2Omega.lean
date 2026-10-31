/-
b729, (R339)(3): TRIAL DIVISION IS OMEGA. `bigOmega n` is Mathlib's `ArithmeticFunction.cardFactors n` for n ≥ 1.
-/
import SIDEExplicitFormula.C2Walk
import Mathlib

namespace C2Walk

theorem omegaAux_succ (f n p : Nat) :
    omegaAux (f + 1) n p =
      if n < 2 then 0
      else if n < p * p then 1
      else if n % p = 0 then omegaAux f (n / p) p + 1
      else omegaAux f n (p + 1) := by
  first
    | rfl
    | simp [omegaAux]
    | rw [omegaAux]

theorem omegaAux_eq : ∀ (f n p : Nat), 2 ≤ p → 1 ≤ n → n + 1 ≤ f + p →
    (∀ r : Nat, r.Prime → r ∣ n → p ≤ r) → omegaAux f n p = ArithmeticFunction.cardFactors n := by
  intro f
  induction f with
  | zero =>
    intro n p hp hn hf hr
    by_cases h1 : n = 1
    · subst h1
      simp [omegaAux]
    · exfalso
      have hmf := hr n.minFac (Nat.minFac_prime h1) (Nat.minFac_dvd n)
      have hle := Nat.minFac_le (n := n) (by omega)
      omega
  | succ f ih =>
    intro n p hp hn hf hr
    rw [omegaAux_succ]
    by_cases h2 : n < 2
    · have h1 : n = 1 := by omega
      subst h1
      simp
    rw [if_neg h2]
    by_cases h3 : n < p * p
    · rw [if_pos h3]
      have hprime : n.Prime := by
        by_contra hnp
        have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
        have hmf := hr n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
        have hpp : p * p ≤ n.minFac ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul hmf hmf
        exact lt_irrefl n (lt_of_lt_of_le h3 (le_trans hpp hsq))
      exact (ArithmeticFunction.cardFactors_apply_prime hprime).symm
    rw [if_neg h3]
    by_cases h4 : n % p = 0
    · rw [if_pos h4]
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h4
      have hpp : p.Prime := by
        have hmf := hr p.minFac (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd p).trans hdvd)
        have hle := Nat.minFac_le (n := p) (by omega)
        have heq : p.minFac = p := le_antisymm hle hmf
        have hprime := Nat.minFac_prime (show p ≠ 1 by omega)
        rwa [heq] at hprime
      obtain ⟨q, hq⟩ := hdvd
      have hq0 : q ≠ 0 := by
        intro h
        rw [h, Nat.mul_zero] at hq
        omega
      have hdiv : n / p = q := by
        rw [hq]
        exact Nat.mul_div_cancel_left q (by omega)
      have h2q : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp
      rw [← hq] at h2q
      have hrec := ih q p hp (by omega) (by omega) (fun r hr1 hr2 => hr r hr1 (by
        rw [hq]
        exact Dvd.dvd.mul_left hr2 p))
      rw [hdiv, hrec, hq, ArithmeticFunction.cardFactors_mul (m := p) (by omega) hq0, ArithmeticFunction.cardFactors_apply_prime hpp]
      omega
    · rw [if_neg h4]
      refine ih n (p + 1) (by omega) hn (by omega) (fun r hr1 hr2 => ?_)
      have hge := hr r hr1 hr2
      by_contra hlt
      have hre : r = p := by omega
      rw [hre] at hr2
      exact h4 (Nat.mod_eq_zero_of_dvd hr2)

theorem bigOmega_eq (n : Nat) (hn : 1 ≤ n) : bigOmega n = ArithmeticFunction.cardFactors n :=
  omegaAux_eq (n + 1) n 2 le_rfl hn (by omega) (fun _ hr _ => hr.two_le)

/-- Omega is positive from 2 on -/
theorem cardFactors_pos (m : Nat) (hm : 2 ≤ m) : 0 < ArithmeticFunction.cardFactors m := by
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  obtain ⟨k, hk⟩ := Nat.minFac_dvd m
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hk
    omega
  have e := congrArg (⇑ArithmeticFunction.cardFactors) hk
  rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hk0, ArithmeticFunction.cardFactors_apply_prime hp] at e
  omega

end C2Walk
