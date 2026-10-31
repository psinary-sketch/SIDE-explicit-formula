/-
b729, (R339)(3): THE DIVISOR LOOP IS THE SUM OVER x y = n, x, y ≥ 2. `divSum` from d collects every ordered pair of cofactors at least d.
-/
import SIDEExplicitFormula.C2Spair
import Mathlib

namespace C2Walk

theorem divSum_succ (a : Nat → Int) (W : Tab) (n f d : Nat) (s : Int) :
    divSum a W n (f + 1) d s =
      if n < d * d then s
      else if n % d = 0 then
        divSum a W n f (d + 1)
          (if n / d = d then s + Tab.get W d * a d
           else s + Tab.get W d * a (n / d) + Tab.get W (n / d) * a d)
      else divSum a W n f (d + 1) s := by
  first
    | rfl
    | simp [divSum]
    | rw [divSum]

theorem Spair_empty {n d : Nat} (h : n < d * d) : Spair n d = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  obtain ⟨⟨hxy, _⟩, h1, h2⟩ := mem_Spair.mp hp
  have := Nat.mul_le_mul h1 h2
  omega

theorem Spair_skip {n d : Nat} (hd : 1 ≤ d) (hm : n % d ≠ 0) : Spair n d = Spair n (d + 1) := by
  ext p
  rw [mem_Spair, mem_Spair]
  constructor
  · rintro ⟨⟨hxy, hn⟩, h1, h2⟩
    refine ⟨⟨hxy, hn⟩, ?_, ?_⟩
    · by_contra hc
      have hx : p.1 = d := by omega
      apply hm
      apply Nat.mod_eq_zero_of_dvd
      rw [← hxy, hx]
      exact Dvd.intro _ rfl
    · by_contra hc
      have hy : p.2 = d := by omega
      apply hm
      apply Nat.mod_eq_zero_of_dvd
      rw [← hxy, hy]
      exact Dvd.intro_left _ rfl
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, by omega, by omega⟩

theorem Spair_square {n d : Nat} (hd : 1 ≤ d) (hn : n ≠ 0) (hdd : d * d = n) :
    Spair n d = insert (d, d) (Spair n (d + 1)) := by
  ext p
  rw [Finset.mem_insert, mem_Spair, mem_Spair]
  constructor
  · rintro ⟨⟨hxy, hn'⟩, h1, h2⟩
    by_cases hx : p.1 = d
    · left
      have hy : p.2 = d := by
        have h3 : d * p.2 = d * d := by rw [← hx, hxy, hx, hdd]
        exact Nat.eq_of_mul_eq_mul_left (by omega) h3
      exact Prod.ext hx hy
    · by_cases hy : p.2 = d
      · left
        have hx' : p.1 = d := by
          have h3 : d * p.1 = d * d := by rw [hdd, ← hxy, hy, Nat.mul_comm]
          exact Nat.eq_of_mul_eq_mul_left (by omega) h3
        exact absurd hx' hx
      · right
        exact ⟨⟨hxy, hn'⟩, by omega, by omega⟩
  · rintro (h | ⟨h, h1, h2⟩)
    · rw [h]
      exact ⟨⟨hdd, hn⟩, le_rfl, le_rfl⟩
    · exact ⟨h, by omega, by omega⟩

theorem Spair_pair {n d q : Nat} (hd : 1 ≤ d) (hn : n ≠ 0) (hdq : d * q = n) (hle : d ≤ q) :
    Spair n d = insert (d, q) (insert (q, d) (Spair n (d + 1))) := by
  ext p
  rw [Finset.mem_insert, Finset.mem_insert, mem_Spair, mem_Spair]
  constructor
  · rintro ⟨⟨hxy, hn'⟩, h1, h2⟩
    by_cases hx : p.1 = d
    · left
      have hy : p.2 = q := by
        have h3 : d * p.2 = d * q := by rw [hdq, ← hxy, hx]
        exact Nat.eq_of_mul_eq_mul_left (by omega) h3
      exact Prod.ext hx hy
    · by_cases hy : p.2 = d
      · right
        left
        have hx' : p.1 = q := by
          have h3 : d * p.1 = d * q := by rw [hdq, ← hxy, hy, Nat.mul_comm]
          exact Nat.eq_of_mul_eq_mul_left (by omega) h3
        exact Prod.ext hx' hy
      · right
        right
        exact ⟨⟨hxy, hn'⟩, by omega, by omega⟩
  · rintro (h | h | ⟨h, h1, h2⟩)
    · rw [h]
      exact ⟨⟨hdq, hn⟩, le_rfl, hle⟩
    · rw [h]
      exact ⟨⟨by rw [Nat.mul_comm]; exact hdq, hn⟩, hle, le_rfl⟩
    · exact ⟨h, by omega, by omega⟩

theorem divSum_eq (a : Nat → Int) (W : Tab) (n : Nat) (hn : n ≠ 0) :
    ∀ (f d : Nat) (s : Int), 1 ≤ d → n < (d + f) * (d + f) →
      divSum a W n f d s = s + ∑ p ∈ Spair n d, Tab.get W p.1 * a p.2 := by
  intro f
  induction f with
  | zero =>
    intro d s _ h
    have h0 : divSum a W n 0 d s = s := by
      first
        | rfl
        | simp [divSum]
    rw [h0, Spair_empty (by simpa using h), Finset.sum_empty, add_zero]
  | succ f ih =>
    intro d s hd h
    have hshift : d + (f + 1) = d + 1 + f := by omega
    rw [hshift] at h
    rw [divSum_succ]
    by_cases h1 : n < d * d
    · rw [if_pos h1, Spair_empty h1, Finset.sum_empty, add_zero]
    rw [if_neg h1]
    by_cases h2 : n % d = 0
    · rw [if_pos h2]
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      have hdq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      by_cases h3 : n / d = d
      · rw [if_pos h3, ih (d + 1) _ (by omega) h]
        have hdd : d * d = n := by
          rw [h3] at hdq
          exact hdq
        have hnot : (d, d) ∉ Spair n (d + 1) := by
          intro hm
          have := (mem_Spair.mp hm).2.2
          simp at this
        rw [Spair_square hd hn hdd, Finset.sum_insert hnot]
        first
          | ring
          | (dsimp only; ring)
      · rw [if_neg h3, ih (d + 1) _ (by omega) h]
        have hle : d ≤ n / d := by
          by_contra hc
          have hlt : n / d + 1 ≤ d := by omega
          have h4 : d * (n / d + 1) ≤ d * d := Nat.mul_le_mul_left d hlt
          rw [Nat.mul_add, hdq, Nat.mul_one] at h4
          have h5 : n < d * d := by omega
          exact h1 h5
        have hne : n / d ≠ d := h3
        have hnot2 : (n / d, d) ∉ Spair n (d + 1) := by
          intro hm
          have := (mem_Spair.mp hm).2.2
          simp at this
        have hnot1 : (d, n / d) ∉ insert (n / d, d) (Spair n (d + 1)) := by
          intro hm
          rcases Finset.mem_insert.mp hm with hm | hm
          · have := (Prod.ext_iff.mp hm).1
            exact hne this.symm
          · have := (mem_Spair.mp hm).2.1
            simp at this
        rw [Spair_pair hd hn hdq hle, Finset.sum_insert hnot1, Finset.sum_insert hnot2]
        first
          | ring
          | (dsimp only; ring)
    · rw [if_neg h2, ih (d + 1) s (by omega) h, Spair_skip hd h2]

theorem divSum_full (a : Nat → Int) (W : Tab) (n : Nat) (hn : n ≠ 0) :
    divSum a W n n 2 0 = ∑ p ∈ Spair n 2, Tab.get W p.1 * a p.2 := by
  have h : n < (2 + n) * (2 + n) := by nlinarith
  rw [divSum_eq a W n hn n 2 0 (by omega) h, zero_add]

end C2Walk
