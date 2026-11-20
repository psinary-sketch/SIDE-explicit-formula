import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Squares at 24

THIS PROGRAMME'S WORK (act b763, ruling (R373)(8), W-ORD-SQUARES-AT-24 under [A4], its home this kernel).

A prime above 3 has -1, 2 and 3 all squares modulo it exactly when it is 1 modulo 24. The three
laws are Mathlib's: the first supplementary law (`ZMod.exists_sq_eq_neg_one_iff`), the second
(`ZMod.exists_sq_eq_two_iff`), and quadratic reciprocity at 3 for a prime that is 1 modulo 4
(`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`). Nothing here is computed at a zero.
-/

namespace SIDEExplicitFormula
namespace SquaresAt24

/-- 2 is not a square modulo 3: the second supplementary law at 3, which is 3 modulo 8. -/
theorem not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by
  rw [ZMod.exists_sq_eq_two_iff (p := 3) (by norm_num)]
  norm_num

/-- Modulo a prime above 3 that is 1 modulo 4, 3 is a square exactly when the prime is 1 modulo 3. -/
theorem isSquare_three_iff {p : ℕ} [Fact p.Prime] (h3 : 3 < p) (h4 : p % 4 = 1) :
    IsSquare (3 : ZMod p) ↔ p % 3 = 1 := by
  have hrec : IsSquare (3 : ZMod p) ↔ IsSquare (p : ZMod 3) := by
    exact_mod_cast ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3) h4 (by norm_num)
  rw [hrec]
  have hp : p.Prime := Fact.out
  have h0 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have hcast := ZMod.natCast_mod p 3
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h
  · rw [h, Nat.cast_one] at hcast
    rw [← hcast]
    exact ⟨fun _ => h, fun _ => IsSquare.one⟩
  · rw [h] at hcast
    have hcast' : (2 : ZMod 3) = (p : ZMod 3) := by exact_mod_cast hcast
    rw [← hcast']
    exact ⟨fun hs => absurd hs not_isSquare_two_zmod_three, fun h' => (by omega : False).elim⟩

/-- A prime above 3 has -1, 2 and 3 all squares modulo it exactly when it is 1 modulo 24. -/
theorem squares_at_24 {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    (IsSquare (-1 : ZMod p) ∧ IsSquare (2 : ZMod p) ∧ IsSquare (3 : ZMod p)) ↔ p % 24 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  rw [ZMod.exists_sq_eq_neg_one_iff (p := p), ZMod.exists_sq_eq_two_iff (p := p) (by omega)]
  constructor
  · rintro ⟨h4, h8, hsq3⟩
    have h4' : p % 4 = 1 := by omega
    have h31 := (isSquare_three_iff h3 h4').mp hsq3
    omega
  · intro h24
    have h4' : p % 4 = 1 := by omega
    exact ⟨by omega, by omega, (isSquare_three_iff h3 h4').mpr (by omega)⟩

end SquaresAt24
end SIDEExplicitFormula
