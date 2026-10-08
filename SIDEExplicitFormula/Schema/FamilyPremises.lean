/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/FamilyPremises.lean
THIS PROGRAMME'S WORK (act b642, ruling (R252)(3)(c); the computations of b641, relay data/b641_premise_status.txt, D1-D2) -- NOT
VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE DEDEKIND READING'S TWO PREMISES (Family.lean (d), v0.21), READ IN THE KERNEL:

* `not_trivialSummandPremise : ¬ TrivialSummandPremise`. At the box of half-width 1/2 (real, nonnegative, supported in `(-log 2, log 2)`)
  both prime sums vanish -- the von Mangoldt function is nonzero only at `n ≥ 2`, where `log n > 1/2` -- and the Γ terms agree
  (`archTerm_chi_one`: the trivial character mod 1 is even and its Γ bracket is `gammaBracket`), so the premise would need the pole term to
  vanish; it is `8 sinh(1/4) > 0` (`poleTerm_box_half`, from `PlateauRamp.box_paperFT`). The premise is false.
* `eulerFactorPremise_of_primitive`: where every non-trivial character mod `q` is primitive, each is read at the same character and the
  same level on both sides (`primitiveCharacter_apply_nat`, the parity and the conductor carried), so the premise holds;
  `eulerFactorPremise_three` at `q = 3`, the modulus of `dedekind_three`.
* `not_eulerFactorPremise_six : ¬ EulerFactorPremise 6`: the odd character mod 6 induced from a non-trivial character mod 3. At the point
  mass at `log 2` the transform vanishes almost everywhere, so both Γ terms are 0; the prime terms differ at `n = 2`, where the character
  mod 6 is 0 and its primitive inducer is not. b641 computed the failure through the Γ terms at a smooth window, `log 2 · k(0)`; the
  compiled witness is the prime terms at a point mass, the premise quantifying every `k : ℝ → ℂ`.

Nothing here proves RH or GRH, identifies a sum with a Dedekind zeta function, or locates any zero.
-/
import SIDEExplicitFormula.Schema.Family
import SIDEExplicitFormula.Schema.PlateauRamp
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Family

open B321 GRHWeil DirichletCharacter

/-- The trivial character mod 1 is even. -/
theorem parity_one : parity (1 : DirichletCharacter ℂ 1) = 0 := by
  have h : (1 : DirichletCharacter ℂ 1).Even := by
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  unfold parity
  exact if_pos h

/-- The trivial character mod 1 takes the value 1 at every natural number. -/
theorem one_apply_nat (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

/-- **The Γ term of the trivial character mod 1 is b321's archimedean term.** -/
theorem archTerm_chi_one (k : ℝ → ℂ) : archTerm_chi (1 : DirichletCharacter ℂ 1) k = archTerm k := by
  have hG : ∀ r, gammaBracket_chi (1 : DirichletCharacter ℂ 1) r = Zeta23.EF.gammaBracket r := by
    intro r
    unfold gammaBracket_chi Zeta23.EF.gammaBracket
    rw [parity_one]
    simp only [Nat.cast_one, Nat.cast_zero, zero_div, add_zero, one_div, Real.log_inv]
    ring
  unfold archTerm_chi archTerm
  simp only [hG]

/-- `log n > 1/2` for `n ≥ 2`. -/
theorem log_nat_gt_half {n : ℕ} (hn : 2 ≤ n) : (1 / 2 : ℝ) < Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have := Real.log_two_gt_d9
  linarith

/-- The pole term at the box of half-width 1/2: `8 sinh(1/4)`, positive. -/
theorem poleTerm_box_half : poleTerm (B321.phiC (PlateauRamp.box (1 / 2))) = 8 * (Real.sinh (1 / 4) : ℂ) := by
  unfold poleTerm
  have h1 := PlateauRamp.box_paperFT (a := 1 / 2) (by norm_num) (z := I / 2) (by simp)
  have h2 := PlateauRamp.box_paperFT (a := 1 / 2) (by norm_num) (z := -I / 2) (by simp)
  rw [h1, h2]
  have s1 : Complex.sin (I / 2 * ((1 / 2 : ℝ) : ℂ)) = (Real.sinh (1 / 4) : ℂ) * I := by
    rw [show I / 2 * ((1 / 2 : ℝ) : ℂ) = ((1 / 4 : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have s2 : Complex.sin (-I / 2 * ((1 / 2 : ℝ) : ℂ)) = -((Real.sinh (1 / 4) : ℂ) * I) := by
    rw [show -I / 2 * ((1 / 2 : ℝ) : ℂ) = -(((1 / 4 : ℝ) : ℂ) * I) by push_cast; ring, Complex.sin_neg, Complex.sin_mul_I,
      ← Complex.ofReal_sinh]
  rw [s1, s2]
  field_simp
  ring_nf

/-- **TrivialSummandPremise IS FALSE** (b641's computation, compiled at b642): at the box of half-width 1/2 -- real, nonnegative,
supported in `(-log 2, log 2)` -- both prime sums vanish and the Γ terms agree, so the premise would need the pole term to vanish,
while it is `8 sinh(1/4) > 0`. -/
theorem not_trivialSummandPremise : ¬ TrivialSummandPremise := by
  intro h
  set k := B321.phiC (PlateauRamp.box (1 / 2)) with hk
  have hvan : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n = 0) ∨ (k (Real.log n) = 0 ∧ k (-Real.log n) = 0) := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · left
      interval_cases n <;> simp
    · right
      have hl := log_nat_gt_half hn
      constructor
      · simp only [hk, B321.phiC, PlateauRamp.box]
        rw [Set.indicator_of_notMem (fun hm => by linarith [hm.2])] <;> simp
      · simp only [hk, B321.phiC, PlateauRamp.box]
        rw [Set.indicator_of_notMem (fun hm => by linarith [hm.1])] <;> simp
  have hP : primeSum k = 0 := by
    unfold primeSum
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases hvan n with h0 | ⟨h1, _⟩
    · simp [h0]
    · simp [h1]
  have hPc : primeSum_chi (1 : DirichletCharacter ℂ 1) k = 0 := by
    unfold primeSum_chi
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases hvan n with h0 | ⟨h1, h2⟩
    · simp [h0]
    · simp [h1, h2]
  have := h k
  rw [zeta_rhs_pole, hP, hPc, archTerm_chi_one, poleTerm_box_half] at this
  have hs : 0 < Real.sinh (1 / 4) := by
    rw [Real.sinh_eq]
    have := Real.exp_lt_exp.mpr (show -(1 / 4 : ℝ) < 1 / 4 by norm_num)
    linarith
  have : (8 * Real.sinh (1 / 4) : ℝ) = 0 := by
    have h' : (8 : ℂ) * (Real.sinh (1 / 4) : ℂ) = 0 := by linear_combination this
    exact_mod_cast h'
  linarith

/-- The values of a primitive character's inducer agree with the character's at every natural number. -/
theorem primitiveCharacter_apply_nat {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ℕ) :
    χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
  have hc : χ.conductor = q := hχ
  by_cases hco : IsCoprime (n : ℤ) (q : ℤ)
  · have := χ.primitiveCharacter_apply_of_isCoprime hco
    simpa using this
  · have h1 : χ (((n : ℤ)) : ZMod q) = 0 := (apply_eq_zero_iff ..).mpr hco
    have h2 : χ.primitiveCharacter (((n : ℤ)) : ZMod χ.conductor) = 0 := (apply_eq_zero_iff ..).mpr (by rw [hc]; exact hco)
    simp only [Int.cast_natCast] at h1 h2
    rw [h1, h2]

/-- **THE EULER-FACTOR PREMISE WHERE EVERY NON-TRIVIAL CHARACTER IS PRIMITIVE**: both sides then read the same character at the
same level. -/
theorem eulerFactorPremise_of_primitive (q : ℕ) [NeZero q] (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ.IsPrimitive) :
    EulerFactorPremise q := by
  intro χ hχ k
  have hp := h χ hχ
  have hc : χ.conductor = q := hp
  have hv := primitiveCharacter_apply_nat χ hp
  have hneg : χ.primitiveCharacter (-1) = χ (-1) := by
    have := χ.primitiveCharacter_apply_of_isCoprime (a := -1) isCoprime_one_left.neg_left
    simpa using this
  have hpar : parity χ.primitiveCharacter = parity χ := by
    have he : χ.primitiveCharacter.Even ↔ χ.Even := by
      unfold DirichletCharacter.Even
      rw [hneg]
    unfold parity
    by_cases h1 : χ.Even
    · rw [if_pos (he.mpr h1), if_pos h1]
    · rw [if_neg (fun h' => h1 (he.mp h')), if_neg h1]
  have hG : ∀ r, gammaBracket_chi χ.primitiveCharacter r = gammaBracket_chi χ r := by
    intro r
    unfold gammaBracket_chi
    rw [hpar, show ((χ.conductor : ℕ) : ℝ) = (q : ℝ) by exact_mod_cast hc]
  have hA : archTerm_chi χ.primitiveCharacter k = archTerm_chi χ k := by
    unfold archTerm_chi
    simp only [hG]
  have hP : primeSum_chi χ.primitiveCharacter k = primeSum_chi χ k := by
    unfold primeSum_chi
    simp only [hv]
  rw [hA, hP]

/-- Every non-trivial character mod 3 is primitive. -/
theorem primitive_of_ne_one_three (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have hd : χ.conductor ∣ 3 := χ.conductor_dvd_level
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hd) with h1 | h3
  · exact absurd (χ.eq_one_iff_conductor_eq_one.mpr h1) hχ
  · exact h3

/-- **THE EULER-FACTOR PREMISE AT q = 3**, the modulus of `dedekind_three`. -/
theorem eulerFactorPremise_three : EulerFactorPremise 3 :=
  eulerFactorPremise_of_primitive 3 primitive_of_ne_one_three

/-- The point mass at `log 2`, the test function of the refutation at the modulus 6. -/
def pointLog2 (x : ℝ) : ℂ := if x = Real.log 2 then 1 else 0

theorem paperFT_pointLog2 (z : ℂ) : Zeta23.paperFT pointLog2 z = 0 := by
  unfold Zeta23.paperFT
  apply integral_eq_zero_of_ae
  have h0 : (volume : Measure ℝ) {Real.log 2} = 0 := measure_singleton _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
  have : x ≠ Real.log 2 := hx
  simp [pointLog2, this]

theorem archTerm_chi_pointLog2 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : archTerm_chi χ pointLog2 = 0 := by
  unfold archTerm_chi
  simp [paperFT_pointLog2]

theorem log_nat_eq_log_two {n : ℕ} (h : Real.log n = Real.log 2) : n = 2 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp at h; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  · exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hpos)) (Set.mem_Ioi.mpr (by norm_num)) h

theorem neg_log_nat_ne_log_two (n : ℕ) : -Real.log n ≠ Real.log 2 := by
  have h1 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  intro h; linarith

/-- **THE EULER-FACTOR PREMISE FAILS AT q = 6**: the odd character mod 6 induced from a non-trivial character mod 3. At the point mass
at `log 2` the transform vanishes almost everywhere, so both Γ terms are 0; the prime terms differ at `n = 2`, where the character mod 6
is 0 (2 is not a unit mod 6) and its primitive inducer takes the non-zero value of the character mod 3. (b641 computed the failure
through the Γ terms at a smooth window; the compiled witness is the prime terms at a point mass.) -/
theorem not_eulerFactorPremise_six : ¬ EulerFactorPremise 6 := by
  intro h
  obtain ⟨ψ, hψ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity (R := ℂ) (n := 3)
    (a := (2 : ZMod 3)) (by decide)
  have hd : (3 : ℕ) ∣ 6 := by norm_num
  set χ := changeLevel hd ψ with hχdef
  have hψ1 : ψ ≠ 1 := by
    intro h1; apply hψ; rw [h1]; exact MulChar.one_apply (by decide)
  have hχ1 : χ ≠ 1 := fun h1 => hψ1 ((changeLevel_eq_one_iff hd).mp h1)
  have hψ2 : ψ 2 ≠ 0 := by
    intro h0
    have hm : ψ (2 * 2) = ψ 2 * ψ 2 := map_mul ψ 2 2
    rw [show (2 : ZMod 3) * 2 = 1 by decide, map_one, h0, zero_mul] at hm
    exact one_ne_zero hm
  have hχ2 : χ (2 : ZMod 6) = 0 := by
    apply MulChar.map_nonunit
    rw [show (2 : ZMod 6) = ((2 : ℕ) : ZMod 6) by rfl, ZMod.isUnit_iff_coprime]
    norm_num
  have hp2 : χ.primitiveCharacter (2 : ZMod χ.conductor) = ψ 2 := by
    have a1 := primitiveCharacter_changeLevel_apply hd ψ 2
    have a2 := ψ.primitiveCharacter_apply_of_isCoprime (a := 2) (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    simp only [Int.cast_ofNat] at a1 a2
    rw [a1, a2]
  have nl2 : ¬(-Real.log 2 = Real.log 2) := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); intro h'; linarith
  have hP6 : primeSum_chi χ pointLog2 = 0 := by
    unfold primeSum_chi
    refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases hn : n = 2
    · subst hn
      have : pointLog2 (-Real.log ((2 : ℕ) : ℝ)) = 0 := by simp [pointLog2, nl2]
      simp [this, hχ2]
    · have hne : Real.log n ≠ Real.log 2 := fun h' => hn (log_nat_eq_log_two h')
      have a : pointLog2 (Real.log n) = 0 := by simp [pointLog2, hne]
      have b : pointLog2 (-Real.log n) = 0 := by simp [pointLog2, neg_log_nat_ne_log_two n]
      simp [a, b]
  have hP3 : primeSum_chi χ.primitiveCharacter pointLog2 =
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) * ψ 2 := by
    unfold primeSum_chi
    rw [tsum_eq_single 2]
    · have a : pointLog2 (Real.log ((2 : ℕ) : ℝ)) = 1 := by simp [pointLog2]
      have b : pointLog2 (-Real.log ((2 : ℕ) : ℝ)) = 0 := by simp [pointLog2, nl2]
      rw [a, b]
      push_cast
      rw [hp2]
      ring
    · intro n hn
      have hne : Real.log n ≠ Real.log 2 := fun h' => hn (log_nat_eq_log_two h')
      have a : pointLog2 (Real.log n) = 0 := by simp [pointLog2, hne]
      have b : pointLog2 (-Real.log n) = 0 := by simp [pointLog2, neg_log_nat_ne_log_two n]
      simp [a, b]
  have := h χ hχ1 pointLog2
  rw [archTerm_chi_pointLog2, archTerm_chi_pointLog2, hP6, hP3] at this
  have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [hΛ]; exact_mod_cast (div_pos hl hs).ne'
  have : ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) * ψ 2 = 0 := by linear_combination this
  exact (mul_ne_zero hc hψ2) this

end Family
end Schema
end SIDEExplicitFormula
