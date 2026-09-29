/-
SIDE-explicit-formula -- SIDEExplicitFormula/GRHWeil.lean
THIS PROGRAMME'S WORK (act b562, ruling (R172)(4); W-ORD-GRH-WEIL, act one) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-SIDE OF THE WEIL ARC, in Mathlib's own terms, for a Dirichlet character `χ : DirichletCharacter ℂ N`, primitive,
`χ ≠ 1`: Mathlib's `DirichletCharacter.LFunction`, its completion and functional equation
(NumberTheory/LSeries/DirichletContinuation.lean at the kernel's Mathlib rev).

(a) THE STATEMENT LAYER. `GRH_chi χ`: every zero of `LFunction χ` in the open strip has real part 1/2. `GRH_chi_trivial χ`:
every zero off the trivial points `-(2m + a)` (`a` the parity) has real part 1/2. `h2_sign_chi χ`: the Weil form's sign on
`classK` with the χ-explicit formula's terms -- the prime term `Σ Λ(n) n^{-1/2} (χ(n) k(log n) + conj χ(n) k(-log n))` and the
Γ term `(1/2π) ∫ h(r) (log(N/π) + Re ψ(1/4 + a/2 + ir/2)) dr`, no pole term for `χ ≠ 1`; at `N = 1`, `a = 0` these are
H2Sign's own terms without the pole. `h2_sign_chi χ ↔ GRH_chi χ` is the arc's TARGET, stated and NOT proved here: it needs the
χ-explicit formula, which this act prices and does not build.

(b) THE SEAM: a zero of `LFunction χ` with real part `≤ 0` is a trivial point -- from the relation between the L-function and
its completion, the functional equation applied to `χ⁻¹` (primitive, by `conductor_inv`), the nonvanishing of `LFunction χ⁻¹`
on `re ≥ 1`, and the nonvanishing of `Gammaℝ` on `re > 0`; no root-number fact is consumed. Hence
`GRH_chi χ ↔ GRH_chi_trivial χ`.

(c) THE PAIRING: `LFunction χ⁻¹ (conj s) = conj (LFunction χ s)` -- by the Dirichlet series on `re > 1` and the identity
theorem on `ℂ` (the rev holds no conjugation lemma for `LFunction`) -- and the vanishing orders agree, by Zeta23's
`analyticOrderAt_conj_conj`.

Nothing here proves GRH, RH, h2_sign or h2_sign_chi.
-/
import SIDEExplicitFormula.LiWeil

open Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## (a) The statement layer -/

open scoped Classical in
/-- The parity of `χ`: `0` if `χ` is even, `1` otherwise -- the shift in Mathlib's `gammaFactor` (`Gammaℝ s` or
`Gammaℝ (s + 1)`). -/
def parity (χ : DirichletCharacter ℂ N) : ℕ := if χ.Even then 0 else 1

/-- The trivial points of `L(s, χ)`: `s = -(2m + a)`, `a` the parity. -/
def IsTrivialPoint (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop := ∃ m : ℕ, s = -((2 * m + parity χ : ℕ) : ℂ)

/-- **GRH for `χ`, the strip form:** every zero of Mathlib's `LFunction χ` with `0 < re s < 1` has `re s = 1/2`. -/
def GRH_chi (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- **GRH for `χ`, off the trivial points:** every zero of `LFunction χ` that is not a trivial point has `re s = 1/2`. -/
def GRH_chi_trivial (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → ¬ IsTrivialPoint χ s → s.re = 1 / 2

/-- The χ-explicit formula's prime term: `Σ Λ(n) n^{-1/2} (χ(n) k(log n) + conj χ(n) k(-log n))`. -/
def primeSum_chi (χ : DirichletCharacter ℂ N) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (χ (n : ZMod N) * k (Real.log n) + conj (χ (n : ZMod N)) * k (-Real.log n))

/-- The χ-explicit formula's Γ bracket: `log(N/π) + Re ψ(1/4 + a/2 + ir/2)`; at `N = 1`, `a = 0` it is `gammaBracket`. -/
def gammaBracket_chi (χ : DirichletCharacter ℂ N) (r : ℝ) : ℝ :=
  Real.log (N / Real.pi) + (Complex.digamma (1 / 4 + (parity χ : ℂ) / 2 + I * r / 2)).re

/-- The χ-explicit formula's Γ term: `(1/2π) ∫ h(r) gammaBracket_chi χ r dr`, `h = paperFT k`. -/
def archTerm_chi (χ : DirichletCharacter ℂ N) (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (gammaBracket_chi χ r : ℂ)

/-- **The Weil form's sign for `χ`, in H2Sign's form:** for every `k` in `classK`, `0 ≤ A_χ(k) - PR_χ(k)` (no pole term for
`χ ≠ 1`). STATED; its equivalence to `GRH_chi χ` is the arc's target and is not proved here. -/
def h2_sign_chi (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ k : ℝ → ℂ, B321.classK k → 0 ≤ archTerm_chi χ k - primeSum_chi χ k

/-! ## (b) The seam -/

/-- A nontrivial character has modulus other than `1`. -/
theorem ne_one_of_ne_one {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) : N ≠ 1 := fun h => h1 (level_one' χ h)

/-- The inverse of a primitive character is primitive (`conductor_inv`). -/
theorem isPrimitive_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]
  exact hχ

/-- `gammaFactor` does not vanish on `re s > 0`: it is `Gammaℝ s` or `Gammaℝ (s + 1)`. -/
theorem gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  unfold gammaFactor
  split_ifs
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

/-- Where `gammaFactor` vanishes, `s` is a trivial point: `Gammaℝ z = π^{-z/2} Γ(z/2)` vanishes only where `Γ(z/2)` does. -/
theorem trivialPoint_of_gammaFactor_eq_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (h : gammaFactor χ s = 0) :
    IsTrivialPoint χ s := by
  classical
  unfold gammaFactor at h
  unfold IsTrivialPoint parity
  split_ifs at h ⊢ with he
  · rw [Complex.Gammaℝ, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).mp h
      refine ⟨m, ?_⟩
      push_cast
      linear_combination 2 * hm
  · rw [Complex.Gammaℝ, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).mp h
      refine ⟨m, ?_⟩
      push_cast
      linear_combination 2 * hm

/-- **The seam for `L(s, χ)`:** a zero of `LFunction χ` with `re s ≤ 0` is a trivial point. From
`LFunction_eq_completed_div_gammaFactor`, the functional equation applied to the primitive `χ⁻¹`, the nonvanishing of
`LFunction χ⁻¹` on `re ≥ 1`, and `Gammaℝ_ne_zero_of_re_pos`; no root-number fact is consumed. -/
theorem LFunction_zero_re_nonpos {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) (hre : s.re ≤ 0) : IsTrivialPoint χ s := by
  have hN := ne_one_of_ne_one h1
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), div_eq_zero_iff] at hs
  rcases hs with hc | hg
  · exfalso
    have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
    have hFE := (isPrimitive_inv hχ).completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hFE
    have hre1 : (0 : ℝ) < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hG := gammaFactor_ne_zero_of_re_pos χ⁻¹ hre1
    have hL := LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN)
    rw [hFE, zero_div] at hL
    exact LFunction_ne_zero_of_one_le_re (χ := χ⁻¹) (Or.inl hinv1)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) hL
  · exact trivialPoint_of_gammaFactor_eq_zero χ hg

/-- A trivial point has real part `≤ 0`. -/
theorem re_nonpos_of_trivialPoint {χ : DirichletCharacter ℂ N} {s : ℂ} (h : IsTrivialPoint χ s) : s.re ≤ 0 := by
  obtain ⟨m, rfl⟩ := h
  simp only [Complex.neg_re, Complex.natCast_re]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

/-- **The strip form and the form off the trivial points coincide**, for a primitive `χ ≠ 1`: the seam and the
nonvanishing of `LFunction χ` on `re ≥ 1`. -/
theorem GRH_chi_iff_trivial {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    GRH_chi χ ↔ GRH_chi_trivial χ := by
  constructor
  · intro h s hs hnt
    by_cases h0 : s.re ≤ 0
    · exact absurd (LFunction_zero_re_nonpos hχ h1 hs h0) hnt
    by_cases h2 : 1 ≤ s.re
    · exact absurd hs (LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl h1) h2)
    exact h s hs (not_le.mp h0) (not_le.mp h2)
  · intro h s hs h0 _
    exact h s hs (fun ht => absurd (re_nonpos_of_trivialPoint ht) (not_le.mpr h0))

/-! ## (c) The pairing across (χ, χ⁻¹) -/

/-- On `re s > 1`, by the Dirichlet series: `conj (L(conj s, χ)) = L(s, χ⁻¹)`, since `conj (χ n) = χ⁻¹ n`
(`MulChar.star_apply'`) and `conj (n ^ conj s) = n ^ s`. -/
theorem LFunction_conj_of_one_lt_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    conj (LFunction χ (conj s)) = LFunction χ⁻¹ s := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [LFunction_eq_LSeries χ hs', LFunction_eq_LSeries χ⁻¹ hs]
  unfold LSeries
  show star (∑' n : ℕ, LSeries.term (fun n : ℕ => χ (n : ZMod N)) (conj s) n) = _
  rw [tsum_star]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Ne.symm Real.pi_ne_zero
    have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
      have h := Complex.cpow_conj (n : ℂ) s harg
      rwa [Complex.conj_natCast] at h
    rw [star_div₀, hpow, MulChar.star_apply']
    congr 1
    exact Complex.conj_conj _

/-- **The pairing:** `LFunction χ⁻¹ (conj s) = conj (LFunction χ s)` for every `s`, `χ ≠ 1` -- the series agreement on
`re > 1` carried to `ℂ` by the identity theorem (both sides entire, `differentiable_LFunction`). -/
theorem LFunction_inv_conj {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    LFunction χ⁻¹ (conj s) = conj (LFunction χ s) := by
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have hf1 : AnalyticOnNhd ℂ (LFunction χ⁻¹) Set.univ :=
    (differentiable_LFunction hinv1).differentiableOn.analyticOnNhd isOpen_univ
  have hf2 : AnalyticOnNhd ℂ (fun z => conj (LFunction χ (conj z))) Set.univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ (LFunction χ) (conj z) := differentiable_LFunction h1 _
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : (fun z => conj (LFunction χ (conj z))) =ᶠ[nhds (2 : ℂ)] LFunction χ⁻¹ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact LFunction_conj_of_one_lt_re χ hz
  have heq := hf2.eqOn_of_preconnected_of_eventuallyEq hf1 isPreconnected_univ (Set.mem_univ 2) hagree
  have h3 := heq (Set.mem_univ (conj s))
  simp only [Complex.conj_conj] at h3
  exact h3.symm

/-- The zeros are carried by conjugation: `LFunction χ s = 0 ↔ LFunction χ⁻¹ (conj s) = 0`. -/
theorem LFunction_zero_iff_conj {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s : ℂ) :
    LFunction χ s = 0 ↔ LFunction χ⁻¹ (conj s) = 0 := by
  rw [LFunction_inv_conj h1, map_eq_zero]

/-- **The multiplicities agree across the pair:** the vanishing order of `LFunction χ⁻¹` at `conj w` is that of
`LFunction χ` at `w`, by Zeta23's `analyticOrderAt_conj_conj`. -/
theorem analyticOrderAt_LFunction_inv_conj {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (w : ℂ) :
    analyticOrderAt (LFunction χ⁻¹) (conj w) = analyticOrderAt (LFunction χ) w := by
  have e : LFunction χ⁻¹ = fun z => conj (LFunction χ (conj z)) := by
    funext z
    have h := LFunction_inv_conj h1 (conj z)
    rwa [Complex.conj_conj] at h
  rw [e]
  exact Zeta23.analyticOrderAt_conj_conj _ w

end GRHWeil
end SIDEExplicitFormula
