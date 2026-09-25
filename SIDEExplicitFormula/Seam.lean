/-
SIDE-explicit-formula -- SIDEExplicitFormula/Seam.lean
THIS PROGRAMME'S WORK (act b536, ruling (R146)(1)-(2)) -- NOT VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full:
`theorem`, never `lemma`.

THE SEAM, FROM MATHLIB'S FUNCTIONAL EQUATION. A zero of zeta with real part at most 0 is a trivial zero
(`zeta_zero_re_nonpos`): for s = 1 - z, Mathlib's `riemannZeta_one_sub` writes zeta(z) as
2 (2 pi)^(-s) Gamma(s) cos(pi s / 2) zeta(s); for Re s >= 1 every factor but the cosine is nonzero
(`Complex.cpow_ne_zero_iff`, `Complex.Gamma_ne_zero`, `riemannZeta_ne_zero_of_one_le_re`), so cos(pi s / 2) = 0,
s is an odd integer (`Complex.cos_eq_zero_iff`) and z = 1 - s an even integer at most 0, not 0 (`riemannZeta_zero`).
With it the seam `rh_strip_imp_rh` of PowerWindow.lean holds, RHChain's `h2_sign_imp_rh` and H2Bridge's `h2_sign_imp_ch`
are inhabited, and `h2_sign ↔ RiemannHypothesis` and `conservationHypothesis ↔ h2_sign` hold with no hypothesis.
Nothing here proves RH or h2_sign: these are equivalences between open statements.
-/
import SIDEExplicitFormula.PowerLimit

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **The seam's classical fact:** a zero of zeta with real part at most 0 is a trivial zero. -/
theorem zeta_zero_re_nonpos : ∀ z : ℂ, riemannZeta z = 0 → z.re ≤ 0 → ∃ n : ℕ, z = -2 * (n + 1) := by
  intro z hz hre
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  set s : ℂ := 1 - z with hsdef
  have h1s : 1 - s = z := by
    rw [hsdef]
    ring
  have hsre : 1 ≤ s.re := by
    rw [hsdef, Complex.sub_re, Complex.one_re]
    linarith
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n h
    have h2 := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at h2
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    apply hz0
    rw [← h1s, h, sub_self]
  have key := riemannZeta_one_sub hsn hs1
  rw [h1s, hz] at key
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero hpi))
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsn
  have hZ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
  have hc : Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hA) hG) hc) hZ key.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  have hs_eq : s = 2 * (k : ℂ) + 1 := by
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by linear_combination 2 * hk
    exact mul_left_cancel₀ hpi h2
  have hzk : z = -2 * (k : ℂ) := by
    rw [← h1s, hs_eq]
    ring
  have hzre : z.re = -2 * (k : ℝ) := by
    rw [hzk]
    simp
  have hk0 : (0 : ℤ) ≤ k := by
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hkne : k ≠ 0 := by
    rintro rfl
    apply hz0
    rw [hzk]
    simp
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k - 1 by omega)
  refine ⟨n, ?_⟩
  have hkn : (k : ℂ) = (n : ℂ) + 1 := by
    have hk1 : k = (n : ℤ) + 1 := by omega
    rw [hk1]
    simp
  rw [hzk, hkn]

/-- **The seam, closed:** RH on the kernel's configuration is Mathlib's RiemannHypothesis. -/
theorem rh_strip_imp_rh_holds : rh_strip_imp_rh := by
  intro hstrip s hz hnt _h1
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h)
  · rcases le_or_gt s.re 0 with h' | h'
    · exact absurd (zeta_zero_re_nonpos s hz h') hnt
    · have hmem : s ∈ Zeta23.zetaZeroConfig.carrier := by
        rw [Zeta23.zetaZeroConfig_carrier]
        show Zeta23.IsNontrivialZero s
        unfold Zeta23.IsNontrivialZero
        exact ⟨hz, h', h⟩
      exact hstrip s hmem

/-- RHChain.lean:83's Prop, inhabited. -/
theorem h2_sign_imp_rh_holds : h2_sign_imp_rh := h2_sign_imp_rh_of_seam rh_strip_imp_rh_holds

/-- **Weil positivity on classK is Mathlib's RiemannHypothesis**, both directions, no hypothesis. -/
theorem h2_sign_iff_rh : h2_sign ↔ RiemannHypothesis := ⟨h2_sign_imp_rh_holds, rh_imp_h2_sign⟩

/-- H2Bridge.lean:88's Prop, inhabited. -/
theorem h2_sign_imp_ch_holds : h2_sign_imp_ch := h2_sign_imp_ch_iff.mpr h2_sign_imp_rh_holds

/-- The deposit's Route 3 premise and Weil positivity on classK, equivalent, unconditionally. -/
theorem ch_iff_h2_sign : conservationHypothesis ↔ h2_sign := ch_iff_h2_sign_of_seam rh_strip_imp_rh_holds

end B321
end SIDEExplicitFormula
