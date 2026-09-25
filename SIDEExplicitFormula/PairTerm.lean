/-
SIDE-explicit-formula -- SIDEExplicitFormula/PairTerm.lean
THIS PROGRAMME'S WORK (act b529, ruling (R139)(3); W-ORD-WEIL-CONVERSE's (f)(ii), the fold's (f2)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(f)(ii), THE PAIR'S TERM, AS FAR AS IT DERIVES. The window of b524 (`TwoPropertyWindow.lean`) at `gamma_0`, for a real
`phi`, `C^4` with compact support; `rho_0 = 1/2 + delta + i gamma_0`; the pair's term is `term(rho_0) + term(1 - conj rho_0)`
with `term(rho) = paperFT k (gammaOf rho)`, each of multiplicity one (`pairTwo`).

COMPONENT 1, THE EXACT ALGEBRA (`pairTwo_factored`, any `phi`): through b524's factorisation and the kernel's
`paperFT (weilTest h h) z = h^(z) conj(h^(conj z))` (for real `h`, `= h^(z) h^(-z)`), the pair's term is
`(delta^2 + 2 i gamma_0 delta)^2 C(gamma_0 - i delta) C(-gamma_0 + i delta)
 + (delta^2 - 2 i gamma_0 delta)^2 C(gamma_0 + i delta) C(-gamma_0 - i delta)`, `C` the transform of `cos(gamma_0 .) phi`.
For EVEN `phi` (`pairTwo_near_far`): each of the four values is `(N + F)/2` or `(N + conj F)/2`, the NEAR factor
`N = INT phi(u) cosh(delta u) du` (`nearInt`, times the constant 1/2) and the FAR factor `F = phi^(2 gamma_0 - i delta)`
(`farFT`). Evenness is a hypothesis the ferry's identification needs and b524's (i)-(iii) did not: for a non-even `phi`
the near factor is `INT phi e^{delta u}` on one side and `INT phi e^{-delta u}` on the other.

COMPONENT 2, THE NEAR FACTOR (`nearInt_ge`, `realizedGrowth_eq`, `realizedGrowth_ge_one`, `nearPair_eq`, `pair_near_sign`):
from `phi >= 0`, `INT phi cosh(delta u) >= INT phi > 0`; b524's `realizedGrowth phi delta` IS that ratio (by `rfl`); the
near-factor product at the pair (`nearPair`, the pair's term with `F = 0`) equals `N^2 delta^2 (delta^2 - 4 gamma_0^2) / 2`,
negative for `0 < delta < 2 gamma_0`.

COMPONENT 3, THE FAR FACTOR AS A NAMED HYPOTHESIS, NOT PROVED (`farSmall`, `pair_bound`): `farSmall gamma_0 phi delta eps`
is `|F| <= eps N` (equivalently `|F/2| <= eps (N/2)`, the far factor against the near factor). Under it at `delta` AND at
`0` (the slope `-2 gamma_0 C(gamma_0)` carries the far factor at `delta = 0`, `phi^(2 gamma_0)`), the pair's term is at most
`-(c - eps') delta^2 |slope|^2 G^2`, `c = pairConst = 2` (two terms; b524's `fConst = 4` counts the four images of a zero
of a conjugation-symmetric configuration, twice this pair), `eps' = pairEps eps delta gamma_0` printed from its definition.
Nothing here is a statement about the zeros of zeta or about RH.
-/
import SIDEExplicitFormula.TwoPropertyWindow

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The objects -/

/-- `phi` as a complex-valued function. -/
def phiC (φ : ℝ → ℝ) : ℝ → ℂ := fun u => (φ u : ℂ)

/-- **The near factor's integral** `INT phi(u) cosh(delta u) du`. -/
def nearInt (φ : ℝ → ℝ) (δ : ℝ) : ℝ := ∫ u, φ u * Real.cosh (δ * u)

/-- **The far factor**: the base bump's transform at `2 gamma_0 - i delta`. -/
def farFT (γ₀ : ℝ) (φ : ℝ → ℝ) (δ : ℝ) : ℂ := Zeta23.paperFT (phiC φ) (2 * (γ₀ : ℂ) - I * (δ : ℂ))

/-- `rho_0 = 1/2 + delta + i gamma_0`. -/
def rhoZero (γ₀ δ : ℝ) : ℂ := 1 / 2 + (δ : ℂ) + (γ₀ : ℂ) * I

/-- **The pair's term**: `term(rho_0) + term(1 - conj rho_0)`, each of multiplicity one. -/
def pairTwo (γ₀ : ℝ) (φ : ℝ → ℝ) (δ : ℝ) : ℂ :=
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf (rhoZero γ₀ δ)) +
  Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf (Zeta23.reflect (rhoZero γ₀ δ)))

/-! ### The images and the transform of `k` -/

theorem gammaOf_rhoZero (γ₀ δ : ℝ) : Zeta23.gammaOf (rhoZero γ₀ δ) = (γ₀ : ℂ) - I * δ := by
  unfold Zeta23.gammaOf rhoZero
  rw [div_eq_iff Complex.I_ne_zero]
  linear_combination (δ : ℂ) * Complex.I_sq

theorem gammaOf_reflect_rhoZero (γ₀ δ : ℝ) :
    Zeta23.gammaOf (Zeta23.reflect (rhoZero γ₀ δ)) = (γ₀ : ℂ) + I * δ := by
  have hc : (starRingEnd ℂ) (rhoZero γ₀ δ) = 1 / 2 + (δ : ℂ) - (γ₀ : ℂ) * I := by
    unfold rhoZero
    first
    | (simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; ring)
    | (simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring)
    | simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  unfold Zeta23.gammaOf Zeta23.reflect
  rw [hc, div_eq_iff Complex.I_ne_zero]
  linear_combination (-(δ : ℂ)) * Complex.I_sq

/-- For a real `f`: `conj (f^(z)) = f^(-conj z)`. -/
theorem paperFT_ofReal_conj (f : ℝ → ℝ) (z : ℂ) :
    conj (Zeta23.paperFT (phiC f) z) = Zeta23.paperFT (phiC f) (-conj z) := by
  simp only [Zeta23.paperFT, phiC]
  rw [← integral_conj]
  congr 1
  ext u
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  ring_nf

/-- `k^(z) = h^(z) h^(-z)` for the real window `h`. -/
theorem kWin_FT (γ₀ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ) (z : ℂ) :
    Zeta23.paperFT (kWin γ₀ φ) z = Zeta23.paperFT (windowC γ₀ φ) z * Zeta23.paperFT (windowC γ₀ φ) (-z) := by
  have hc : Continuous (windowC γ₀ φ) := (windowC_contDiff hφ).continuous
  have hs : HasCompactSupport (windowC γ₀ φ) := windowC_hasCompactSupport hφs
  unfold kWin
  rw [Zeta23.EF.paperFT_weilTest hc hc hs hs z]
  congr 1
  have h := paperFT_ofReal_conj (window γ₀ φ) (conj z)
  rw [Complex.conj_conj] at h
  exact h

/-! ### Component 1 -- the exact algebra -/

/-- **COMPONENT 1: the pair's term, exactly,** through the factorisation of b524, for any real `C^4` compactly supported
`phi`: an explicit expression in `delta`, `gamma_0` and the four values of the cosine window's transform. -/
theorem pairTwo_factored (γ₀ δ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ) :
    pairTwo γ₀ φ δ =
      ((δ : ℂ) ^ 2 + 2 * I * γ₀ * δ) ^ 2 *
          (Zeta23.paperFT (cosWinC γ₀ φ) ((γ₀ : ℂ) - I * δ) * Zeta23.paperFT (cosWinC γ₀ φ) (-(γ₀ : ℂ) + I * δ)) +
      ((δ : ℂ) ^ 2 - 2 * I * γ₀ * δ) ^ 2 *
          (Zeta23.paperFT (cosWinC γ₀ φ) ((γ₀ : ℂ) + I * δ) * Zeta23.paperFT (cosWinC γ₀ φ) (-(γ₀ : ℂ) - I * δ)) := by
  have f1 : (γ₀ : ℂ) ^ 2 - ((γ₀ : ℂ) - I * δ) ^ 2 = (δ : ℂ) ^ 2 + 2 * I * γ₀ * δ := by
    linear_combination (-(δ : ℂ) ^ 2) * Complex.I_sq
  have f2 : (γ₀ : ℂ) ^ 2 - (-(γ₀ : ℂ) + I * δ) ^ 2 = (δ : ℂ) ^ 2 + 2 * I * γ₀ * δ := by
    linear_combination (-(δ : ℂ) ^ 2) * Complex.I_sq
  have f3 : (γ₀ : ℂ) ^ 2 - ((γ₀ : ℂ) + I * δ) ^ 2 = (δ : ℂ) ^ 2 - 2 * I * γ₀ * δ := by
    linear_combination (-(δ : ℂ) ^ 2) * Complex.I_sq
  have f4 : (γ₀ : ℂ) ^ 2 - (-(γ₀ : ℂ) - I * δ) ^ 2 = (δ : ℂ) ^ 2 - 2 * I * γ₀ * δ := by
    linear_combination (-(δ : ℂ) ^ 2) * Complex.I_sq
  have n1 : -((γ₀ : ℂ) - I * δ) = -(γ₀ : ℂ) + I * δ := by ring
  have n2 : -((γ₀ : ℂ) + I * δ) = -(γ₀ : ℂ) - I * δ := by ring
  unfold pairTwo
  rw [gammaOf_rhoZero, gammaOf_reflect_rhoZero, kWin_FT γ₀ hφ hφs, kWin_FT γ₀ hφ hφs, n1, n2,
    paperFT_window γ₀ hφ hφs ((γ₀ : ℂ) - I * δ), paperFT_window γ₀ hφ hφs (-(γ₀ : ℂ) + I * δ),
    paperFT_window γ₀ hφ hφs ((γ₀ : ℂ) + I * δ), paperFT_window γ₀ hφ hφs (-(γ₀ : ℂ) - I * δ), f1, f2, f3, f4]
  ring

/-! ### The base bump's transform: near and far -/

theorem phiC_exp_integrable {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (z : ℂ) :
    Integrable (fun u : ℝ => (φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) := by
  have hφc : Continuous (fun t => (φ t : ℂ)) := Complex.continuous_ofReal.comp hc
  have hE : Continuous (fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))) := by fun_prop
  exact (hφc.mul hE).integrable_of_hasCompactSupport
    ((hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_right
      (f' := fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ))))

/-- The cosine window's transform is the average of two shifted transforms of `phi`. -/
theorem cosWinC_FT (γ₀ : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (z : ℂ) :
    Zeta23.paperFT (cosWinC γ₀ φ) z =
      (Zeta23.paperFT (phiC φ) (z + γ₀) + Zeta23.paperFT (phiC φ) (z - γ₀)) / 2 := by
  have i1 := phiC_exp_integrable hc hs (z + γ₀)
  have i2 := phiC_exp_integrable hc hs (z - γ₀)
  have hpt : ∀ u : ℝ, ((cosWin γ₀ φ u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) =
      ((φ u : ℂ) * Complex.exp (Complex.I * (z + γ₀) * (u : ℂ)) +
        (φ u : ℂ) * Complex.exp (Complex.I * (z - γ₀) * (u : ℂ))) / 2 := by
    intro u
    have e1 : Complex.exp (Complex.I * (z + γ₀) * (u : ℂ)) =
        Complex.exp (Complex.I * z * (u : ℂ)) * Complex.exp ((γ₀ : ℂ) * (u : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have e2 : Complex.exp (Complex.I * (z - γ₀) * (u : ℂ)) =
        Complex.exp (Complex.I * z * (u : ℂ)) * Complex.exp (-((γ₀ : ℂ) * (u : ℂ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hcos := Complex.two_cos ((γ₀ : ℂ) * (u : ℂ))
    unfold cosWin
    push_cast
    rw [e1, e2]
    linear_combination ((φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) / 2) * hcos
  simp only [Zeta23.paperFT, cosWinC, phiC]
  simp_rw [hpt]
  rw [integral_div, integral_add i1 i2]

/-- For an even `phi`, its transform is even. -/
theorem phiC_FT_neg {φ : ℝ → ℝ} (hev : ∀ x, φ (-x) = φ x) (z : ℂ) :
    Zeta23.paperFT (phiC φ) (-z) = Zeta23.paperFT (phiC φ) z := by
  simp only [Zeta23.paperFT, phiC]
  rw [← integral_neg_eq_self]
  congr 1
  ext u
  simp only [hev, Complex.ofReal_neg]
  congr 2
  ring

/-- `phi^(0) = INT phi`. -/
theorem phiC_FT_zero (φ : ℝ → ℝ) : Zeta23.paperFT (phiC φ) 0 = ((∫ u, φ u : ℝ) : ℂ) := by
  simp only [Zeta23.paperFT, phiC, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_ofReal

theorem nearInt_zero (φ : ℝ → ℝ) : nearInt φ 0 = ∫ u, φ u := by
  simp only [nearInt, zero_mul, Real.cosh_zero, mul_one]

/-- **The near factor**: for an even `phi`, `phi^(i delta) = INT phi(u) cosh(delta u) du`. -/
theorem phiC_FT_imag {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (hev : ∀ x, φ (-x) = φ x) (δ : ℝ) :
    Zeta23.paperFT (phiC φ) (I * δ) = (nearInt φ δ : ℂ) := by
  have hn := phiC_FT_neg hev (I * (δ : ℂ))
  have i1 := phiC_exp_integrable hc hs (I * δ)
  have i2 := phiC_exp_integrable hc hs (-(I * δ))
  have hsum : Zeta23.paperFT (phiC φ) (I * δ) + Zeta23.paperFT (phiC φ) (-(I * δ)) = 2 * (nearInt φ δ : ℂ) := by
    have hre : ((∫ u, φ u * Real.cosh (δ * u) : ℝ) : ℂ) = ∫ u, ((φ u * Real.cosh (δ * u) : ℝ) : ℂ) :=
      integral_ofReal.symm
    simp only [Zeta23.paperFT, phiC, nearInt]
    rw [← integral_add i1 i2, hre, ← integral_const_mul]
    congr 1
    ext u
    have ea : Complex.exp (Complex.I * (Complex.I * δ) * u) = Complex.exp (-((δ : ℂ) * u)) := by
      congr 1
      linear_combination ((δ : ℂ) * u) * Complex.I_sq
    have eb : Complex.exp (Complex.I * -(Complex.I * δ) * u) = Complex.exp ((δ : ℂ) * u) := by
      congr 1
      linear_combination (-((δ : ℂ) * u)) * Complex.I_sq
    have hch := Complex.two_cosh ((δ : ℂ) * u)
    rw [ea, eb]
    push_cast
    linear_combination (-(φ u : ℂ)) * hch
  rw [hn] at hsum
  linear_combination hsum / 2

/-- For an even real `phi`, `conj F = phi^(2 gamma_0 + i delta)`. -/
theorem farFT_conj (γ₀ : ℝ) {φ : ℝ → ℝ} (hev : ∀ x, φ (-x) = φ x) (δ : ℝ) :
    conj (farFT γ₀ φ δ) = Zeta23.paperFT (phiC φ) (2 * (γ₀ : ℂ) + I * δ) := by
  have h := paperFT_ofReal_conj φ (2 * (γ₀ : ℂ) - I * δ)
  have hz : -conj (2 * (γ₀ : ℂ) - I * δ) = -(2 * (γ₀ : ℂ) + I * δ) := by
    first
    | (simp only [map_sub, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; ring)
    | (simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring)
    | simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [hz, phiC_FT_neg hev] at h
  exact h

/-- The four values of the cosine window's transform, near and far, for an even `phi`. -/
theorem cosWinC_FT_near_far (γ₀ : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ)
    (hev : ∀ x, φ (-x) = φ x) (δ : ℝ) :
    Zeta23.paperFT (cosWinC γ₀ φ) ((γ₀ : ℂ) - I * δ) = ((nearInt φ δ : ℂ) + farFT γ₀ φ δ) / 2 ∧
    Zeta23.paperFT (cosWinC γ₀ φ) (-(γ₀ : ℂ) + I * δ) = ((nearInt φ δ : ℂ) + farFT γ₀ φ δ) / 2 ∧
    Zeta23.paperFT (cosWinC γ₀ φ) ((γ₀ : ℂ) + I * δ) = ((nearInt φ δ : ℂ) + conj (farFT γ₀ φ δ)) / 2 ∧
    Zeta23.paperFT (cosWinC γ₀ φ) (-(γ₀ : ℂ) - I * δ) = ((nearInt φ δ : ℂ) + conj (farFT γ₀ φ δ)) / 2 := by
  have hN := phiC_FT_imag hc hs hev δ
  have hN' : Zeta23.paperFT (phiC φ) (-(I * δ)) = (nearInt φ δ : ℂ) := by
    rw [phiC_FT_neg hev]
    exact hN
  have hF' := farFT_conj γ₀ hev δ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cosWinC_FT γ₀ hc hs, show (γ₀ : ℂ) - I * δ + γ₀ = 2 * γ₀ - I * δ by ring,
      show (γ₀ : ℂ) - I * δ - γ₀ = -(I * δ) by ring, hN']
    unfold farFT
    ring
  · rw [cosWinC_FT γ₀ hc hs, show -(γ₀ : ℂ) + I * δ + γ₀ = I * δ by ring,
      show -(γ₀ : ℂ) + I * δ - γ₀ = -(2 * γ₀ - I * δ) by ring, hN, phiC_FT_neg hev]
    unfold farFT
    ring
  · rw [cosWinC_FT γ₀ hc hs, hF', show (γ₀ : ℂ) + I * δ + γ₀ = 2 * γ₀ + I * δ by ring,
      show (γ₀ : ℂ) + I * δ - γ₀ = I * δ by ring, hN]
    ring
  · rw [cosWinC_FT γ₀ hc hs, hF', show -(γ₀ : ℂ) - I * δ + γ₀ = -(I * δ) by ring,
      show -(γ₀ : ℂ) - I * δ - γ₀ = -(2 * γ₀ + I * δ) by ring, hN', phiC_FT_neg hev]

/-- **COMPONENT 1, near and far:** for an even `phi`, the pair's term with the near factor `N = INT phi cosh(delta u)`
and the far factor `F = phi^(2 gamma_0 - i delta)` named. -/
theorem pairTwo_near_far (γ₀ δ : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ)
    (hev : ∀ x, φ (-x) = φ x) :
    pairTwo γ₀ φ δ =
      (((δ : ℂ) ^ 2 + 2 * I * γ₀ * δ) * ((nearInt φ δ : ℂ) + farFT γ₀ φ δ) / 2) ^ 2 +
      (((δ : ℂ) ^ 2 - 2 * I * γ₀ * δ) * ((nearInt φ δ : ℂ) + conj (farFT γ₀ φ δ)) / 2) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := cosWinC_FT_near_far γ₀ hφ.continuous hφs hev δ
  rw [pairTwo_factored γ₀ δ hφ hφs, h1, h2, h3, h4]
  ring

/-! ### Component 2 -- the near factor bounded below -/

/-- **COMPONENT 2:** from `phi >= 0`, `INT phi <= INT phi cosh(delta u)`. -/
theorem nearInt_ge {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (hnn : ∀ x, 0 ≤ φ x) (δ : ℝ) :
    (∫ u, φ u) ≤ nearInt φ δ := by
  unfold nearInt
  have i1 : Integrable φ := hc.integrable_of_hasCompactSupport hs
  have hch : Continuous (fun u : ℝ => Real.cosh (δ * u)) := by fun_prop
  have i2 : Integrable (fun u => φ u * Real.cosh (δ * u)) :=
    (hc.mul hch).integrable_of_hasCompactSupport (hs.mul_right (f' := fun u : ℝ => Real.cosh (δ * u)))
  have hc1 : ∀ x : ℝ, 1 ≤ Real.cosh x := fun x => by
    nlinarith [Real.cosh_sq x, Real.cosh_pos x, sq_nonneg (Real.sinh x)]
  exact integral_mono i1 i2 (fun u => le_mul_of_one_le_right (hnn u) (hc1 _))

theorem nearInt_pos {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (hnn : ∀ x, 0 ≤ φ x)
    (hpos : 0 < ∫ u, φ u) (δ : ℝ) : 0 < nearInt φ δ :=
  lt_of_lt_of_le hpos (nearInt_ge hc hs hnn δ)

/-- **b524's realized G is that ratio**, by definition. -/
theorem realizedGrowth_eq (φ : ℝ → ℝ) (δ : ℝ) : realizedGrowth φ δ = nearInt φ δ / ∫ u, φ u := rfl

theorem realizedGrowth_ge_one {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (hnn : ∀ x, 0 ≤ φ x)
    (hpos : 0 < ∫ u, φ u) (δ : ℝ) : 1 ≤ realizedGrowth φ δ := by
  rw [realizedGrowth_eq, le_div_iff₀ hpos, one_mul]
  exact nearInt_ge hc hs hnn δ

/-- **The near-factor product at the pair**: the pair's term with the far factor set to zero, `N` the near factor. -/
def nearPair (γ₀ δ N : ℝ) : ℂ :=
  (((δ : ℂ) ^ 2 + 2 * I * γ₀ * δ) * (N : ℂ) / 2) ^ 2 + (((δ : ℂ) ^ 2 - 2 * I * γ₀ * δ) * (N : ℂ) / 2) ^ 2

theorem nearPair_eq (γ₀ δ N : ℝ) : nearPair γ₀ δ N = ((N ^ 2 * δ ^ 2 * (δ ^ 2 - 4 * γ₀ ^ 2) / 2 : ℝ) : ℂ) := by
  unfold nearPair
  push_cast
  linear_combination (2 * (N : ℂ) ^ 2 * (γ₀ : ℂ) ^ 2 * (δ : ℂ) ^ 2) * Complex.I_sq

theorem nearPair_neg (γ₀ δ N : ℝ) (hδ : 0 < δ) (hδγ : δ < 2 * γ₀) (hN : 0 < N) : (nearPair γ₀ δ N).re < 0 := by
  rw [nearPair_eq, Complex.ofReal_re]
  have h1 : δ ^ 2 - 4 * γ₀ ^ 2 < 0 := by nlinarith
  have h2 : 0 < N ^ 2 * δ ^ 2 := by positivity
  have h3 : N ^ 2 * δ ^ 2 * (δ ^ 2 - 4 * γ₀ ^ 2) < 0 := mul_neg_of_pos_of_neg h2 h1
  linarith

/-- **COMPONENT 2, the sign at the pair, fixed:** for `phi >= 0` with `INT phi > 0` and `0 < delta < 2 gamma_0`, the
near-factor product at the pair is negative. -/
theorem pair_near_sign (γ₀ δ : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) (hnn : ∀ x, 0 ≤ φ x)
    (hpos : 0 < ∫ u, φ u) (hδ : 0 < δ) (hδγ : δ < 2 * γ₀) : (nearPair γ₀ δ (nearInt φ δ)).re < 0 :=
  nearPair_neg γ₀ δ _ hδ hδγ (nearInt_pos hc hs hnn hpos δ)

/-! ### Component 3 -- the far factor as a named hypothesis -/

/-- **THE HYPOTHESIS OF COMPONENT 3, A Prop, NOT PROVED:** the far factor is at most `eps` times the near factor,
`|phi^(2 gamma_0 - i delta)| <= eps * INT phi cosh(delta u)`. -/
def farSmall (γ₀ : ℝ) (φ : ℝ → ℝ) (δ ε : ℝ) : Prop := ‖farFT γ₀ φ δ‖ ≤ ε * nearInt φ δ

/-- `c = 2`: the pair's two terms, each contributing `-delta^2 slope^2 G^2` at first order. -/
def pairConst : ℝ := 2

/-- `eps'`: the loss to `c` from the far factor (through `2 eps + eps^2`, in the pair and in the slope) and from the
second order in `delta / gamma_0`. -/
def pairEps (ε δ γ₀ : ℝ) : ℝ :=
  pairConst - (2 * (1 - (2 * ε + ε ^ 2)) - δ ^ 2 / (2 * γ₀ ^ 2) * (1 + (2 * ε + ε ^ 2))) / (1 + ε) ^ 2

theorem cross_bound (N ε : ℝ) (G : ℂ) (hN : 0 ≤ N) (hG : ‖G‖ ≤ ε * N) :
    ‖2 * (N : ℂ) * G + G ^ 2‖ ≤ (2 * ε + ε ^ 2) * N ^ 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simpa using Complex.norm_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  have hG0 : 0 ≤ ‖G‖ := norm_nonneg G
  have a1 : 2 * N * ‖G‖ ≤ 2 * N * (ε * N) := mul_le_mul_of_nonneg_left hG (by linarith)
  have a2 := mul_self_le_mul_self hG0 hG
  calc ‖2 * (N : ℂ) * G + G ^ 2‖ ≤ ‖2 * (N : ℂ) * G‖ + ‖G ^ 2‖ := norm_add_le _ _
    _ = 2 * N * ‖G‖ + ‖G‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow, h2, Complex.norm_of_nonneg hN]
    _ ≤ 2 * N * (ε * N) + (ε * N) ^ 2 := by nlinarith
    _ = (2 * ε + ε ^ 2) * N ^ 2 := by ring

theorem weight_norm_plus (γ₀ δ : ℝ) : ‖((δ : ℂ) ^ 2 + 2 * I * γ₀ * δ) ^ 2‖ = δ ^ 4 + 4 * γ₀ ^ 2 * δ ^ 2 := by
  have hw : (δ : ℂ) ^ 2 + 2 * I * γ₀ * δ = ((δ ^ 2 : ℝ) : ℂ) + ((2 * γ₀ * δ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [norm_pow, Complex.sq_norm, hw, Complex.normSq_add_mul_I]
  ring

theorem weight_norm_minus (γ₀ δ : ℝ) : ‖((δ : ℂ) ^ 2 - 2 * I * γ₀ * δ) ^ 2‖ = δ ^ 4 + 4 * γ₀ ^ 2 * δ ^ 2 := by
  have hw : (δ : ℂ) ^ 2 - 2 * I * γ₀ * δ = ((δ ^ 2 : ℝ) : ℂ) + ((-(2 * γ₀ * δ) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [norm_pow, Complex.sq_norm, hw, Complex.normSq_add_mul_I]
  ring

/-- The algebra of Component 3, on named reals: `N` the near factor, `S = INT phi`, `F` the far factor, `sl` the slope. -/
theorem pair_algebra (γ δ ε N S : ℝ) (F sl : ℂ) (hγ : 0 < γ) (hε : 0 ≤ ε) (hS : 0 < S) (hSN : S ≤ N)
    (hF : ‖F‖ ≤ ε * N) (hsl : ‖sl‖ ≤ γ * (1 + ε) * S) (hc : pairEps ε δ γ ≤ pairConst) :
    ((((δ : ℂ) ^ 2 + 2 * I * γ * δ) * ((N : ℂ) + F) / 2) ^ 2 +
      (((δ : ℂ) ^ 2 - 2 * I * γ * δ) * ((N : ℂ) + conj F) / 2) ^ 2).re ≤
      -(pairConst - pairEps ε δ γ) * δ ^ 2 * ‖sl‖ ^ 2 * (N / S) ^ 2 := by
  have hN : 0 < N := lt_of_lt_of_le hS hSN
  have hsplit : (((δ : ℂ) ^ 2 + 2 * I * γ * δ) * ((N : ℂ) + F) / 2) ^ 2 +
      (((δ : ℂ) ^ 2 - 2 * I * γ * δ) * ((N : ℂ) + conj F) / 2) ^ 2 =
      nearPair γ δ N + ((1 / 4 : ℝ) : ℂ) * (((δ : ℂ) ^ 2 + 2 * I * γ * δ) ^ 2 * (2 * (N : ℂ) * F + F ^ 2) +
        ((δ : ℂ) ^ 2 - 2 * I * γ * δ) ^ 2 * (2 * (N : ℂ) * conj F + (conj F) ^ 2)) := by
    unfold nearPair
    push_cast
    ring
  have hF' : ‖conj F‖ ≤ ε * N := by
    rw [Complex.norm_conj]
    exact hF
  have hA : (((δ : ℂ) ^ 2 + 2 * I * γ * δ) ^ 2 * (2 * (N : ℂ) * F + F ^ 2)).re ≤
      (δ ^ 4 + 4 * γ ^ 2 * δ ^ 2) * ((2 * ε + ε ^ 2) * N ^ 2) := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, weight_norm_plus]
    exact mul_le_mul_of_nonneg_left (cross_bound N ε F hN.le hF) (by positivity)
  have hB : (((δ : ℂ) ^ 2 - 2 * I * γ * δ) ^ 2 * (2 * (N : ℂ) * conj F + (conj F) ^ 2)).re ≤
      (δ ^ 4 + 4 * γ ^ 2 * δ ^ 2) * ((2 * ε + ε ^ 2) * N ^ 2) := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, weight_norm_minus]
    exact mul_le_mul_of_nonneg_left (cross_bound N ε (conj F) hN.le hF') (by positivity)
  have hsl2 : ‖sl‖ ^ 2 * (N / S) ^ 2 ≤ γ ^ 2 * (1 + ε) ^ 2 * N ^ 2 := by
    have h0 : 0 ≤ ‖sl‖ := norm_nonneg _
    have h1 : ‖sl‖ ^ 2 ≤ (γ * (1 + ε) * S) ^ 2 := by nlinarith [mul_self_le_mul_self h0 hsl]
    have h2 : (γ * (1 + ε) * S) ^ 2 * (N / S) ^ 2 = γ ^ 2 * (1 + ε) ^ 2 * N ^ 2 := by
      rw [show (γ * (1 + ε) * S) ^ 2 * (N / S) ^ 2 = γ ^ 2 * (1 + ε) ^ 2 * N ^ 2 * (S / S) ^ 2 by ring,
        div_self hS.ne']
      ring
    calc ‖sl‖ ^ 2 * (N / S) ^ 2 ≤ (γ * (1 + ε) * S) ^ 2 * (N / S) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = γ ^ 2 * (1 + ε) ^ 2 * N ^ 2 := h2
  have hK : pairConst - pairEps ε δ γ =
      (2 * (1 - (2 * ε + ε ^ 2)) - δ ^ 2 / (2 * γ ^ 2) * (1 + (2 * ε + ε ^ 2))) / (1 + ε) ^ 2 := by
    unfold pairEps
    ring
  have hK0 : 0 ≤ pairConst - pairEps ε δ γ := by linarith
  have h1e : (1 + ε) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith : (0 : ℝ) < 1 + ε).ne'
  have hγ2 : γ ^ 2 ≠ 0 := pow_ne_zero 2 hγ.ne'
  have hq : (1 + ε) ^ 2 / (1 + ε) ^ 2 = 1 := div_self h1e
  have hg : γ ^ 2 / γ ^ 2 = 1 := div_self hγ2
  have hmain : -(pairConst - pairEps ε δ γ) * δ ^ 2 * (γ ^ 2 * (1 + ε) ^ 2 * N ^ 2) =
      N ^ 2 * δ ^ 2 * (δ ^ 2 - 4 * γ ^ 2) / 2 + 1 / 4 * ((δ ^ 4 + 4 * γ ^ 2 * δ ^ 2) * ((2 * ε + ε ^ 2) * N ^ 2) +
        (δ ^ 4 + 4 * γ ^ 2 * δ ^ 2) * ((2 * ε + ε ^ 2) * N ^ 2)) := by
    rw [hK]
    first
    | (calc _ = -(2 * (1 - (2 * ε + ε ^ 2))) * γ ^ 2 * δ ^ 2 * N ^ 2 * ((1 + ε) ^ 2 / (1 + ε) ^ 2) +
              δ ^ 2 * (1 + (2 * ε + ε ^ 2)) / 2 * δ ^ 2 * N ^ 2 * (γ ^ 2 / γ ^ 2) *
                ((1 + ε) ^ 2 / (1 + ε) ^ 2) := by ring
          _ = _ := by rw [hq, hg]; ring)
    | (field_simp; ring)
  have hfin : -(pairConst - pairEps ε δ γ) * δ ^ 2 * (γ ^ 2 * (1 + ε) ^ 2 * N ^ 2) ≤
      -(pairConst - pairEps ε δ γ) * δ ^ 2 * (‖sl‖ ^ 2 * (N / S) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsl2 (mul_nonneg hK0 (sq_nonneg δ))
    linarith
  rw [hsplit, Complex.add_re, nearPair_eq, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.add_re]
  linarith [hA, hB, hmain, hfin]

/-- The slope `-2 gamma_0 C(gamma_0)` bounded through the far factor at `delta = 0`. -/
theorem windowSlope_bound (γ₀ ε : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ)
    (hγ : 0 < γ₀) (hS : 0 ≤ ∫ u, φ u) (hfar0 : farSmall γ₀ φ 0 ε) :
    ‖windowSlope γ₀ φ‖ ≤ γ₀ * (1 + ε) * ∫ u, φ u := by
  unfold farSmall farFT at hfar0
  rw [Complex.ofReal_zero, mul_zero, sub_zero, nearInt_zero] at hfar0
  unfold windowSlope
  rw [cosWinC_FT γ₀ hc hs, show (γ₀ : ℂ) + γ₀ = 2 * γ₀ by ring, sub_self, phiC_FT_zero]
  calc ‖-2 * (γ₀ : ℂ) * ((Zeta23.paperFT (phiC φ) (2 * γ₀) + ((∫ u, φ u : ℝ) : ℂ)) / 2)‖
      = ‖-(γ₀ : ℂ) * (Zeta23.paperFT (phiC φ) (2 * γ₀) + ((∫ u, φ u : ℝ) : ℂ))‖ := by
        congr 1
        ring
    _ = γ₀ * ‖Zeta23.paperFT (phiC φ) (2 * γ₀) + ((∫ u, φ u : ℝ) : ℂ)‖ := by
        rw [norm_mul, norm_neg, Complex.norm_of_nonneg hγ.le]
    _ ≤ γ₀ * (‖Zeta23.paperFT (phiC φ) (2 * γ₀)‖ + ‖((∫ u, φ u : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hγ.le
    _ ≤ γ₀ * (ε * (∫ u, φ u) + ∫ u, φ u) := by
        rw [Complex.norm_of_nonneg hS]
        exact mul_le_mul_of_nonneg_left (by linarith) hγ.le
    _ = γ₀ * (1 + ε) * ∫ u, φ u := by ring

/-- **COMPONENT 3, UNDER THE NAMED HYPOTHESIS:** for an even `phi >= 0`, `C^4`, compactly supported, `INT phi > 0`, and
`gamma_0, delta > 0`: if the far factor is at most `eps` times the near factor at `delta` and at `0`, and `eps' <= c`, then
the pair's term is at most `-(c - eps') delta^2 |slope|^2 G^2`. -/
theorem pair_bound (γ₀ δ ε : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (hφs : HasCompactSupport φ)
    (hev : ∀ x, φ (-x) = φ x) (hnn : ∀ x, 0 ≤ φ x) (hpos : 0 < ∫ u, φ u)
    (hγ : 0 < γ₀) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hfar : farSmall γ₀ φ δ ε) (hfar0 : farSmall γ₀ φ 0 ε) (hc : pairEps ε δ γ₀ ≤ pairConst) :
    (pairTwo γ₀ φ δ).re ≤
      -(pairConst - pairEps ε δ γ₀) * δ ^ 2 * ‖windowSlope γ₀ φ‖ ^ 2 * realizedGrowth φ δ ^ 2 := by
  rw [pairTwo_near_far γ₀ δ hφ hφs hev, realizedGrowth_eq]
  exact pair_algebra γ₀ δ ε (nearInt φ δ) (∫ u, φ u) (farFT γ₀ φ δ) (windowSlope γ₀ φ) hγ hε hpos
    (nearInt_ge hφ.continuous hφs hnn δ) hfar
    (windowSlope_bound γ₀ ε hφ.continuous hφs hγ hpos.le hfar0) hc

end B321
end SIDEExplicitFormula
