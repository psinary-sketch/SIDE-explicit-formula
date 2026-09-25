/-
SIDE-explicit-formula -- SIDEExplicitFormula/DecayBound.lean
THIS PROGRAMME'S WORK (act b530, ruling (R140)(2); W-ORD-WEIL-CONVERSE's (f3), its decay lemma (d')) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(d'), THE DECAY LEMMA. For a real `g`, `C^p`, supported in `[-L, L]`: integration by parts `p` times on the compact
support (b524's `ibp_step`, iterated) gives `paperFT (g^(p)) z = (-(i z))^p paperFT g z`, and (d) (b517's
`paperFT_growth`) applied to `g^(p)` gives `|paperFT g z| |z|^p <= (INT |g^(p)|) exp(L |Im z|)` (`paperFT_decay`); for
`Re z ≠ 0`, since `|Re z| <= |z|`, the ferry's form `|paperFT g z| <= (INT |g^(p)|) exp(L |Im z|) / |Re z|^p`
(`paperFT_decay_re`); (d) is the case `p = 0` (`paperFT_decay_zero`). Through b524's factorisation, the window's
transform: `|paperFT h z| <= |gamma_0^2 - z^2| (INT |(cos(gamma_0 .) phi)^(p)|) exp(L |Im z|) / |Re z|^p`
(`window_decay_re`). Nothing here is a statement about the zeros of zeta or about RH.
-/
import SIDEExplicitFormula.PairTerm
import SIDEExplicitFormula.GrowthBound

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

theorem hasCompactSupport_of_Icc {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    HasCompactSupport g :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => by
    by_contra h
    exact hx (hs h))

theorem support_deriv_Icc {g : ℝ → ℝ} {L : ℝ} (hs : Function.support g ⊆ Set.Icc (-L) L) :
    Function.support (deriv g) ⊆ Set.Icc (-L) L :=
  support_deriv_subset.trans (closure_minimal hs isClosed_Icc)

theorem support_iteratedDeriv_Icc (p : ℕ) : ∀ {g : ℝ → ℝ} {L : ℝ}, Function.support g ⊆ Set.Icc (-L) L →
    Function.support (iteratedDeriv p g) ⊆ Set.Icc (-L) L := by
  induction p with
  | zero =>
    intro g L hs
    rwa [iteratedDeriv_zero]
  | succ p ih =>
    intro g L hs
    rw [iteratedDeriv_succ']
    exact ih (support_deriv_Icc hs)

/-- Integration by parts `p` times on the whole line: `paperFT (g^(p)) z = (-(i z))^p paperFT g z`. -/
theorem paperFT_iteratedDeriv (p : ℕ) : ∀ (g : ℝ → ℝ), ContDiff ℝ p g → HasCompactSupport g → ∀ z : ℂ,
    Zeta23.paperFT (phiC (iteratedDeriv p g)) z = (-(I * z)) ^ p * Zeta23.paperFT (phiC g) z := by
  induction p with
  | zero =>
    intro g _ _ z
    rw [iteratedDeriv_zero, pow_zero, one_mul]
  | succ p ih =>
    intro g hg hgs z
    have hg' : ContDiff ℝ ((p : WithTop ℕ∞) + 1) g := by exact_mod_cast hg
    have hd : ContDiff ℝ p (deriv g) := hg'.deriv'
    have h1 : ContDiff ℝ 1 g := hg'.one_of_succ
    have hi : Zeta23.paperFT (phiC (deriv g)) z = -(I * z) * Zeta23.paperFT (phiC g) z := ibp_step g h1 hgs z
    rw [iteratedDeriv_succ', ih (deriv g) hd hgs.deriv z, hi]
    ring

/-- **(d'), THE DECAY LEMMA:** `|paperFT g z| |z|^p <= (INT |g^(p)|) exp(L |Im z|)` for a real `C^p` `g` supported in
`[-L, L]`, at every complex `z`. -/
theorem paperFT_decay (p : ℕ) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ p g) (hs : Function.support g ⊆ Set.Icc (-L) L)
    (z : ℂ) : ‖Zeta23.paperFT (phiC g) z‖ * ‖z‖ ^ p ≤ (∫ u, |iteratedDeriv p g u|) * Real.exp (L * |z.im|) := by
  have hgs := hasCompactSupport_of_Icc hs
  have hsp := support_iteratedDeriv_Icc p hs
  have hc : Continuous (phiC (iteratedDeriv p g)) :=
    Complex.continuous_ofReal.comp (hg.continuous_iteratedDeriv p le_rfl)
  have hcs : HasCompactSupport (phiC (iteratedDeriv p g)) :=
    (hasCompactSupport_of_Icc hsp).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hsupp : Function.support (phiC (iteratedDeriv p g)) ⊆ Set.Icc (-L) L := by
    intro u hu
    apply hsp
    intro h0
    apply hu
    simp [phiC, h0]
  have key := paperFT_growth (phiC (iteratedDeriv p g)) L (hc.integrable_of_hasCompactSupport hcs) hsupp z
  rw [paperFT_iteratedDeriv p g hg hgs z, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul] at key
  have hn : (∫ u, ‖phiC (iteratedDeriv p g) u‖) = ∫ u, |iteratedDeriv p g u| := by
    congr 1
    ext u
    simp [phiC, Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at key
  linarith

/-- **(d') in the ferry's form:** for `Re z ≠ 0`, `|paperFT g z| <= (INT |g^(p)|) exp(L |Im z|) / |Re z|^p`. -/
theorem paperFT_decay_re (p : ℕ) {g : ℝ → ℝ} {L : ℝ} (hg : ContDiff ℝ p g) (hs : Function.support g ⊆ Set.Icc (-L) L)
    (z : ℂ) (hz : z.re ≠ 0) :
    ‖Zeta23.paperFT (phiC g) z‖ ≤ (∫ u, |iteratedDeriv p g u|) * Real.exp (L * |z.im|) / |z.re| ^ p := by
  have h := paperFT_decay p hg hs z
  have hpos : 0 < |z.re| ^ p := pow_pos (abs_pos.mpr hz) p
  rw [le_div_iff₀ hpos]
  calc ‖Zeta23.paperFT (phiC g) z‖ * |z.re| ^ p ≤ ‖Zeta23.paperFT (phiC g) z‖ * ‖z‖ ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) p) (norm_nonneg _)
    _ ≤ _ := h

/-- **(d) as the case `p = 0`:** `|paperFT g z| <= (INT |g|) exp(L |Im z|)`. -/
theorem paperFT_decay_zero {g : ℝ → ℝ} {L : ℝ} (hg : Continuous g) (hs : Function.support g ⊆ Set.Icc (-L) L) (z : ℂ) :
    ‖Zeta23.paperFT (phiC g) z‖ ≤ (∫ u, |g u|) * Real.exp (L * |z.im|) := by
  have hg0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) g := by simpa using hg
  have h := paperFT_decay 0 hg0 hs z
  simpa [iteratedDeriv_zero] using h

theorem cosWin_support_Icc {γ₀ : ℝ} {φ : ℝ → ℝ} {L : ℝ} (hs : Function.support φ ⊆ Set.Icc (-L) L) :
    Function.support (cosWin γ₀ φ) ⊆ Set.Icc (-L) L := by
  intro u hu
  apply hs
  intro h0
  apply hu
  simp [cosWin, h0]

/-- **(d') for the window**, through b524's factorisation: for `Re z ≠ 0`,
`|paperFT h z| <= |gamma_0^2 - z^2| (INT |(cos(gamma_0 .) phi)^(p)|) exp(L |Im z|) / |Re z|^p`. -/
theorem window_decay_re (p : ℕ) (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ) (hφp : ContDiff ℝ p φ)
    (hs : Function.support φ ⊆ Set.Icc (-L) L) (z : ℂ) (hz : z.re ≠ 0) :
    ‖Zeta23.paperFT (windowC γ₀ φ) z‖ ≤
      ‖(γ₀ : ℂ) ^ 2 - z ^ 2‖ * ((∫ u, |iteratedDeriv p (cosWin γ₀ φ) u|) * Real.exp (L * |z.im|) / |z.re| ^ p) := by
  rw [paperFT_window γ₀ hφ (hasCompactSupport_of_Icc hs) z, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (paperFT_decay_re p (cosWin_contDiff (γ₀ := γ₀) hφp) (cosWin_support_Icc hs) z hz) (norm_nonneg _)

end B321
end SIDEExplicitFormula
