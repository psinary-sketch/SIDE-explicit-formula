/-
SIDE-explicit-formula -- SIDEExplicitFormula/RestBound.lean
THIS PROGRAMME'S WORK (act b530, ruling (R140)(2); W-ORD-WEIL-CONVERSE's (f3)) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(f3), THE OTHER ZEROS BOUNDED ABOVE, WITH ITS LIMIT PRINTED.

COMPONENT 2 (`rest_bound`). For an abstract zero configuration `Z` (the kernel's `Zeta23.ZeroConfig`), the window of
b524 at `gamma_0` (phi real, `C^4`, supported in `[-L, L]`, `L >= 0`) and `k = weilTest h h`, under the two named
hypotheses H-STRIP (`HStrip Z`: every zero has real part in `(0, 1)`) and H-COUNT (`HCount Z A0`: the kernel's local
count, `N(t, t + 1) <= A0 log(|t| + 3)`, `A0 >= 1`), the sum over the zeros outside the pair's orbit `{rho_0, 1 - conj
rho_0, conj rho_0, 1 - rho_0}` of `m_rho |k^(gamma_rho)|` is at most `restR gamma_0 phi L A0 = 768 A0 A^2 e^L (gamma_0^2 +
1)^2 SUM_m (1 + |m|)^{-3}`, `A = INT |cos(gamma_0 .) phi| + INT |(cos(gamma_0 .) phi)''''|` (`windowA`): (d') at `p = 0`
and `p = 4` per zero, `|Im gamma_rho| <= 1/2` from the strip giving `e^{L/2}` per factor and `e^L` for `k`, the zeros
grouped by `ceil(Im rho)` into unit intervals and each interval's count taken from H-COUNT. The pair's orbit is excluded
because for a conjugation-symmetric configuration the conjugates carry the pair's own terms; the bound does not use the
exclusion. `rest_bound_closed` needs no H-STRIP: the closed strip is a field of `ZeroConfig`. `rest_bound_zeta` needs no
hypothesis: H-COUNT for `zetaZeroConfig` is the kernel's `Zeta23.RvM.zetaZeroConfig_local_count`.

COMPONENT 3 (`realizedGrowth_le_exp`, `two_delta_lt_one`, `f4_needs`, `not_f4_needs`, `f4_needs_of_half_le`). The pair's
G is at most `e^{delta L}`, so the pair grows at most like `e^{2 delta L}`, while the rest is allowed `e^L`: `f4_needs
delta` (the rest's allowed growth eventually at most a constant times the pair's) fails for every `delta < 1/2` and holds
for `delta >= 1/2`.

COMPONENT 4 (`HMax`). A zero of maximal real part, as a Prop; not proved, status UNKNOWN.
Nothing here is a statement about the zeros of zeta or about RH.
-/
import SIDEExplicitFormula.DecayBound

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The named hypotheses and the bound -/

/-- **H-STRIP:** every zero has real part in the open strip `(0, 1)`. -/
def HStrip (Z : Zeta23.ZeroConfig) : Prop := ∀ ρ ∈ Z.carrier, 0 < ρ.re ∧ ρ.re < 1

/-- **H-COUNT:** the kernel's local count, `N(t, t + 1) <= A0 log(|t| + 3)` with `A0 >= 1`
(the shape of `Zeta23.RvM.zetaZeroConfig_local_count`). -/
def HCount (Z : Zeta23.ZeroConfig) (A₀ : ℝ) : Prop :=
  1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/-- `A = INT |cos(gamma_0 .) phi| + INT |(cos(gamma_0 .) phi)''''|`, the two ends of (d') at `p = 0` and `p = 4`. -/
def windowA (γ₀ : ℝ) (φ : ℝ → ℝ) : ℝ := (∫ u, |cosWin γ₀ φ u|) + ∫ u, |iteratedDeriv 4 (cosWin γ₀ φ) u|

/-- `SUM_{m in Z} (1 + |m|)^{-3}`. -/
def zeta3Sum : ℝ := ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 3

/-- **R(L, 4, gamma_0)**, the rest's bound: `768 A0 A^2 e^L (gamma_0^2 + 1)^2 SUM_m (1 + |m|)^{-3}`. -/
def restR (γ₀ : ℝ) (φ : ℝ → ℝ) (L A₀ : ℝ) : ℝ :=
  768 * A₀ * windowA γ₀ φ ^ 2 * Real.exp L * (γ₀ ^ 2 + 1) ^ 2 * zeta3Sum

/-- The pair's orbit: `rho_0`, `1 - conj rho_0`, `conj rho_0`, `1 - rho_0`. -/
def pairOrbit (ρ₀ : ℂ) : Set ℂ := {ρ₀, Zeta23.reflect ρ₀, starRingEnd ℂ ρ₀, 1 - ρ₀}

/-- **The rest:** `SUM m_rho |k^(gamma_rho)|` over the zeros outside the pair's orbit. -/
def restSum (Z : Zeta23.ZeroConfig) (γ₀ : ℝ) (φ : ℝ → ℝ) (ρ₀ : ℂ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ Z.carrier ∧ ρ ∉ pairOrbit ρ₀},
    (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖

/-! ### Per zero -/

theorem cosWin_bound (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ) (hs : Function.support φ ⊆ Set.Icc (-L) L)
    (w : ℂ) : ‖Zeta23.paperFT (cosWinC γ₀ φ) w‖ * (1 + ‖w‖ ^ 4) ≤ windowA γ₀ φ * Real.exp (L * |w.im|) := by
  have hC : ContDiff ℝ 4 (cosWin γ₀ φ) := cosWin_contDiff hφ
  have h0 := paperFT_decay_zero hC.continuous (cosWin_support_Icc (γ₀ := γ₀) hs) w
  have h4 := paperFT_decay 4 hC (cosWin_support_Icc (γ₀ := γ₀) hs) w
  have e : Zeta23.paperFT (cosWinC γ₀ φ) w = Zeta23.paperFT (phiC (cosWin γ₀ φ)) w := rfl
  rw [e]
  unfold windowA
  nlinarith [h0, h4]

theorem window_bound (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ) (hs : Function.support φ ⊆ Set.Icc (-L) L)
    (w : ℂ) : ‖Zeta23.paperFT (windowC γ₀ φ) w‖ * (1 + ‖w‖ ^ 4) ≤
      (γ₀ ^ 2 + ‖w‖ ^ 2) * (windowA γ₀ φ * Real.exp (L * |w.im|)) := by
  rw [paperFT_window γ₀ hφ (hasCompactSupport_of_Icc hs) w, norm_mul, mul_assoc]
  have hn : ‖(γ₀ : ℂ) ^ 2 - w ^ 2‖ ≤ γ₀ ^ 2 + ‖w‖ ^ 2 := by
    calc ‖(γ₀ : ℂ) ^ 2 - w ^ 2‖ ≤ ‖(γ₀ : ℂ) ^ 2‖ + ‖w ^ 2‖ := norm_sub_le _ _
      _ = γ₀ ^ 2 + ‖w‖ ^ 2 := by rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul hn (cosWin_bound γ₀ hφ hs w) (by positivity) (by positivity)

theorem kWin_bound (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ) (hs : Function.support φ ⊆ Set.Icc (-L) L)
    (hL : 0 ≤ L) (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (kWin γ₀ φ) z‖ * (1 + ‖z‖ ^ 4) ^ 2 ≤
      (γ₀ ^ 2 + ‖z‖ ^ 2) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) := by
  have hA : 0 ≤ windowA γ₀ φ := by
    unfold windowA
    exact add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have he : Real.exp (L * |z.im|) ≤ Real.exp (L / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  have he' : Real.exp (L * |(-z).im|) ≤ Real.exp (L / 2) := by rwa [Complex.neg_im, abs_neg]
  have b1 := window_bound γ₀ hφ hs z
  have b2 := window_bound γ₀ hφ hs (-z)
  rw [norm_neg] at b2
  have b1' : ‖Zeta23.paperFT (windowC γ₀ φ) z‖ * (1 + ‖z‖ ^ 4) ≤ (γ₀ ^ 2 + ‖z‖ ^ 2) * (windowA γ₀ φ * Real.exp (L / 2)) :=
    b1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hA) (by positivity))
  have b2' : ‖Zeta23.paperFT (windowC γ₀ φ) (-z)‖ * (1 + ‖z‖ ^ 4) ≤
      (γ₀ ^ 2 + ‖z‖ ^ 2) * (windowA γ₀ φ * Real.exp (L / 2)) :=
    b2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' hA) (by positivity))
  have hexp : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [kWin_FT γ₀ hφ (hasCompactSupport_of_Icc hs) z, norm_mul]
  calc ‖Zeta23.paperFT (windowC γ₀ φ) z‖ * ‖Zeta23.paperFT (windowC γ₀ φ) (-z)‖ * (1 + ‖z‖ ^ 4) ^ 2
      = (‖Zeta23.paperFT (windowC γ₀ φ) z‖ * (1 + ‖z‖ ^ 4)) *
          (‖Zeta23.paperFT (windowC γ₀ φ) (-z)‖ * (1 + ‖z‖ ^ 4)) := by ring
    _ ≤ ((γ₀ ^ 2 + ‖z‖ ^ 2) * (windowA γ₀ φ * Real.exp (L / 2))) *
          ((γ₀ ^ 2 + ‖z‖ ^ 2) * (windowA γ₀ φ * Real.exp (L / 2))) :=
        mul_le_mul b1' b2' (by positivity) (by positivity)
    _ = (γ₀ ^ 2 + ‖z‖ ^ 2) ^ 2 * (windowA γ₀ φ ^ 2 * (Real.exp (L / 2) * Real.exp (L / 2))) := by ring
    _ = (γ₀ ^ 2 + ‖z‖ ^ 2) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) := by rw [hexp]

/-- A real inequality: `(g^2 + x^2)^2 (1 + |m|)^4 <= 256 (g^2 + 1)^2 (1 + x^4)^2` for `|t| <= x`, `m - 1 < t <= m`. -/
theorem weight_ineq (γ₀ x t m : ℝ) (hx : 0 ≤ x) (htx : |t| ≤ x) (hm1 : m - 1 < t) (hm2 : t ≤ m) :
    (γ₀ ^ 2 + x ^ 2) ^ 2 * (1 + |m|) ^ 4 ≤ 256 * (γ₀ ^ 2 + 1) ^ 2 * (1 + x ^ 4) ^ 2 := by
  have a : γ₀ ^ 2 + x ^ 2 ≤ (γ₀ ^ 2 + 1) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg γ₀, sq_nonneg x, mul_nonneg (sq_nonneg γ₀) (sq_nonneg x)]
  have b : (1 + x ^ 2) ^ 2 ≤ 2 * (1 + x ^ 4) := by nlinarith [sq_nonneg (1 - x ^ 2)]
  have hm : |m| ≤ x + 1 := abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have c : 1 + |m| ≤ 2 * (1 + x) := by linarith
  have d : (1 + x) ^ 4 ≤ 8 * (1 + x ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by positivity : (0 : ℝ) ≤ 7 * x ^ 2 + 10 * x + 7)]
  have e : (1 + |m|) ^ 4 ≤ 16 * (8 * (1 + x ^ 4)) := by
    calc (1 + |m|) ^ 4 ≤ (2 * (1 + x)) ^ 4 := pow_le_pow_left₀ (by positivity) c 4
      _ = 16 * (1 + x) ^ 4 := by ring
      _ ≤ 16 * (8 * (1 + x ^ 4)) := by linarith
  have f : (γ₀ ^ 2 + x ^ 2) ^ 2 ≤ (γ₀ ^ 2 + 1) ^ 2 * (2 * (1 + x ^ 4)) := by
    calc (γ₀ ^ 2 + x ^ 2) ^ 2 ≤ ((γ₀ ^ 2 + 1) * (1 + x ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) a 2
      _ = (γ₀ ^ 2 + 1) ^ 2 * (1 + x ^ 2) ^ 2 := by ring
      _ ≤ (γ₀ ^ 2 + 1) ^ 2 * (2 * (1 + x ^ 4)) := mul_le_mul_of_nonneg_left b (by positivity)
  calc (γ₀ ^ 2 + x ^ 2) ^ 2 * (1 + |m|) ^ 4 ≤ ((γ₀ ^ 2 + 1) ^ 2 * (2 * (1 + x ^ 4))) * (16 * (8 * (1 + x ^ 4))) :=
        mul_le_mul f e (by positivity) (by positivity)
    _ = 256 * (γ₀ ^ 2 + 1) ^ 2 * (1 + x ^ 4) ^ 2 := by ring

theorem gammaOf_re' (ρ : ℂ) : (Zeta23.gammaOf ρ).re = ρ.im := by
  unfold Zeta23.gammaOf
  rw [Complex.div_I, Complex.neg_re, Complex.mul_I_re, Complex.sub_im, Complex.div_ofNat_im, Complex.one_im]
  ring

theorem gammaOf_im' (ρ : ℂ) : (Zeta23.gammaOf ρ).im = -(ρ.re - 1 / 2) := by
  unfold Zeta23.gammaOf
  rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]

/-- **Per zero:** `|k^(gamma_rho)| (1 + |ceil(Im rho)|)^4 <= 256 (gamma_0^2 + 1)^2 A^2 e^L` when `|Re rho - 1/2| <= 1/2`. -/
theorem zero_term_bound (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ) (hs : Function.support φ ⊆ Set.Icc (-L) L)
    (hL : 0 ≤ L) (ρ : ℂ) (hρ : |ρ.re - 1 / 2| ≤ 1 / 2) :
    ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖ * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 ≤
      256 * (γ₀ ^ 2 + 1) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) := by
  set z := Zeta23.gammaOf ρ with hzdef
  have him : |z.im| ≤ 1 / 2 := by rw [hzdef, gammaOf_im', abs_neg]; exact hρ
  have hk := kWin_bound γ₀ hφ hs hL z him
  have hre : z.re = ρ.im := by rw [hzdef]; exact gammaOf_re' ρ
  have htx : |ρ.im| ≤ ‖z‖ := by rw [← hre]; exact Complex.abs_re_le_norm z
  have hceil := Int.ceil_eq_iff.mp (rfl : ⌈ρ.im⌉ = ⌈ρ.im⌉)
  have hw := weight_ineq γ₀ ‖z‖ ρ.im ((⌈ρ.im⌉ : ℤ) : ℝ) (norm_nonneg _) htx hceil.1 hceil.2
  have hAE : 0 ≤ windowA γ₀ φ ^ 2 * Real.exp L := by positivity
  have hpos : 0 < (1 + ‖z‖ ^ 4) ^ 2 := by positivity
  have h1 : ‖Zeta23.paperFT (kWin γ₀ φ) z‖ * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 * (1 + ‖z‖ ^ 4) ^ 2 ≤
      256 * (γ₀ ^ 2 + 1) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) * (1 + ‖z‖ ^ 4) ^ 2 := by
    calc ‖Zeta23.paperFT (kWin γ₀ φ) z‖ * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 * (1 + ‖z‖ ^ 4) ^ 2
        = (‖Zeta23.paperFT (kWin γ₀ φ) z‖ * (1 + ‖z‖ ^ 4) ^ 2) * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 := by ring
      _ ≤ ((γ₀ ^ 2 + ‖z‖ ^ 2) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L)) * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 :=
          mul_le_mul_of_nonneg_right hk (by positivity)
      _ = ((γ₀ ^ 2 + ‖z‖ ^ 2) ^ 2 * (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4) * (windowA γ₀ φ ^ 2 * Real.exp L) := by ring
      _ ≤ (256 * (γ₀ ^ 2 + 1) ^ 2 * (1 + ‖z‖ ^ 4) ^ 2) * (windowA γ₀ φ ^ 2 * Real.exp L) :=
          mul_le_mul_of_nonneg_right hw hAE
      _ = 256 * (γ₀ ^ 2 + 1) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) * (1 + ‖z‖ ^ 4) ^ 2 := by ring
  exact le_of_mul_le_mul_right h1 hpos

/-! ### Summing over unit intervals -/

theorem summable_zeta3 : Summable (fun m : ℤ => 1 / (1 + |(m : ℝ)|) ^ 3) := by
  have base : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨base.congr fun n => ?_, base.congr fun n => ?_⟩
  · first
    | (dsimp only; rw [Int.cast_natCast, Nat.abs_cast, add_comm])
    | simp [add_comm]
  · first
    | (dsimp only; rw [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, add_comm])
    | simp [add_comm]

theorem zeta3Sum_nonneg : 0 ≤ zeta3Sum := tsum_nonneg fun m => by positivity

/-- The multiplicities of the zeros of a finite set `s` with `ceil(Im rho) = m` are at most `N(m - 1, m)`. -/
theorem fiber_count (Z : Zeta23.ZeroConfig) (s : Finset ℂ) (hs : ∀ ρ ∈ s, ρ ∈ Z.carrier) (m : ℤ) :
    (∑ ρ ∈ s.filter (fun ρ => ⌈ρ.im⌉ = m), (Z.mult ρ : ℝ)) ≤ (Z.N ((m : ℝ) - 1) (m : ℝ) : ℝ) := by
  have hfin : (Z.window ((m : ℝ) - 1) (m : ℝ)).Finite := Z.finite_window _ _
  unfold Zeta23.ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Nat.cast_sum]
  apply Nat.cast_le.mpr
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Finset.mem_filter] at hρ
  rw [Set.Finite.mem_toFinset]
  show ρ ∈ Z.carrier ∩ {ρ | ((m : ℝ) - 1) < ρ.im ∧ ρ.im ≤ (m : ℝ)}
  exact ⟨hs ρ hρ.1, Int.ceil_eq_iff.mp hρ.2⟩

/-- **The finite sums:** for every finite set of zeros, `SUM m_rho |k^(gamma_rho)| <= restR`, under the closed strip
bound `|Re rho - 1/2| <= 1/2` and H-COUNT. -/
theorem finite_rest_bound (Z : Zeta23.ZeroConfig) (γ₀ : ℝ) {φ : ℝ → ℝ} {L A₀ : ℝ} (hφ : ContDiff ℝ 4 φ)
    (hs : Function.support φ ⊆ Set.Icc (-L) L) (hL : 0 ≤ L)
    (hstrip : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ 1 / 2) (hcount : HCount Z A₀)
    (s : Finset ℂ) (hsZ : ∀ ρ ∈ s, ρ ∈ Z.carrier) :
    (∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖) ≤ restR γ₀ φ L A₀ := by
  set B : ℝ := 256 * (γ₀ ^ 2 + 1) ^ 2 * (windowA γ₀ φ ^ 2 * Real.exp L) with hB
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ A₀ := by linarith [hcount.1]
  set c : ℂ → ℤ := fun ρ => ⌈ρ.im⌉ with hc
  set w : ℤ → ℝ := fun m => B / (1 + |(m : ℝ)|) ^ 4 with hw
  have step1 : (∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖) ≤
      ∑ ρ ∈ s, (Z.mult ρ : ℝ) * w (c ρ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hpos : 0 < (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4 := by positivity
    show _ ≤ B / (1 + |((⌈ρ.im⌉ : ℤ) : ℝ)|) ^ 4
    exact (le_div_iff₀ hpos).mpr
      (zero_term_bound γ₀ hφ hs hL ρ (hstrip ρ (hsZ ρ hρ)))
  have step2 : (∑ ρ ∈ s, (Z.mult ρ : ℝ) * w (c ρ)) =
      ∑ m ∈ s.image c, w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image c) (g := c) (fun ρ hρ => Finset.mem_image_of_mem c hρ)]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [(Finset.mem_filter.mp hρ).2]
    ring
  have step3 : (∑ m ∈ s.image c, w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ)) ≤
      ∑ m ∈ s.image c, 3 * A₀ * B * (1 / (1 + |(m : ℝ)|) ^ 3) := by
    apply Finset.sum_le_sum
    intro m _
    have hwm : 0 ≤ w m := div_nonneg hB0 (by positivity)
    have hf := fiber_count Z s hsZ m
    have hcnt := hcount.2 ((m : ℝ) - 1)
    rw [sub_add_cancel] at hcnt
    have hlog : Real.log (|(m : ℝ) - 1| + 3) ≤ 3 * (1 + |(m : ℝ)|) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |(m : ℝ) - 1| + 3)
      have h2 : |(m : ℝ) - 1| ≤ |(m : ℝ)| + 1 :=
        abs_le.mpr ⟨by linarith [neg_abs_le (m : ℝ)], by linarith [le_abs_self (m : ℝ)]⟩
      linarith [abs_nonneg (m : ℝ)]
    have hN : (∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ)) ≤ A₀ * (3 * (1 + |(m : ℝ)|)) :=
      hf.trans (hcnt.trans (mul_le_mul_of_nonneg_left hlog hA0))
    have hne : (1 + |(m : ℝ)|) ≠ 0 := by positivity
    calc w m * ∑ ρ ∈ s.filter (fun ρ => c ρ = m), (Z.mult ρ : ℝ) ≤ w m * (A₀ * (3 * (1 + |(m : ℝ)|))) :=
          mul_le_mul_of_nonneg_left hN hwm
      _ = 3 * A₀ * B * (1 / (1 + |(m : ℝ)|) ^ 3) := by
          show B / (1 + |(m : ℝ)|) ^ 4 * (A₀ * (3 * (1 + |(m : ℝ)|))) = 3 * A₀ * B * (1 / (1 + |(m : ℝ)|) ^ 3)
          have hq : (1 + |(m : ℝ)|) / (1 + |(m : ℝ)|) ^ 4 = 1 / (1 + |(m : ℝ)|) ^ 3 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            ring
          calc B / (1 + |(m : ℝ)|) ^ 4 * (A₀ * (3 * (1 + |(m : ℝ)|)))
              = 3 * A₀ * B * ((1 + |(m : ℝ)|) / (1 + |(m : ℝ)|) ^ 4) := by ring
            _ = 3 * A₀ * B * (1 / (1 + |(m : ℝ)|) ^ 3) := by rw [hq]
  have step4 : (∑ m ∈ s.image c, 3 * A₀ * B * (1 / (1 + |(m : ℝ)|) ^ 3)) ≤ 3 * A₀ * B * zeta3Sum := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (summable_zeta3.sum_le_tsum _ (fun m _ => by positivity)) (mul_nonneg (mul_nonneg (by norm_num) hA0) hB0)
  have hR : 3 * A₀ * B * zeta3Sum = restR γ₀ φ L A₀ := by
    rw [hB]
    unfold restR
    ring
  rw [← hR]
  linarith [step1, step2, step3, step4]

/-! ### Component 2 -/

theorem rest_le_of_finite (Z : Zeta23.ZeroConfig) (γ₀ : ℝ) (φ : ℝ → ℝ) (ρ₀ : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ s : Finset ℂ, (∀ ρ ∈ s, ρ ∈ Z.carrier) →
      (∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖) ≤ R) :
    restSum Z γ₀ φ ρ₀ ≤ R := by
  unfold restSum
  refine tsum_le_of_sum_le' hR fun s => ?_
  calc (∑ i ∈ s, (Z.mult (i : ℂ) : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf (i : ℂ))‖)
      = ∑ ρ ∈ s.map (Function.Embedding.subtype (fun ρ : ℂ => ρ ∈ Z.carrier ∧ ρ ∉ pairOrbit ρ₀)),
          (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖ :=
        (Finset.sum_map s (Function.Embedding.subtype (fun ρ : ℂ => ρ ∈ Z.carrier ∧ ρ ∉ pairOrbit ρ₀))
          (fun ρ => (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (kWin γ₀ φ) (Zeta23.gammaOf ρ)‖)).symm
    _ ≤ R := h _ fun ρ hρ => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hρ
        exact i.2.1

theorem restR_nonneg (γ₀ : ℝ) (φ : ℝ → ℝ) {L A₀ : ℝ} (hA0 : 0 ≤ A₀) : 0 ≤ restR γ₀ φ L A₀ := by
  unfold restR
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) (sq_nonneg _))
    (Real.exp_pos _).le) (by positivity)) zeta3Sum_nonneg

/-- **COMPONENT 2, f3 UNDER THE TWO NAMED HYPOTHESES:** under H-STRIP and H-COUNT, the rest of the zero sum --
the zeros outside the pair's orbit, with multiplicity -- is at most `restR gamma_0 phi L A0`. -/
theorem rest_bound (Z : Zeta23.ZeroConfig) (γ₀ : ℝ) {φ : ℝ → ℝ} {L A₀ : ℝ} (hφ : ContDiff ℝ 4 φ)
    (hs : Function.support φ ⊆ Set.Icc (-L) L) (hL : 0 ≤ L)
    (hstrip : HStrip Z) (hcount : HCount Z A₀) (ρ₀ : ℂ) :
    restSum Z γ₀ φ ρ₀ ≤ restR γ₀ φ L A₀ :=
  rest_le_of_finite Z γ₀ φ ρ₀ _ (restR_nonneg γ₀ φ (by linarith [hcount.1]))
    (finite_rest_bound Z γ₀ hφ hs hL
      (fun ρ hρ => abs_le.mpr ⟨by linarith [(hstrip ρ hρ).1], by linarith [(hstrip ρ hρ).2]⟩) hcount)

/-- **H-STRIP is not needed:** the closed strip, a field of every `ZeroConfig`, gives the same bound. -/
theorem rest_bound_closed (Z : Zeta23.ZeroConfig) (γ₀ : ℝ) {φ : ℝ → ℝ} {L A₀ : ℝ} (hφ : ContDiff ℝ 4 φ)
    (hs : Function.support φ ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) (hcount : HCount Z A₀) (ρ₀ : ℂ) :
    restSum Z γ₀ φ ρ₀ ≤ restR γ₀ φ L A₀ :=
  rest_le_of_finite Z γ₀ φ ρ₀ _ (restR_nonneg γ₀ φ (by linarith [hcount.1]))
    (finite_rest_bound Z γ₀ hφ hs hL
      (fun ρ hρ => abs_le.mpr ⟨by linarith [(Z.strip ρ hρ).1], by linarith [(Z.strip ρ hρ).2]⟩) hcount)

/-- **For zeta, no hypothesis:** H-COUNT for `zetaZeroConfig` is the kernel's `zetaZeroConfig_local_count`. -/
theorem rest_bound_zeta (γ₀ : ℝ) {φ : ℝ → ℝ} {L : ℝ} (hφ : ContDiff ℝ 4 φ)
    (hs : Function.support φ ⊆ Set.Icc (-L) L) (hL : 0 ≤ L) (ρ₀ : ℂ) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ restSum Zeta23.zetaZeroConfig γ₀ φ ρ₀ ≤ restR γ₀ φ L A₀ := by
  obtain ⟨A₀, h1, h2⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, h1, rest_bound_closed Zeta23.zetaZeroConfig γ₀ hφ hs hL ⟨h1, h2⟩ ρ₀⟩

/-! ### Component 3 -- the exponent comparison -/

theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.mpr (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.mpr (neg_le_abs y)
  linarith

/-- **The pair's growth, bounded:** for `phi >= 0` supported in `[-L, L]` with `INT phi > 0` and `delta >= 0`,
`G = realizedGrowth phi delta <= e^{delta L}`; the pair's term, of order `delta^2 slope^2 G^2`, grows at most like
`e^{2 delta L}`. -/
theorem realizedGrowth_le_exp {φ : ℝ → ℝ} {L δ : ℝ} (hc : Continuous φ) (hs : Function.support φ ⊆ Set.Icc (-L) L)
    (hnn : ∀ x, 0 ≤ φ x) (hpos : 0 < ∫ u, φ u) (hδ : 0 ≤ δ) : realizedGrowth φ δ ≤ Real.exp (δ * L) := by
  have hcs := hasCompactSupport_of_Icc hs
  have i1 : Integrable (fun u => φ u * Real.cosh (δ * u)) :=
    (hc.mul (by fun_prop : Continuous fun u : ℝ => Real.cosh (δ * u))).integrable_of_hasCompactSupport
      (hcs.mul_right (f' := fun u : ℝ => Real.cosh (δ * u)))
  have i2 : Integrable (fun u => φ u * Real.exp (δ * L)) := (hc.integrable_of_hasCompactSupport hcs).mul_const _
  rw [realizedGrowth_eq, div_le_iff₀ hpos]
  unfold nearInt
  calc (∫ u, φ u * Real.cosh (δ * u)) ≤ ∫ u, φ u * Real.exp (δ * L) := by
        refine integral_mono i1 i2 fun u => ?_
        by_cases h0 : φ u = 0
        · simp [h0]
        · have hu : u ∈ Set.Icc (-L) L := hs h0
          have hab : |δ * u| ≤ δ * L := by
            rw [abs_mul, abs_of_nonneg hδ]
            exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hu.1, hu.2⟩) hδ
          exact mul_le_mul_of_nonneg_left
            ((cosh_le_exp_abs _).trans (Real.exp_le_exp.mpr hab)) (hnn u)
    _ = Real.exp (δ * L) * ∫ u, φ u := by rw [integral_mul_const]; ring

/-- **The inequality, as a theorem of real numbers:** `delta < 1/2` gives `2 delta < 1`. -/
theorem two_delta_lt_one (δ : ℝ) (h : δ < 1 / 2) : 2 * δ < 1 := by linarith

/-- **f4_needs:** the rest's allowed growth `e^L` (H-STRIP's, in `restR`) is eventually at most a constant times the
pair's `e^{2 delta L}` -- what f4 needs to close from f2 and f3 alone. -/
def f4_needs (δ : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ, ∀ L ≥ L₀, Real.exp L ≤ C * Real.exp (2 * δ * L)

/-- **Not closable below 1/2:** for `delta < 1/2`, `f4_needs delta` fails. -/
theorem not_f4_needs {δ : ℝ} (hδ : δ < 1 / 2) : ¬ f4_needs δ := by
  rintro ⟨C, hC, L₀, h⟩
  have hk : 0 < 1 - 2 * δ := by linarith
  obtain ⟨L, hL0, hL1⟩ : ∃ L : ℝ, L₀ ≤ L ∧ Real.log C + 1 ≤ (1 - 2 * δ) * L := by
    refine ⟨max L₀ ((Real.log C + 1) / (1 - 2 * δ)), le_max_left _ _, ?_⟩
    have h1 : (Real.log C + 1) / (1 - 2 * δ) ≤ max L₀ ((Real.log C + 1) / (1 - 2 * δ)) := le_max_right _ _
    rw [div_le_iff₀ hk] at h1
    linarith
  have hL := h L hL0
  have h3 : C < Real.exp ((1 - 2 * δ) * L) := by
    rw [← Real.log_lt_iff_lt_exp hC]
    linarith
  have h4 : Real.exp L = Real.exp (2 * δ * L) * Real.exp ((1 - 2 * δ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 : 0 < Real.exp (2 * δ * L) := Real.exp_pos _
  nlinarith [h3, h4, h5, hL]

/-- For `delta >= 1/2` it holds, with `C = 1` from `L = 0`. -/
theorem f4_needs_of_half_le {δ : ℝ} (h : 1 / 2 ≤ δ) : f4_needs δ :=
  ⟨1, one_pos, 0, fun L hL => by
    rw [one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)⟩

/-! ### Component 4 -- f4's remaining need, stated, not proved -/

/-- **H-MAX:** a zero of maximal real part -- the supremum of the real parts of the zeros is attained. A Prop; its
status is UNKNOWN in the kernel and in the record. -/
def HMax (Z : Zeta23.ZeroConfig) : Prop := ∃ ρ ∈ Z.carrier, ∀ ρ' ∈ Z.carrier, ρ'.re ≤ ρ.re

end B321
end SIDEExplicitFormula
