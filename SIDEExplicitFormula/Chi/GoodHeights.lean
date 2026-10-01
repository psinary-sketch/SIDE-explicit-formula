/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/GoodHeights.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/WeilEF/GoodHeights.lean: good heights for `L(·, χ)`, primitive `χ ≠ 1` -- for every `j ≥ 7` a
height `R ∈ [j, j+1]` with `L(s, χ) ≠ 0` and `‖L'/L(s, χ)‖ ≤ C log²(j + 3)` on both horizontal segments `Im s = ±R`,
`1/2 ≤ Re s ≤ 2`, and the consumed re-indexed form. The proof is Zeta23's, carried with `zetaZeroConfig` replaced by
`chiZeroConfig χ hχ h1`, `riemannZeta` by `LFunction χ`, Zeta23's partial fraction and local count by their
χ-analogues (Chi/Landau.lean, Chi/LocalCount.lean); Zeta23's generic lemmas (the pigeonhole `exists_far_point`, the ball
geometry, `Tail`'s window sums) are used from Zeta23 unchanged. Generated from the vendored file by relay
data/b569_gen_goodheights.py.txt. Nothing here proves GRH or locates any zero.
-/
import SIDEExplicitFormula.Chi.Landau
import SIDEExplicitFormula.Chi.LocalCount
import Zeta23.WeilEF.GoodHeights

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open Complex Set Filter Finset DirichletCharacter Zeta23 Zeta23.WeilEF

variable {N : ℕ} [NeZero N]

/-- a zero of `L(·, χ)` in the closed ball of radius r₀ < 2 about 2 + t i is a nontrivial zero. -/
theorem isNontrivialZeroChi_of_mem_closedBall {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {t r : ℝ} (hr : r < 2) {ρ : ℂ}
    (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) (hz : LFunction χ ρ = 0) : IsNontrivialZeroChi χ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have hre : |ρ.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (ρ - (2 + t * I))
    simp at this; linarith
  refine ⟨hz, by rw [abs_le] at hre; linarith, ?_⟩
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hz

/-- a finite set of nontrivial zeros with ordinates in (a, a+6] has total multiplicity
≤ 6 A₀ log(|a|+9) (six unit windows of the local count). -/
theorem sum_mult_six_windows_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {A₀ : ℝ}
    (hLC : Tail.LocalCount (fun ρ : (chiZeroConfig χ hχ hχ1).carrier => (ρ : ℂ).im)
      (fun ρ : (chiZeroConfig χ hχ hχ1).carrier => (chiZeroConfig χ hχ hχ1).mult ρ) A₀)
    {a : ℤ} (F : Finset (chiZeroConfig χ hχ hχ1).carrier)
    (hF : ∀ ρ ∈ F, (a : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + 6) :
    ∑ ρ ∈ F, ((chiZeroConfig χ hχ hχ1).mult ρ : ℝ) ≤ 6 * (A₀ * Real.log (|(a : ℝ)| + 9)) := by
  classical
  have hA₀ := hLC.A₀_pos.le
  -- key k : ℕ with a + k < Im ≤ a + k + 1
  set key : (chiZeroConfig χ hχ hχ1).carrier → ℕ := fun ρ => (⌈(ρ : ℂ).im⌉ - a - 1).toNat with hkey
  have hkey_spec : ∀ ρ ∈ F, ((a : ℝ) + key ρ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + key ρ + 1)
      ∧ key ρ < 6 := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ
    have hc1 := Int.le_ceil (ρ : ℂ).im
    have hc2 := Int.ceil_lt_add_one (ρ : ℂ).im
    have hlo : a + 1 ≤ ⌈(ρ : ℂ).im⌉ := by
      have : (a : ℝ) < ⌈(ρ : ℂ).im⌉ := lt_of_lt_of_le h1 hc1
      have : a < ⌈(ρ : ℂ).im⌉ := by exact_mod_cast this
      omega
    have hhi : ⌈(ρ : ℂ).im⌉ ≤ a + 6 := by
      have : (⌈(ρ : ℂ).im⌉ : ℝ) < (a : ℝ) + 6 + 1 := by linarith
      have : ⌈(ρ : ℂ).im⌉ < a + 6 + 1 := by exact_mod_cast this
      omega
    have hk : ((key ρ : ℕ) : ℤ) = ⌈(ρ : ℂ).im⌉ - a - 1 := by
      simp only [hkey]; rw [Int.toNat_of_nonneg (by omega)]
    have hkR : ((key ρ : ℕ) : ℝ) = (⌈(ρ : ℂ).im⌉ : ℝ) - a - 1 := by exact_mod_cast hk
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have : ((key ρ : ℕ) : ℤ) < 6 := by omega
    exact_mod_cast this
  have h := Tail.sum_mult_le_of_windows F (fun ρ => (chiZeroConfig χ hχ hχ1).mult ρ) key 6
    (C := A₀ * Real.log (|(a : ℝ)| + 9)) (fun ρ hρ => (hkey_spec ρ hρ).2) (fun k hk => by
      have hw := hLC.window ((a : ℝ) + k) (F.filter fun ρ => key ρ = k) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        have := (hkey_spec ρ hρ.1).1
        rw [hρ.2] at this; exact this)
      refine hw.trans (mul_le_mul_of_nonneg_left ?_ hA₀)
      apply Real.log_le_log (by positivity)
      have : |(a : ℝ) + k| ≤ |(a : ℝ)| + k := by
        calc |(a:ℝ) + k| ≤ |(a:ℝ)| + |(k:ℝ)| := abs_add_le _ _
          _ = |(a:ℝ)| + k := by rw [Nat.abs_cast]
      have hk6 : (k : ℝ) < 6 := by exact_mod_cast hk
      linarith)
  simpa using h

/-- card ≤ total multiplicity (each nontrivial zero has multiplicity ≥ 1). -/
theorem card_le_sum_mult_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (F : Finset (chiZeroConfig χ hχ hχ1).carrier) :
    (F.card : ℝ) ≤ ∑ ρ ∈ F, ((chiZeroConfig χ hχ hχ1).mult ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  exact_mod_cast (chiZeroConfig χ hχ hχ1).one_le_mult ρ ρ.2

/-! ### good heights -/

/-- **Good heights**: for every j ≥ 7 there is R ∈ [j, j+1] such that on both horizontal segments
Im s = ±R, 1/2 ≤ Re s ≤ 2, ζ(s) ≠ 0 and ‖ζ'/ζ(s)‖ ≤ C log²(j+3)  (R avoids the ordinates of all
zeros with |Im ρ ∓ R| < 2 by at least 1/(2(n+1)), n ≪ log j their number; then the partial
fraction ζ'/ζ(s) = Σ_{|ρ−(2±iR)| ≤ 1.6} m_ρ/(s−ρ) + O(log) with Σ m_ρ ≪ log). -/
theorem good_heights_at_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      (LFunction χ) s ≠ 0 ∧ ‖logDeriv (LFunction χ) s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  obtain ⟨C, hC, hpf⟩ := LFunction_logDeriv_partial_fraction hχ1
  obtain ⟨A₀, hA₀, hloc⟩ := chiZeroConfig_local_count hχ hχ1
  have hLC := Tail.LocalCount.ofWindowCount (chiZeroConfig χ hχ hχ1) hA₀ hloc
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, fun j hj => ?_⟩
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  set Lg : ℝ := Real.log ((j : ℝ) + 3) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog2 : Real.log 2 ≤ Lg := by
    rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  -- the two finite families of zeros near height ±j
  set Wp : Set ℂ := (chiZeroConfig χ hχ hχ1).window ((j : ℝ) - 3) ((j : ℝ) + 3) with hWp
  set Wm : Set ℂ := (chiZeroConfig χ hχ hχ1).window (-(j : ℝ) - 4) (-(j : ℝ) + 2) with hWm
  have hWpfin : ((fun ρ : (chiZeroConfig χ hχ hχ1).carrier => (ρ : ℂ)) ⁻¹' Wp).Finite :=
    ((chiZeroConfig χ hχ hχ1).finite_window _ _).preimage Subtype.val_injective.injOn
  have hWmfin : ((fun ρ : (chiZeroConfig χ hχ hχ1).carrier => (ρ : ℂ)) ⁻¹' Wm).Finite :=
    ((chiZeroConfig χ hχ hχ1).finite_window _ _).preimage Subtype.val_injective.injOn
  set Fp : Finset (chiZeroConfig χ hχ hχ1).carrier := hWpfin.toFinset with hFp
  set Fm : Finset (chiZeroConfig χ hχ hχ1).carrier := hWmfin.toFinset with hFm
  have hFp_mem : ∀ ρ : (chiZeroConfig χ hχ hχ1).carrier, ρ ∈ Fp ↔ (ρ : ℂ) ∈ Wp := fun ρ => by
    rw [hFp, Set.Finite.mem_toFinset]; rfl
  have hFm_mem : ∀ ρ : (chiZeroConfig χ hχ hχ1).carrier, ρ ∈ Fm ↔ (ρ : ℂ) ∈ Wm := fun ρ => by
    rw [hFm, Set.Finite.mem_toFinset]; rfl
  set S : Finset ℝ := Fp.image (fun ρ : (chiZeroConfig χ hχ hχ1).carrier => (ρ : ℂ).im)
    ∪ Fm.image (fun ρ : (chiZeroConfig χ hχ hχ1).carrier => -(ρ : ℂ).im) with hS
  -- count: |S| ≤ 24 A₀ Lg
  have hcountp : ∑ ρ ∈ Fp, ((chiZeroConfig χ hχ hχ1).mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows_chi hχ hχ1 hLC (a := (j : ℤ) - 3) Fp (fun ρ hρ => by
      have := ((hFp_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |((j : ℤ) - 3 : ℤ)| = (j : ℤ) - 3 := abs_of_nonneg (by omega)
      have habs : |(((j:ℤ) - 3 : ℤ) : ℝ)| = (j : ℝ) - 3 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) - 3 + 9) ≤ Real.log (2 * ((j:ℝ) + 3)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 * Lg := by linarith
  have hcountm : ∑ ρ ∈ Fm, ((chiZeroConfig χ hχ hχ1).mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows_chi hχ hχ1 hLC (a := -(j : ℤ) - 4) Fm (fun ρ hρ => by
      have := ((hFm_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |(-(j : ℤ) - 4 : ℤ)| = (j : ℤ) + 4 := by
        rw [abs_of_nonpos (by omega)]; ring
      have habs : |((-(j:ℤ) - 4 : ℤ) : ℝ)| = (j : ℝ) + 4 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) + 4 + 9) ≤ Real.log (((j:ℝ) + 3) ^ 2) := by
            apply Real.log_le_log (by linarith); nlinarith
        _ = 2 * Lg := by rw [Real.log_pow]; push_cast; ring
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ Fp.card + Fm.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ Fp.card + Fm.card := by exact_mod_cast h1
    linarith [card_le_sum_mult_chi hχ hχ1 Fp, card_le_sum_mult_chi hχ hχ1 Fm]
  -- the good height
  obtain ⟨R, hR1, hR2, hfar⟩ := exists_far_point S j
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, fun s hs hσ1 hσ2 => ?_⟩
  have hR6 : (6 : ℝ) ≤ |R| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hR6' : (6 : ℝ) ≤ |-R| := by rwa [abs_neg]
  have hlogR : Real.log (|R| + 3) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  -- s in the conclusion ball of the partial fraction at t = s.im
  have hsball : s ∈ Metric.closedBall (2 + s.im * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- every zero in the pf ball at height s.im = ±R has its (signed) ordinate in S
  have hordS : ∀ ρ : ℂ, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) →
      (LFunction χ) ρ = 0 → δ ≤ ‖s - ρ‖ := by
    intro ρ hρ hz
    have hnt := isNontrivialZeroChi_of_mem_closedBall hχ1 (by norm_num) hρ hz
    have him := im_mem_of_mem_closedBall hρ
    rw [abs_le] at him
    have hρc : ρ ∈ (chiZeroConfig χ hχ hχ1).carrier := by rw [chiZeroConfig_carrier]; exact hnt
    refine le_trans ?_ (abs_im_sub_le_norm_sub s ρ)
    rcases hs with hsR | hsR
    · -- Im ρ ∈ S via Fp
      have hmem : (⟨ρ, hρc⟩ : (chiZeroConfig χ hχ hχ1).carrier) ∈ Fp := by
        rw [hFp_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : (chiZeroConfig χ hχ hχ1).carrier), hmem, rfl⟩
      have := hfar _ this
      rwa [hsR]
    · have hmem : (⟨ρ, hρc⟩ : (chiZeroConfig χ hχ hχ1).carrier) ∈ Fm := by
        rw [hFm_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : -ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : (chiZeroConfig χ hχ hχ1).carrier), hmem, rfl⟩
      have := hfar _ this
      rw [hsR, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  -- ζ(s) ≠ 0: s itself would be a zero in the ball at distance 0
  have hζ : (LFunction χ) s ≠ 0 := by
    intro hz
    have h0 := hordS s (Metric.closedBall_subset_closedBall (by norm_num) hsball) hz
    simp at h0; linarith
  refine ⟨hζ, ?_⟩
  -- apply the partial fraction at t := s.im
  have ht6 : (6 : ℝ) ≤ |s.im| := by rcases hs with h | h <;> rw [h] <;> assumption
  obtain ⟨Z, hZ, hZsum, hZpf⟩ := hpf s.im ht6
  have hZpf' := hZpf s hsball hζ
  have hlogt : Real.log (|s.im| + 3) ≤ 2 * Lg := by
    rcases hs with h | h
    · rw [h]; exact hlogR
    · rw [h, abs_neg]; exact hlogR
  -- the sum over Z
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) ∧ (LFunction χ) ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at this
    exact this
  have hsumZ : ‖∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℂ) / (s - ρ)‖
      ≤ (C * (2 * Lg)) * (1 / δ) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt (LFunction χ) ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℝ) * (1 / δ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρb, hρz⟩ := hZmem ρ hρ
          have hd := hordS ρ hρb hρz
          have hsρ : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδpos hd
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
      _ ≤ (C * (2 * Lg)) * (1 / δ) := by
          refine mul_le_mul_of_nonneg_right (hZsum.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hlogt hC.le
  -- assemble
  have hmain : ‖logDeriv (LFunction χ) s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
    have h1 : ‖logDeriv (LFunction χ) s‖
        ≤ ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt (LFunction χ) ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    have h2 := hZpf'.trans (mul_le_mul_of_nonneg_left hlogt hC.le)
    linarith [hsumZ]
  refine hmain.trans ?_
  rw [hδinv]
  have hc := hcard
  have hA := hLC.A₀_pos.le
  -- C·2Lg·(1 + 2(n+1)) ≤ 2C(48A₀+3) Lg²
  have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
      = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
  rw [this]
  have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
  calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * C * (48 * A₀ + 3) * Real.log ((j : ℝ) + 3) ^ 2 := by rw [hLg]; ring

/-- **Good heights**, in the consumed shape: a height function `R_j ∈ [j+7, j+8]` (all `j : ℕ`) with
ζ ≠ 0 and `‖ζ'/ζ‖ ≤ C_g log²(j+10)` on both horizontal lines `im = ±R_j`, `1/2 ≤ re ≤ 2`
(`good_heights_at` re-indexed by `j ↦ j + 7` and a choice function). -/
theorem good_heights_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : ∃ Cg : ℝ, 0 < Cg ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
    (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
    ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      (LFunction χ) s ≠ 0 ∧ ‖logDeriv (LFunction χ) s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := good_heights_at_chi hχ hχ1
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + 7 : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + 7 : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
        (LFunction χ) s ≠ 0 ∧ ‖logDeriv (LFunction χ) s‖ ≤ C * (Real.log (((j + 7 : ℕ) : ℝ) + 3)) ^ 2 :=
    fun j => h (j + 7) (by omega)
  refine ⟨C, hC, fun j => (hex j).choose, fun j => ?_⟩
  dsimp only
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + 7 : ℕ) : ℝ) = (j : ℝ) + 7 := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · calc (j : ℝ) + 7 = ((j + 7 : ℕ) : ℝ) := e.symm
      _ ≤ _ := hs1
  · exact hs2.trans (by rw [e]; linarith)
  · intro s him h1 h2
    have e3 : Real.log (((j + 7 : ℕ) : ℝ) + 3) = Real.log ((j : ℝ) + 10) := by rw [e]; ring_nf
    obtain ⟨h3, h4⟩ := hs3 s him h1 h2
    exact ⟨h3, by rwa [e3] at h4⟩

end GRHWeil
end SIDEExplicitFormula
