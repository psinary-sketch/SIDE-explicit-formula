/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/Contour.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt rows E7 E8, group D) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE RECTANGLE AND ITS HORIZONTALS. E7: `(1/2πi)∮ H·Λ'/Λ = Σ_{|γ_ρ| < R} m_ρ H(ρ) − H(0) − H(1)` over `[−1/2, 3/2] × [−R, R]`, Zeta23/WeilEF/Contour.lean's proof, the poles of `lamQ` at `0` and `1` simple with
residues `−1` and `1` read from `lamQ_eq`. Break points (1), (3), (5): the right edge is `c = 3/2` exactly, the configuration open at it and `lamQ` free of zeros on it; a point of the configuration can lie
right of any smaller `c`, so the identity is stated at `3/2` alone; two poles, as for `ζ`; the orders are the configuration's multiplicities by `analyticOrderNatAt_lamQ`, and the trivial zero at `−1` lies outside the rectangle.
E8: the horizontals vanish along the good heights, Chi/Horizontal.lean's majorant, the left half by E3. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.Heights

open Complex Topology Filter Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

open Zeta23 Zeta23.WeilEF

/-- The residue of `lamQ` at `0`. -/
theorem lamQ_residue_zero :
    Tendsto (fun s : ℂ => (s - 0) ^ (1 : ℕ) * lamQ s) (nhdsWithin 0 {0}ᶜ) (𝓝 (-1)) := by
  have hc : ContinuousAt (fun s : ℂ => s * zqPair.Λ₀ s - 1 - s / (1 - s)) 0 := by
    have h1 : ContinuousAt zqPair.Λ₀ 0 := zqPair.differentiable_Λ₀.continuous.continuousAt
    exact ((continuousAt_id.mul h1).sub continuousAt_const).sub
      (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by simp))
  have h0 : (fun s : ℂ => s * zqPair.Λ₀ s - 1 - s / (1 - s)) 0 = -1 := by simp
  have ht := hc.tendsto
  rw [h0] at ht
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  have e : s * (1 / s) = 1 := mul_one_div_cancel hs0
  rw [lamQ_eq, sub_zero, pow_one]
  linear_combination e

/-- The residue of `lamQ` at `1`. -/
theorem lamQ_residue_one :
    Tendsto (fun s : ℂ => (s - 1) ^ (1 : ℕ) * lamQ s) (nhdsWithin 1 {1}ᶜ) (𝓝 1) := by
  have hc : ContinuousAt (fun s : ℂ => (s - 1) * zqPair.Λ₀ s - (s - 1) / s + 1) 1 := by
    have h1 : ContinuousAt zqPair.Λ₀ 1 := zqPair.differentiable_Λ₀.continuous.continuousAt
    have h2 : ContinuousAt (fun s : ℂ => s - 1) 1 := continuousAt_id.sub continuousAt_const
    exact ((h2.mul h1).sub (h2.div continuousAt_id (by simp))).add continuousAt_const
  have h0 : (fun s : ℂ => (s - 1) * zqPair.Λ₀ s - (s - 1) / s + 1) 1 = 1 := by simp
  have ht := hc.tendsto
  rw [h0] at ht
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have e : (1 - s) * (1 / (1 - s)) = 1 := mul_one_div_cancel (sub_ne_zero.mpr hs1.symm)
  rw [lamQ_eq, pow_one]
  linear_combination -e

theorem Hfn_differentiable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) : Differentiable ℂ (Hfn k) := by
  unfold Hfn
  exact (differentiable_paperFT hk.continuous hkc).comp ((differentiable_id.sub_const _).div_const _)

theorem mem_C {ρ : ℂ} (h : ρ ∈ zqZeroConfig.carrier) : ρ ≠ 0 ∧ ρ ≠ 1 := by
  have h' : ρ ≠ 0 ∧ ρ ≠ 1 ∧ (∀ n : ℕ, ρ ≠ -((n : ℂ) + 1)) ∧ zqFn ρ = 0 := h
  exact ⟨h'.1, h'.2.1⟩

/-- **E7. The rectangle identity for `lamQ`**, at `c = 3/2`, at a height free of zeros of `lamQ` on the horizontal sides. -/
theorem zq_rectangle_identity {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc : c = 3 / 2) {R : ℝ} (hR : 7 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → lamQ s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ zqZeroConfig.carrier ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv lamQ s)
          ((1 - c : ℝ) - R * I) ((c : ℝ) + R * I)
        = (∑ ρ ∈ Z, (zqZeroConfig.mult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
  classical
  set z : ℂ := (1 - c : ℝ) - R * I with hzdef
  set w : ℂ := (c : ℝ) + R * I with hwdef
  have hzre : z.re = 1 - c := by simp [hzdef]
  have hzim : z.im = -R := by simp [hzdef]
  have hwre : w.re = c := by simp [hwdef]
  have hwim : w.im = R := by simp [hwdef]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
    intro s
    simp only [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  set P : Finset ℂ := {0, 1} with hPdef
  have hfin := zqZeroConfig.finite_window (-R) R
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmemiff : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ zqZeroConfig.carrier ∧ -R < ρ.im ∧ ρ.im ≤ R) := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hstrip : ∀ ρ ∈ zqZeroConfig.carrier, -1 / 2 < ρ.re ∧ ρ.re < 3 / 2 := zqZeroConfig.strip
  have hzero : ∀ ρ ∈ zqZeroConfig.carrier, lamQ ρ = 0 := fun ρ h =>
    (lamQ_eq_zero_iff (mem_C h).1 (mem_C h).2.1 (hstrip ρ h).1).mpr h
  have hZcoe : (Z : Set ℂ) = {ρ : ℂ | ρ ∈ zqZeroConfig.carrier ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, hZmemiff]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, lt_of_le_of_ne h3 ?_⟩
      intro h
      exact hgood ρ (Or.inl h) (by linarith [(hstrip ρ h1).1]) (by linarith [(hstrip ρ h1).2]) (hzero ρ h1)
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.le⟩
  refine ⟨Z, hZcoe, ?_⟩
  have hZP : Disjoint Z P := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρP
    have h1 := ((hZmemiff ρ).mp hρ).1
    rw [hPdef] at hρP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρP
    rcases hρP with rfl | rfl
    · exact (mem_C h1).1 rfl
    · exact (mem_C h1).2.1 rfl
  have hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him,
      hzre, hzim, hwre, hwim]
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · constructor
      · simp only [Complex.zero_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.zero_im, Set.mem_Ioo]
        constructor <;> linarith
    · constructor
      · simp only [Complex.one_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.one_im, Set.mem_Ioo]
        constructor <;> linarith
  have hf : AnalyticOnNhd ℂ lamQ (Rectangle z w \ (P : Set ℂ)) := by
    rintro s ⟨_, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    exact lamQ_analyticAt hsP.1 hsP.2
  have hg : AnalyticOnNhd ℂ (Hfn k) (Rectangle z w) := fun s _ => (Hfn_differentiable hk hkc).analyticAt s
  have hborder : ∀ s ∈ RectangleBorder z w, lamQ s ≠ 0 := by
    intro s hs h0
    have hsrect := rectangleBorder_subset_rectangle z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood s (Or.inr h') hr1 hr2 h0
    · exact lamQ_ne_zero_of_re_le (by rw [h']; linarith) h0
    · exact hgood s (Or.inl h') hr1 hr2 h0
    · exact lamQ_ne_zero_of_three_halves_le (by rw [h']; linarith) h0
  have hZchar : ∀ s ∈ Rectangle z w \ (P : Set ℂ), (lamQ s = 0 ↔ s ∈ Z) := by
    rintro s ⟨hsrect, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    rw [hZmemiff]
    constructor
    · intro h0
      have hgt : -1 / 2 < s.re := by
        by_contra hle
        exact lamQ_ne_zero_of_re_le (not_lt.mp hle) h0
      have hnz : s ∈ zqZeroConfig.carrier := (lamQ_eq_zero_iff hsP.1 hsP.2 hgt).mp h0
      refine ⟨hnz, ?_, hi2⟩
      rcases lt_or_eq_of_le hi1 with h | h
      · exact h
      · exact absurd h0 (hgood s (Or.inr h.symm) hr1 hr2)
    · rintro ⟨h1, _, _⟩
      exact hzero s h1
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro ρ hρ
    rw [Finset.mem_coe, hZmemiff] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [(hstrip ρ h1).1], by linarith [(hstrip ρ h1).2]⟩, h2.le, h3⟩
  have hpole : ∀ p ∈ P, ∃ cp : ℂ, cp ≠ 0 ∧
      Filter.Tendsto (fun s => (s - p) ^ (1 : ℕ) * lamQ s)
        (nhdsWithin p {p}ᶜ) (nhds cp) := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨-1, by norm_num, lamQ_residue_zero⟩
    · exact ⟨1, one_ne_zero, lamQ_residue_one⟩
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv_of_poles hre him Z P hZP hPint hf hg
    hborder hZchar hZsub (fun _ => 1) hpole
  rw [key]
  have hord : ∀ ρ ∈ Z, (analyticOrderNatAt lamQ ρ : ℂ) = (zqZeroConfig.mult ρ : ℂ) := by
    intro ρ hρ
    rw [analyticOrderNatAt_lamQ ((hZmemiff ρ).mp hρ).1]
  have hPsum : ∑ p ∈ P, ((1 : ℕ) : ℂ) * Hfn k p = Hfn k 0 + Hfn k 1 := by
    rw [hPdef, Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hord ρ hρ]), hPsum]
  ring

/-- **E8. The horizontal sides vanish** along the good heights. -/
theorem zq_horizontal_vanish {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc : c = 3 / 2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 2 →
        zqFn s ≠ 0 ∧ ‖logDeriv zqFn s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv lamQ s) (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv lamQ s) (1 - c) c (-(R j))) atTop (𝓝 0) := by
  have hc1 : 1 < c := by linarith
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  obtain ⟨CG, hCG, hψ⟩ := GRHWeil.digamma_growth_strip_wide
  set Lg : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 10) with hLgdef
  have hLg1 : ∀ j : ℕ, 1 ≤ Lg j := fun j => by
    rw [hLgdef, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  set CL : ℝ := ‖(Real.log lam : ℂ)‖ with hCL
  have hCL0 : 0 ≤ CL := norm_nonneg _
  set K : ℝ := CL + CG + Cg with hKdef
  have hK0 : 0 < K := by linarith
  -- the good horizontals, |im| ∈ [j+7, j+8]
  have him8 : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → Real.log (2 + |s.im|) ≤ Lg j := by
    intro j s hsim
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hRj0 : 0 ≤ R j := by linarith
    have h8 : |s.im| ≤ (j : ℝ) + 8 := by
      rcases hsim with h | h
      · rw [h, abs_of_nonneg hRj0]; exact hR2
      · rw [h, abs_neg, abs_of_nonneg hRj0]; exact hR2
    rw [hLgdef]
    exact Real.log_le_log (by positivity) (by linarith)
  -- the right half
  have hright : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖logDeriv lamQ s‖ ≤ K * (Lg j) ^ 2 := by
    intro j s hsim hre1 hre2
    obtain ⟨hL, hLb⟩ := (hR j).2.2 s hsim hre1 (by linarith)
    have hRpos : 0 < R j := by linarith [(hR j).1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hs1 : s ≠ 1 := fun e => by
      rw [e, Complex.one_im] at hsim
      rcases hsim with h | h <;> linarith
    rw [logDeriv_lamQ (by linarith) hs1 hL]
    have hLg := hLg1 j
    have hone : (1 : ℝ) ≤ Lg j ^ 2 := by nlinarith
    have hLg2 : Lg j ≤ Lg j ^ 2 := by nlinarith
    have hpsi : ‖Complex.digamma s‖ ≤ CG * Lg j ^ 2 :=
      calc ‖Complex.digamma s‖ ≤ CG * Real.log (2 + |s.im|) := hψ s (by linarith) (by linarith)
        _ ≤ CG * Lg j ^ 2 := mul_le_mul_of_nonneg_left ((him8 j s hsim).trans hLg2) hCG.le
    calc ‖-(Real.log lam : ℂ) + Complex.digamma s + logDeriv zqFn s‖
        ≤ ‖-(Real.log lam : ℂ)‖ + ‖Complex.digamma s‖ + ‖logDeriv zqFn s‖ := norm_add₃_le
      _ ≤ CL * Lg j ^ 2 + CG * Lg j ^ 2 + Cg * Lg j ^ 2 := by
          refine add_le_add (add_le_add ?_ hpsi) hLb
          rw [norm_neg]
          exact le_mul_of_one_le_right hCL0 hone
      _ = K * Lg j ^ 2 := by rw [hKdef]; ring
  -- the same bound on the whole horizontal segment x ∈ [1-c, c], by E3 for x < 1/2
  have hall : ∀ (j : ℕ) (x y : ℝ), (y = R j ∨ y = -R j) → 1 - c ≤ x → x ≤ c →
      ‖logDeriv lamQ ((x : ℂ) + y * I)‖ ≤ K * (Lg j) ^ 2 := by
    intro j x y hy hx1 hx2
    rcases le_or_gt (1 / 2 : ℝ) x with hx | hx
    · exact hright j _ (by rcases hy with h | h <;> simp [h]) (by simpa using hx) (by simp; linarith)
    · -- reflect: s = 1 − s', s' := (1 − x) − y i on the opposite good horizontal
      set s' : ℂ := ((1 - x : ℝ) : ℂ) + (-y) * I with hs'def
      have him' : s'.im = -y := by simp [hs'def]
      have hre' : s'.re = 1 - x := by simp [hs'def]
      have hs'h : s'.im = R j ∨ s'.im = -R j := by
        rw [him']
        rcases hy with h | h
        · right; rw [h]
        · left; rw [h, neg_neg]
      have hb := hright j s' hs'h (by rw [hre']; linarith) (by rw [hre']; linarith)
      have hRpos : 0 < R j := by linarith [(hR j).1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hne : s' ≠ 0 := fun e => by
        have h0 : s'.re = 0 := by rw [e, Complex.zero_re]
        linarith
      have hne1 : s' ≠ 1 := fun e => by
        rw [e, Complex.one_im] at hs'h
        rcases hs'h with h | h <;> linarith
      have e : ((x : ℂ) + y * I) = 1 - s' := by
        simp only [hs'def]; push_cast; ring
      rw [e, logDeriv_lamQ_one_sub hne hne1, norm_neg]
      exact hb
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * logDeriv lamQ s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    exact mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2]))
      (hall j x y hy hx.1.le hx.2) (norm_nonneg _) (by positivity)
  -- the majorant tends to 0
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hLg_sq : ∀ j : ℕ, Lg j ^ 2 ≤ 4 * ((j : ℝ) + 10) := fun j => by
    have hy0 : (0 : ℝ) ≤ (j : ℝ) + 10 := by positivity
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1/2)
    have hsq : (((j : ℝ) + 10) ^ (1/2 : ℝ)) ^ 2 = (j : ℝ) + 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    have h0 : 0 ≤ Lg j := (zero_le_one.trans (hLg1 j))
    calc Lg j ^ 2 ≤ (((j : ℝ) + 10) ^ (1/2 : ℝ) / (1/2)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 * ((j : ℝ) + 10) := by rw [div_pow, hsq]; ring
  have hb_le : ∀ j : ℕ, b j ≤ (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7) := fun j => by
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1' : Lg j ^ 2 / (1 + R j ^ 2) ≤ 8 / ((j : ℝ) + 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR7 : ((j : ℝ) + 7) ^ 2 ≤ R j ^ 2 := pow_le_pow_left₀ (by positivity) hR1 2
      nlinarith [hLg_sq j, hR7, mul_le_mul_of_nonneg_right (hLg_sq j) (show (0:ℝ) ≤ (j:ℝ) + 7 by positivity),
        sq_nonneg ((j:ℝ) + 7)]
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by
      rw [hbdef]; ring
    rw [e]
    calc CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2))
        ≤ CH * K * |c - (1 - c)| * (8 / ((j : ℝ) + 7)) :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = 8 * CH * K * |c - (1 - c)| / ((j : ℝ) + 7) := by ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

end EF
end ZQ
end Schema
end SIDEExplicitFormula
