/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/Count.lean
THIS PROGRAMME'S WORK (act b733, ruling (R343)(3), relay data/b733_count_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE count FIELD. `N(t, t+1] ≤ A₀ log(|t| + 3)` for the zeros of `Λ_Q` with multiplicity, Chi/LocalCount.lean's route on the entire `aE`:
* count only the zeros with `Re ρ ≥ 1/2` and double, Zeta23/RvM/Halving.lean's proof over `WideConfig`;
* the ported `ZerosBound` on `g(z) := aE(c₀ + 1.3 z) / aE(c₀)`, `c₀ := 3/2 + (t + ½)i`, `r = 0.87`, `R = 0.95`, its order at `z` the order of `Z_Q` at `c₀ + 1.3 z`;
* `aE` has no pole, so the disc holds at every `t` and no small-height constant is needed.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.Growth
import Zeta23.Prelude.InstancePriorities
import Zeta23.FromPNTPlus.StrongPNTPrefix
import Zeta23.RvM.Halving

open Complex Set Filter Topology Metric

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ

open Zeta23

/-! ### The halving over `WideConfig` -/

/-- Monotonicity of `Σ m_ρ` over finite subsets of a window (Zeta23/Defs/Counting.lean :51's proof over the widened class). -/
theorem wide_finsum_mult_mono (Z : WideConfig) (T₁ T₂ : ℝ) {s t : Set ℂ} (hst : s ⊆ t)
    (ht : t ⊆ Wide.window Z T₁ T₂) : ∑ᶠ ρ ∈ s, Z.mult ρ ≤ ∑ᶠ ρ ∈ t, Z.mult ρ := by
  have hW : (Wide.window Z T₁ T₂).Finite := Z.finite_window T₁ T₂
  have htf : t.Finite := hW.subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf, finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst

/-- **Reflection halving** (Zeta23/RvM/Halving.lean :59's proof over the widened class). -/
theorem wide_N_le_two_mul_half (Z : WideConfig) (T₁ T₂ : ℝ) :
    (Wide.N Z T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Wide.window Z T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ) := by
  have hW : (Wide.window Z T₁ T₂).Finite := Z.finite_window T₁ T₂
  set A := Wide.window Z T₁ T₂ ∩ {ρ | ρ.re < 1 / 2} with hAdef
  set B := Wide.window Z T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re} with hBdef
  have hA : A.Finite := hW.subset inter_subset_left
  have hB : B.Finite := hW.subset inter_subset_left
  have hWAB : Wide.window Z T₁ T₂ = A ∪ B := by
    ext ρ
    simp only [hAdef, hBdef, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      rcases lt_or_ge ρ.re (1 / 2) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hN : Wide.N Z T₁ T₂ = ∑ᶠ ρ ∈ A, Z.mult ρ + ∑ᶠ ρ ∈ B, Z.mult ρ := by
    unfold Wide.N
    rw [hWAB, finsum_mem_union hdisj hA hB]
  have himage : reflect '' A ⊆ B := by
    rintro _ ⟨ρ, ⟨hρW, hlt⟩, rfl⟩
    refine ⟨⟨Z.reflect_mem ρ hρW.1, by simpa [reflect_im] using hρW.2⟩, ?_⟩
    simp only [mem_setOf_eq, reflect_re] at hlt ⊢
    linarith
  have hAB : ∑ᶠ ρ ∈ A, Z.mult ρ ≤ ∑ᶠ ρ ∈ B, Z.mult ρ := by
    calc ∑ᶠ ρ ∈ A, Z.mult ρ = ∑ᶠ ρ ∈ A, Z.mult (reflect ρ) :=
          finsum_mem_congr rfl (fun ρ hρ => (Z.mult_reflect ρ hρ.1.1).symm)
      _ = ∑ᶠ σ ∈ reflect '' A, Z.mult σ := (finsum_mem_image reflect_injective.injOn).symm
      _ ≤ ∑ᶠ σ ∈ B, Z.mult σ := wide_finsum_mult_mono Z T₁ T₂ himage inter_subset_left
  have hcast : (∑ᶠ ρ ∈ B, (Z.mult ρ : ℝ)) = ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Nat.cast_sum]
  rw [hcast, hN]
  have hAB' : ((∑ᶠ ρ ∈ A, Z.mult ρ : ℕ) : ℝ) ≤ ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    exact_mod_cast hAB
  push_cast
  linarith

/-! ### Orders -/

/-- Off `1`, `aE` and `zqFn` have one order. -/
theorem aE_order_eq {ρ : ℂ} (h1 : ρ ≠ 1) : analyticOrderAt aE ρ = analyticOrderAt zqFn ρ := by
  have hA : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hZ := zq_analyticAt h1
  have hev : aE =ᶠ[𝓝 ρ] (fun s : ℂ => 1 - s) * zqFn := by
    filter_upwards [isOpen_ne.mem_nhds h1] with s hs
    exact aE_eq hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hA hZ]
  have h0 : analyticOrderAt (fun s : ℂ => 1 - s) ρ = 0 :=
    hA.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h1.symm)
  rw [h0, zero_add]

theorem aE_orderNat_eq {ρ : ℂ} (h1 : ρ ≠ 1) : analyticOrderNatAt aE ρ = analyticOrderNatAt zqFn ρ := by
  unfold analyticOrderNatAt
  rw [aE_order_eq h1]

/-- The rescaled function `g(z) := aE(c₀ + κ z) · u`. -/
def gQ (c₀ κ u z : ℂ) : ℂ := aE (c₀ + κ * z) * u

theorem comp_affine_aE (c₀ κ z : ℂ) : AnalyticAt ℂ (fun z : ℂ => aE (c₀ + κ * z)) z := by
  have hL : AnalyticAt ℂ aE (c₀ + κ * z) := aE_differentiable.analyticAt _
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) z := by fun_prop
  exact hL.comp_of_eq haff rfl

theorem gQ_analyticAt (c₀ κ u z : ℂ) : AnalyticAt ℂ (gQ c₀ κ u) z :=
  (comp_affine_aE c₀ κ z).mul analyticAt_const

/-- Order transport: the order of `g` at `w` is the order of `aE` at `c₀ + κ w`. -/
theorem analyticOrderNatAt_gQ {c₀ κ u w : ℂ} (hκ : κ ≠ 0) (hu : u ≠ 0) :
    analyticOrderNatAt (gQ c₀ κ u) w = analyticOrderNatAt aE (c₀ + κ * w) := by
  unfold analyticOrderNatAt gQ
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => aE (c₀ + κ * z)) w := comp_affine_aE c₀ κ w
  have hmul : (fun z ↦ aE (c₀ + κ * z) * u) = (fun z => aE (c₀ + κ * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => c₀ + κ * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hκ
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := aE) haff hderiv
  simpa [Function.comp_def] using this

/-! ### The disc -/

theorem centre_re (t : ℝ) : (((3 / 2 : ℝ) : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I).re = 3 / 2 := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem centre_im (t : ℝ) : (((3 / 2 : ℝ) : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I).im = t + 1 / 2 := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem kappa_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem kappa_im (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `|aE| ≥ (4 − Z_Q(3/2)) / 2` on the line `Re c = 3/2`. -/
theorem aE_lower {c : ℂ} (hc : c.re = 3 / 2) : (4 - totQ) / 2 ≤ ‖aE c‖ := by
  have hc1 : c ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hc
    norm_num at hc
  have hZ : 4 - totQ ≤ ‖zqFn c‖ := zq_norm_ge hc.ge
  have hT := totQ_lt
  have hrez : (1 - c).re = -(1 / 2) := by
    rw [Complex.sub_re, Complex.one_re, hc]
    norm_num
  have h5 : (1 / 2 : ℝ) ≤ ‖1 - c‖ := by
    have h := Complex.abs_re_le_norm (1 - c)
    rwa [hrez, abs_neg, abs_of_pos (by norm_num)] at h
  rw [aE_eq hc1, norm_mul]
  calc (4 - totQ) / 2 = 1 / 2 * (4 - totQ) := by ring
    _ ≤ ‖1 - c‖ * ‖zqFn c‖ := mul_le_mul h5 hZ (by linarith) (norm_nonneg _)

/-- Zeros with `Re ρ ≥ 1/2` in the window `(t, t+1]`, with multiplicity, as a real number. -/
def NhalfQ (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ Wide.window zqZeroConfig t (t + 1) ∩ {ρ | 1 / 2 ≤ ρ.re}, (zqZeroConfig.mult ρ : ℝ)

/-- **THE DISC**: the `Re ρ ≥ 1/2` half-window count is `≪ log(|t| + 3)` at every `t`. -/
theorem halfQ_count : ∃ A₁ : ℝ, ∀ t : ℝ, NhalfQ t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨M, hM0, hgrowth⟩ := aE_growth
  set δ : ℝ := (4 - totQ) / 2 with hδdef
  have hδ : 0 < δ := by
    have h := totQ_lt
    rw [hδdef]
    linarith
  set K' : ℝ := (M + 1) * δ⁻¹ with hK'
  have hK'pos : 0 < K' := mul_pos (by linarith) (inv_pos.mpr hδ)
  set r : ℝ := 87 / 100 with hr
  set R : ℝ := 95 / 100 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log K'| + 6), fun t => ?_⟩
  set c₀ : ℂ := ((3 / 2 : ℝ) : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I with hc₀
  have hc₀re : c₀.re = 3 / 2 := centre_re t
  have hc₀im : c₀.im = t + 1 / 2 := centre_im t
  set κ : ℂ := ((13 / 10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := Complex.ofReal_ne_zero.mpr (by norm_num)
  have hnormκ : ‖κ‖ = 13 / 10 := by
    rw [hκ, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hlow : δ ≤ ‖aE c₀‖ := aE_lower hc₀re
  have hne : aE c₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hlow
    linarith
  set u : ℂ := (aE c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hne
  have hnu : ‖u‖ ≤ δ⁻¹ := by
    rw [hu, norm_inv]
    exact inv_anti₀ hδ hlow
  set g : ℂ → ℂ := gQ c₀ κ u with hg
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    fun z _ => gQ_analyticAt c₀ κ u z
  have hg0 : g 0 = 1 := by
    show aE (c₀ + κ * 0) * u = 1
    rw [mul_zero, add_zero]
    exact mul_inv_cancel₀ hne
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := aE_zero_finite (isCompact_closedBall c₀ (13 / 10 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    have hgz' : aE (c₀ + κ * z) * u = 0 := hgz
    refine ⟨c₀ + κ * z, ⟨?_, (mul_eq_zero.mp hgz').resolve_right hu0⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]
      nlinarith [norm_nonneg z]
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := K' * (|t| + 7) ^ 3 with hB
  have hT3 : 0 ≤ (|t| + 7) ^ 3 := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    set s : ℂ := c₀ + κ * z with hs
    have hzr := (Complex.abs_re_le_norm z).trans hz
    have hzi := (Complex.abs_im_le_norm z).trans hz
    rw [hR] at hzr hzi
    obtain ⟨hz1, hz2⟩ := abs_le.mp hzr
    obtain ⟨hz3, hz4⟩ := abs_le.mp hzi
    have hsre : s.re = 3 / 2 + 13 / 10 * z.re := by
      rw [hs, Complex.add_re, hc₀re, hκ, kappa_re]
    have hsim : s.im = t + 1 / 2 + 13 / 10 * z.im := by
      rw [hs, Complex.add_im, hc₀im, hκ, kappa_im]
    have hsr : -1 / 2 ≤ s.re := by
      rw [hsre]
      linarith
    have hN : ‖s + 2‖ ≤ |t| + 7 := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (s + 2)
      rw [add_two_re, add_two_im] at h2
      have h3 : |s.re + 2| ≤ 19 / 4 := by
        rw [hsre]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h4 : |s.im| ≤ |t| + 2 := by
        rw [hsim]
        exact abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      linarith
    have hinv : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    calc ‖g z‖ = ‖aE s‖ * ‖u‖ := norm_mul _ _
      _ ≤ (M * (|t| + 7) ^ 3) * δ⁻¹ :=
          mul_le_mul ((hgrowth s hsr).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hN 3) hM0)) hnu (norm_nonneg _)
            (mul_nonneg hM0 hT3)
      _ = (M * δ⁻¹) * (|t| + 7) ^ 3 := by ring
      _ ≤ K' * (|t| + 7) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hinv) hT3
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  set W : Set ℂ := Wide.window zqZeroConfig t (t + 1) ∩ {ρ | 1 / 2 ≤ ρ.re} with hW
  have hWw : (Wide.window zqZeroConfig t (t + 1)).Finite := zqZeroConfig.finite_window t (t + 1)
  have hWfin : W.Finite := hWw.subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by
    intro ρ
    have h : κ * ((ρ - c₀) / κ) = ρ - c₀ := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hκ0]
    show c₀ + κ * ((ρ - c₀) / κ) = ρ
    rw [h]
    ring
  have hφinj : Function.Injective φ := by
    intro a b h
    calc a = c₀ + κ * φ a := (hφinv a).symm
      _ = c₀ + κ * φ b := by rw [h]
      _ = b := hφinv b
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hC := mem_C hρZ
    have hzero : aE ρ = 0 := by rw [aE_eq hC.2.1, hC.2.2.2, mul_zero]
    refine ⟨?_, ?_⟩
    · simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 3 / 2 := by rw [Complex.sub_re, hc₀re]
      have him : (ρ - c₀).im = ρ.im - (t + 1 / 2) := by rw [Complex.sub_im, hc₀im]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (87 / 100 * (13 / 10)) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have hb : ρ.re < 3 / 2 := C_re_lt hρZ
        have hc : 1 / 2 ≤ ρ.re := hρre
        have a1 : (ρ.re - 3 / 2) * (ρ.re - 3 / 2) ≤ 1 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hb.le)]
        have a2 : (ρ.im - (t + 1 / 2)) * (ρ.im - (t + 1 / 2)) ≤ 1 / 4 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hρt.le) (sub_nonneg.mpr hρt1)]
        have a3 : (1 : ℝ) + 1 / 4 ≤ (87 / 100 * (13 / 10)) ^ 2 := by norm_num
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gQ, hφinv]
      rw [hzero, zero_mul]
  have hmult : ∀ ρ ∈ W, (zqZeroConfig.mult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    rw [hg, analyticOrderNatAt_gQ hκ0 hu0, hφinv, aE_orderNat_eq (mem_C hρZ).2.1]
    rfl
  have hsum : NhalfQ t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfQ
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros
      positivity
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg t]
  have hlog7 : Real.log (|t| + 7) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log K'| + 6) * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul hK'pos.ne' (by positivity), Real.log_pow]
    have h1' := le_abs_self (Real.log K')
    have h2 : |Real.log K'| ≤ |Real.log K'| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : ((3 : ℕ) : ℝ) * Real.log (|t| + 7) ≤ 6 * Real.log (|t| + 3) := by
      push_cast
      linarith
    linarith
  calc NhalfQ t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log K'| + 6) * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (one_div_nonneg.mpr hlogRr.le)
    _ = _ := by ring

/-- **THE count FIELD**: `∃ A₀, Wide.HCount zqZeroConfig A₀`, every `t`, the zeros of `Λ_Q` in the open strip counted with multiplicity. -/
theorem zq_count_holds : ∃ A₀ : ℝ, Wide.HCount zqZeroConfig A₀ := by
  obtain ⟨A₁, hA₁⟩ := halfQ_count
  refine ⟨max 1 (2 * A₁), le_max_left _ _, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg t]
  have hhalf : (Wide.N zqZeroConfig t (t + 1) : ℝ) ≤ 2 * NhalfQ t := wide_N_le_two_mul_half zqZeroConfig t (t + 1)
  calc (Wide.N zqZeroConfig t (t + 1) : ℝ) ≤ 2 * NhalfQ t := hhalf
    _ ≤ 2 * (A₁ * Real.log (|t| + 3)) := mul_le_mul_of_nonneg_left (hA₁ t) (by norm_num)
    _ = 2 * A₁ * Real.log (|t| + 3) := by ring
    _ ≤ max 1 (2 * A₁) * Real.log (|t| + 3) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end ZQ
end Schema
end SIDEExplicitFormula
