/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/LocalCount.lean
THIS PROGRAMME'S WORK (act b569, ruling (R179)(6); W-ORD-GRH-WEIL, act four) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE χ-ANALOGUE OF Zeta23/RvM/LocalCount.lean, the next module of EF_lit's route: the local zero count
`N_χ(t, t+1] ≤ A₀ log(|t| + 3)` for primitive `χ ≠ 1`, zeros of `LFunction χ` in the open strip counted with
multiplicity (`chiZeroConfig`). The route is Zeta23's, carried:
* count only the zeros with `β ≥ 1/2` and double (`Zeta23.ZeroConfig.N_le_two_mul_half`, generic over a zero
  configuration, applied to `chiZeroConfig`, whose reflection ρ ↦ 1 − ρ̄ is `chi_reflect_zero`);
* the Jensen-type count on a disc, the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean), applied to
  `g(w) := L(c₀ + 1.9 w, χ) / L(c₀, χ)`, `c₀ := 2 + (t + ½)i`, `r = 0.84`, `R = 0.95`;
* the growth `‖L(s, χ)‖ ≤ (N + 1)(20/3)(|Im s| + 3)` on `σ ≥ 0.15` and `‖L(2 + it, χ)‖ ≥ 1/3`
  (Chi/ZetaGrowth.lean) -- no pole, so ζ's distance-from-1 conditions are not needed;
* `|t| < 4` by the finite constant `N(−4, 5]`.
Nothing here proves GRH or locates any zero of `LFunction χ`.
-/
import SIDEExplicitFormula.Chi.ZeroConfig
import SIDEExplicitFormula.Chi.ZetaGrowth
import Zeta23.Prelude.InstancePriorities
import Zeta23.FromPNTPlus.StrongPNTPrefix
import Zeta23.RvM.Halving

open Complex Set Filter Topology Metric

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The zeros of `LFunction χ` in any compact set are finite, for `χ ≠ 1`. -/
theorem LFunction_zeros_finite_of_isCompact {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {K : Set ℂ}
    (hK : IsCompact K) : (K ∩ {ρ : ℂ | LFunction χ ρ = 0}).Finite := by
  choose t ht hfin using LFunction_zeros_locallyFinite h1
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ⟩

/-- The rescaled function `g(z) := L(s₀ + c z, χ) · u`. -/
def gfunChi (χ : DirichletCharacter ℂ N) (s₀ c u : ℂ) (z : ℂ) : ℂ := LFunction χ (s₀ + c * z) * u

theorem comp_affine_analyticAt_chi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s₀ c z : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => LFunction χ (s₀ + c * z)) z := by
  have hL : AnalyticAt ℂ (LFunction χ) (s₀ + c * z) := analyticAt_LFunction h1 _
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hL.comp_of_eq haff rfl

theorem gfunChi_analyticAt {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (s₀ c u z : ℂ) :
    AnalyticAt ℂ (gfunChi χ s₀ c u) z :=
  (comp_affine_analyticAt_chi h1 s₀ c z).mul analyticAt_const

/-- Order transport: the order of `g` at `w` is the multiplicity of `L(·, χ)` at `s₀ + c w`. -/
theorem analyticOrderNatAt_gfunChi {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s₀ c u w : ℂ} (hc : c ≠ 0)
    (hu : u ≠ 0) : analyticOrderNatAt (gfunChi χ s₀ c u) w = zeroMultChi χ (s₀ + c * w) := by
  unfold analyticOrderNatAt zeroMultChi gfunChi
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => LFunction χ (s₀ + c * z)) w := comp_affine_analyticAt_chi h1 s₀ c w
  have hmul : (fun z ↦ LFunction χ (s₀ + c * z) * u) =
      (fun z => LFunction χ (s₀ + c * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => s₀ + c * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hc
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := LFunction χ) haff hderiv
  simpa [Function.comp_def] using this

/-- Zeros with `β ≥ 1/2` in the window `(t, t+1]`, with multiplicity, as a real number. -/
def NhalfChi (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ (chiZeroConfig χ hχ h1).window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (zeroMultChi χ ρ : ℝ)

/-- The `β ≥ 1/2` half-window count is `≪ log(|t| + 3)` for `|t| ≥ 4` (the disc argument). -/
theorem half_count_large_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfChi χ hχ h1 t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨A, C, hC, hgrowth⟩ := LFunction_growth_right h1
  have hL := LFunction_lower_bound_two χ
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A'), fun t ht => ?_⟩
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hLc₀ : (1/3 : ℝ) ≤ ‖LFunction χ c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have hLc₀ne : LFunction χ c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hLc₀; norm_num at hLc₀
  set u : ℂ := (LFunction χ c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hLc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := gfunChi χ c₀ κ u with hg
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    fun z _ => gfunChi_analyticAt h1 c₀ κ u z
  have hg0 : g 0 = 1 := by simp [hg, gfunChi, hu, hLc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := LFunction_zeros_finite_of_isCompact h1 (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]; nlinarith [norm_nonneg z]
    · simpa [hg, gfunChi, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1', -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1'; nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1' := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1' : ‖LFunction χ s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) hsim hA'0
    calc ‖g z‖ = ‖LFunction χ s‖ * ‖u‖ := by simp [hg, gfunChi, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1'.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  set W : Set ℂ := (chiZeroConfig χ hχ h1).window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := ((chiZeroConfig χ hχ h1).window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : IsNontrivialZeroChi χ ρ := hρZ
    refine ⟨?_, ?_⟩
    · simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gfunChi, hφinv]; rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMultChi χ ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ -
    rw [analyticOrderNatAt_gfunChi h1 hκ0 hu0, hφinv]
  have hsum : NhalfChi χ hχ h1 t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfChi
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1' := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc NhalfChi χ hχ h1 t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring

/-- Small heights: `N_χ(t, t+1] ≤ N_χ(−4, 5]` for `|t| ≤ 4`. -/
theorem count_small_chi {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (t : ℝ) (ht : |t| ≤ 4) :
    ((chiZeroConfig χ hχ h1).N t (t + 1) : ℝ) ≤ (chiZeroConfig χ hχ h1).N (-4) 5 := by
  obtain ⟨h1', h2⟩ := abs_le.mp ht
  have hsub : (chiZeroConfig χ hχ h1).window t (t + 1) ⊆ (chiZeroConfig χ hχ h1).window (-4) 5 := by
    rintro ρ ⟨hρ, ha, hb⟩; exact ⟨hρ, by linarith, by linarith⟩
  have h' : (chiZeroConfig χ hχ h1).N t (t + 1) ≤ (chiZeroConfig χ hχ h1).N (-4) 5 :=
    (chiZeroConfig χ hχ h1).finsum_mult_mono (-4) 5 hsub subset_rfl
  exact_mod_cast h'

/-- **THE LOCAL COUNT FOR `χ`** (the analogue of `zetaZeroConfig_local_count`): `∃ A₀ ≥ 1, ∀ t ∈ ℝ,
N_χ(t, t+1] ≤ A₀ log(|t| + 3)`, zeros of `LFunction χ` in the open strip counted with multiplicity. -/
theorem chiZeroConfig_local_count {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, ((chiZeroConfig χ hχ h1).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₁, hA₁⟩ := half_count_large_chi hχ h1
  set K : ℝ := ((chiZeroConfig χ hχ h1).N (-4) 5 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (max (2 * A₁) K), le_max_left _ _, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hhalf : ((chiZeroConfig χ hχ h1).N t (t + 1) : ℝ) ≤ 2 * NhalfChi χ hχ h1 t := by
    have := (chiZeroConfig χ hχ h1).N_le_two_mul_half t (t + 1)
    simpa [NhalfChi, chiZeroConfig_mult] using this
  rcases le_or_gt 4 |t| with ht | ht
  · calc ((chiZeroConfig χ hχ h1).N t (t + 1) : ℝ) ≤ 2 * NhalfChi χ hχ h1 t := hhalf
      _ ≤ 2 * (A₁ * Real.log (|t| + 3)) := by
          have := hA₁ t ht; nlinarith
      _ = (2 * A₁) * Real.log (|t| + 3) := by ring
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc ((chiZeroConfig χ hχ h1).N t (t + 1) : ℝ) ≤ K := count_small_chi hχ h1 t ht.le
      _ ≤ K * Real.log (|t| + 3) := le_mul_of_one_le_right hK0 hlog3
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)

end GRHWeil
end SIDEExplicitFormula
