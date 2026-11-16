/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZetaBox/Split.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(b), W-ORD-ZETA-BOX Z1; the plan relay data/b744_zetabox_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z1, `Λ₀` OF `hurwitzEvenFEPair 0` SPLIT AT `t = 1` (OffZero/Split.lean :99's form, read at zeta). Mathlib's `WeakFEPair.Λ₀ = mellin f_modif`
(NumberTheory/LSeries/AbstractFuncEq.lean :376); for the pair of `evenKernel 0 = θ` (`θ t = Σ_{n ∈ ℤ} e^(−π n² t)`, `k = 1/2`) the modified kernel
is `zA + zB`, `zA` the theta less one on `(1, ∞)` and `zB` its piece on `(0, 1)`; by the functional equation `θ t = t^(−1/2) θ (1/t)`,
`zB t = t^(−1/2) · zA (1/t)`. So `Λ₀ w = M w + M (1/2 − w)` with `M w = ∫_{t > 1} t^(w − 1) (θ(t) − 1) dt`, and
`completedRiemannZeta₀ s = (M (s/2) + M (1/2 − s/2)) / 2`. No value of any integral is computed here and no zero is located.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Set Filter Topology Asymptotics MeasureTheory HurwitzZeta

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZetaBox

/-! ## Z1 -- the split of `Λ₀` at `t = 1` -/

/-- `θ − 1` on `(1, ∞)`, zero elsewhere; `θ = evenKernel 0`. -/
def zA : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => ((evenKernel 0 t : ℝ) : ℂ) - 1)

/-- The modified kernel's piece on `(0, 1)`, as Mathlib's `f_modif` writes it for `hurwitzEvenFEPair 0`. -/
def zB : ℝ → ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun x => ((evenKernel 0 x : ℝ) : ℂ) - ((1 : ℂ) * ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ))

/-- The half `M w = ∫_{t > 1} t^(w − 1) (θ(t) − 1) dt`, as a Mellin transform. -/
def zM (w : ℂ) : ℂ := mellin zA w

theorem zM_eq (w : ℂ) : zM w = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1) := by
  unfold zM mellin
  have e : (fun t : ℝ => (t : ℂ) ^ (w - 1) • zA t)
      = (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (w - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [zA, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
    · rw [zA, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [e, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- The pair's constant at infinity is `1` at `a = 0`. -/
theorem zf0 : (hurwitzEvenFEPair 0).f₀ = 1 := by
  first
  | exact if_pos rfl
  | simp [hurwitzEvenFEPair]

theorem zf_modif_eq : (hurwitzEvenFEPair 0).f_modif = zA + zB := by
  unfold WeakFEPair.f_modif
  rw [zf0]
  all_goals rfl

theorem zA_locInt : LocallyIntegrableOn zA (Ioi 0) := by
  intro x hx
  obtain ⟨s, hs, hs'⟩ := ((((Complex.continuous_ofReal.comp_continuousOn (continuousOn_evenKernel 0)).sub
    continuousOn_const).locallyIntegrableOn measurableSet_Ioi :
      LocallyIntegrableOn (fun t => ((evenKernel 0 t : ℝ) : ℂ) - 1) (Ioi 0))) x hx
  exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩

theorem zA_top (r : ℝ) : zA =O[atTop] (· ^ r) := by
  have h := (hurwitzEvenFEPair 0).hf_top r
  rw [zf0] at h
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [zA, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
  all_goals rfl

theorem zA_bot (b : ℝ) : zA =O[𝓝[>] 0] (· ^ b) := by
  refine ((isBigO_zero (fun x : ℝ => x ^ b) (𝓝[>] (0 : ℝ)) : (fun _x : ℝ => (0 : ℂ)) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ b)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [zA, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => lt_irrefl _ (ht.2.trans h))]

/-- `zA` is Mellin-convergent at every `w`. -/
theorem zA_conv (w : ℂ) : MellinConvergent zA w :=
  mellinConvergent_of_isBigO_rpow zA_locInt (zA_top (-(w.re + 1))) (by linarith) (zA_bot (-(w.re - 1))) (by linarith)

/-- The theta's functional equation at `a = 0`: `θ t = t^(−1/2) θ (1/t)` for `t > 0`. -/
theorem zK_feq {t : ℝ} (ht : 0 < t) : evenKernel 0 t = t ^ (-(1 / 2 : ℝ)) * evenKernel 0 t⁻¹ := by
  rw [evenKernel_functional_equation 0 t, ← evenKernel_eq_cosKernel_of_zero, Real.rpow_neg ht.le]
  simp only [one_div]

/-- On `(0, ∞)`, `zB t = t^(−1/2) · zA (1/t)`. -/
theorem zB_eq : EqOn zB (fun t => (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) • zA t⁻¹) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
  show zB t = (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) • zA t⁻¹
  rw [← Complex.ofReal_cpow ht0.le]
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · have hi : 1 < t⁻¹ := by nlinarith
    rw [zB, indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, h1⟩), zA,
      indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi), zK_feq ht0, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]
    ring
  · subst h1
    rw [zB, indicator_of_notMem (show (1 : ℝ) ∉ Ioo (0 : ℝ) 1 from fun h => lt_irrefl _ h.2), zA, inv_one,
      indicator_of_notMem (show (1 : ℝ) ∉ Ioi (1 : ℝ) from fun h => lt_irrefl (1 : ℝ) (mem_Ioi.mp h)), smul_zero]
  · have hi : t⁻¹ < 1 := by nlinarith
    rw [zB, indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h => lt_asymm h.2 h1), zA,
      indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from fun h => lt_asymm h hi), smul_zero]

/-- `zB` is Mellin-convergent at every `s`. -/
theorem zB_conv (s : ℂ) : MellinConvergent zB s := by
  have h1 : MellinConvergent (fun t => zA t⁻¹) (s + ((-(1 / 2 : ℝ) : ℝ) : ℂ)) := by
    have h := (MellinConvergent.comp_rpow (f := zA) (s := s + ((-(1 / 2 : ℝ) : ℝ) : ℂ)) (a := -1) (by norm_num)).mpr (zA_conv _)
    simpa only [Real.rpow_neg_one] using h
  have h2 : MellinConvergent (fun t => (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) • zA t⁻¹) s := MellinConvergent.cpow_smul.mpr h1
  show IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • zB t) (Ioi 0)
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr h2
  simp only [zB_eq ht]

/-- **Z1 at the pair**: `Λ₀ w = M w + M (1/2 − w)`, the split at `t = 1`. -/
theorem zLam0_split (s : ℂ) : (hurwitzEvenFEPair 0).Λ₀ s = zM s + zM (1 / 2 - s) := by
  have e1 : (hurwitzEvenFEPair 0).Λ₀ s = mellin zA s + mellin zB s := by
    show mellin (hurwitzEvenFEPair 0).f_modif s = _
    rw [zf_modif_eq]
    unfold mellin
    simp_rw [Pi.add_apply, smul_add]
    exact integral_add (zA_conv s) (zB_conv s)
  have e2 : mellin zB s = mellin zA (1 / 2 - s) := by
    calc mellin zB s = mellin (fun t => (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) • zA t⁻¹) s := by
          unfold mellin
          exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [zB_eq ht])
      _ = mellin (fun t => zA t⁻¹) (s + ((-(1 / 2 : ℝ) : ℝ) : ℂ)) := mellin_cpow_smul _ _ _
      _ = mellin zA (-(s + ((-(1 / 2 : ℝ) : ℝ) : ℂ))) := mellin_comp_inv _ _
      _ = mellin zA (1 / 2 - s) := by
          congr 1
          push_cast
          ring
  unfold zM
  rw [e1, e2]

/-- **Z1**: `completedRiemannZeta₀ s = (M (s/2) + M (1/2 − s/2)) / 2`. -/
theorem zeta0_split (s : ℂ) : completedRiemannZeta₀ s = (zM (s / 2) + zM (1 / 2 - s / 2)) / 2 := by
  show (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 = _
  rw [zLam0_split]

end ZetaBox
end Schema
end SIDEExplicitFormula
