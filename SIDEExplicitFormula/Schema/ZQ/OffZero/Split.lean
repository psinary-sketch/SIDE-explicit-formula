/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Split.lean
THIS PROGRAMME'S WORK (act b738, ruling (R348)(3)(b), relay data/b737_offlinezero_plan.txt (d) S5a) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

S5a, `Λ₀` SPLIT AT `t = 1`. Mathlib's `WeakFEPair.Λ₀ = mellin f_modif` (NumberTheory/LSeries/AbstractFuncEq.lean :376); for `zqPair` the
modified theta is `thA + thB`, `thA` the theta less one on `(1, ∞)` and `thB` its piece on `(0, 1)`, and on `(0, ∞)` the functional equation
`thetaC_feq` gives `thB t = t⁻¹ · thA (1/t)`. So `Λ₀ s = M s + M (1 − s)` with `M w = ∫_{t > 1} t^(w − 1) (θ(t) − 1) dt`, both halves convergent
for every `s`. No value of any integral is computed here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.FEPair

open Set Filter Topology Asymptotics MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- `θ − 1` on `(1, ∞)`, zero elsewhere. -/
def thA : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => thetaC t - 1)

/-- The modified theta's piece on `(0, 1)`, as Mathlib's `f_modif` writes it for `zqPair`. -/
def thB : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator (fun x => thetaC x - ((1 : ℂ) * ((x ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ))

/-- The half `M w = ∫_{t > 1} t^(w − 1) (θ(t) − 1) dt`, as a Mellin transform. -/
def lamM (w : ℂ) : ℂ := mellin thA w

theorem lamM_eq (w : ℂ) : lamM w = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (thetaC t - 1) := by
  unfold lamM mellin
  have e : (fun t : ℝ => (t : ℂ) ^ (w - 1) • thA t)
      = (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (w - 1) * (thetaC t - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [thA, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
    · rw [thA, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [e, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

theorem f_modif_eq : zqPair.f_modif = thA + thB := rfl

theorem thA_locInt : LocallyIntegrableOn thA (Ioi 0) := by
  intro x hx
  obtain ⟨s, hs, hs'⟩ := ((thetaC_continuousOn.sub continuousOn_const).locallyIntegrableOn
    measurableSet_Ioi : LocallyIntegrableOn (fun t => thetaC t - 1) (Ioi 0)) x hx
  exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩

theorem thA_top (r : ℝ) : thA =O[atTop] (· ^ r) := by
  refine (thetaC_decay r).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [thA, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]

theorem thA_bot (b : ℝ) : thA =O[𝓝[>] 0] (· ^ b) := by
  refine ((isBigO_zero (fun x : ℝ => x ^ b) (𝓝[>] (0 : ℝ)) : (fun _x : ℝ => (0 : ℂ)) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ b)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [thA, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => lt_irrefl _ (ht.2.trans h))]

/-- `thA` is Mellin-convergent at every `w`. -/
theorem thA_conv (w : ℂ) : MellinConvergent thA w :=
  mellinConvergent_of_isBigO_rpow thA_locInt (thA_top (-(w.re + 1))) (by linarith) (thA_bot (-(w.re - 1))) (by linarith)

/-- On `(0, ∞)`, `thB t = t⁻¹ · thA (1/t)`: the functional equation of the theta. -/
theorem thB_eq : EqOn thB (fun t => (t : ℂ) ^ (-1 : ℂ) • thA t⁻¹) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
  have hpos : 0 < t⁻¹ := inv_pos.mpr ht0
  show thB t = (t : ℂ) ^ (-1 : ℂ) • thA t⁻¹
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · have hi : 1 < t⁻¹ := by nlinarith
    rw [thB, indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, h1⟩), thA,
      indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi)]
    have hfe := thetaC_feq ht0
    rw [one_div, Real.rpow_one, one_mul, smul_eq_mul] at hfe
    rw [hfe]
    simp only [Real.rpow_neg_one, Complex.cpow_neg_one, Complex.ofReal_inv, one_mul, smul_eq_mul, mul_one]
    have hc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, mul_one]
  · subst h1
    rw [thB, indicator_of_notMem (show (1 : ℝ) ∉ Ioo (0 : ℝ) 1 from fun h => lt_irrefl _ h.2), thA, inv_one,
      indicator_of_notMem (show (1 : ℝ) ∉ Ioi (1 : ℝ) from fun h => lt_irrefl (1 : ℝ) (mem_Ioi.mp h)), smul_zero]
  · have hi : t⁻¹ < 1 := by nlinarith
    rw [thB, indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h => lt_asymm h.2 h1), thA,
      indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from fun h => lt_asymm h hi), smul_zero]

/-- `thB` is Mellin-convergent at every `s`. -/
theorem thB_conv (s : ℂ) : MellinConvergent thB s := by
  have h1 : MellinConvergent (fun t => thA t⁻¹) (s + -1) := by
    have h := (MellinConvergent.comp_rpow (f := thA) (s := s + -1) (a := -1) (by norm_num)).mpr (thA_conv _)
    simpa only [Real.rpow_neg_one] using h
  have h2 : MellinConvergent (fun t => (t : ℂ) ^ (-1 : ℂ) • thA t⁻¹) s := MellinConvergent.cpow_smul.mpr h1
  show IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • thB t) (Ioi 0)
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr h2
  simp only [thB_eq ht]

/-- **S5a**: `Λ₀ s = M s + M (1 − s)`, the split at `t = 1`. -/
theorem zq_Λ₀_split (s : ℂ) : zqPair.Λ₀ s = lamM s + lamM (1 - s) := by
  have e1 : zqPair.Λ₀ s = mellin thA s + mellin thB s := by
    show mellin zqPair.f_modif s = _
    rw [f_modif_eq]
    unfold mellin
    simp_rw [Pi.add_apply, smul_add]
    exact integral_add (thA_conv s) (thB_conv s)
  have e2 : mellin thB s = mellin thA (1 - s) := by
    calc mellin thB s = mellin (fun t => (t : ℂ) ^ (-1 : ℂ) • thA t⁻¹) s := by
          unfold mellin
          exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [thB_eq ht])
      _ = mellin (fun t => thA t⁻¹) (s + -1) := mellin_cpow_smul _ _ _
      _ = mellin thA (-(s + -1)) := mellin_comp_inv _ _
      _ = mellin thA (1 - s) := by congr 1; ring
  unfold lamM
  rw [e1, e2]

/-- `zq_Λ₀_split` under an ASCII name, the one the runner's print step admits (run 41741988143's axioms_refused.txt :1). -/
theorem zq_lambda0_split (s : ℂ) : zqPair.Λ₀ s = lamM s + lamM (1 - s) := zq_Λ₀_split s

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
