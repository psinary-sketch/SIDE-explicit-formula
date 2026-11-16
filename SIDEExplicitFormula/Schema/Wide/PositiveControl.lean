/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/PositiveControl.lean
THIS PROGRAMME'S WORK (act b745, ruling (R355)(4)(a), W-ORD-POSITIVE-CONTROL; the plan relay data/b744_poscontrol_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE POSITIVE CONTROL. A two-point configuration of the widened class, `pcConfig = {1/2 + i, 1/2 - i}`, on which the schema's three
hypotheses are met: the local count (`pc_count`), no point at `0` (`pc_ne_zero`), and Li-nonnegativity for every `n` (`pc_li_nonneg`;
here `λ_n = 2 (1 - cos nθ)`, `θ = atan (4/3)`, since `1 - ρ⁻¹ = (3 + 4i)/5` at `ρ = 1/2 + i`; the bound below uses only that both points lie
on the line). The conclusion `pc_online` is drawn through `Wide.li_nonneg_cfg_imp_online_ne_zero` (StripFree.lean :157), the theorem
Epstein's own conclusion goes through (Schema/EpsteinZQ.lean :166), and through no lemma about finite carriers. Of this programme's
modules it imports `Schema.Wide.StripFree` alone (beside two Mathlib modules, the count's `finsum_one` and `exp_one_lt_d9`), so its
closure has no route to Z_Q's modules.

The schema's implication Li-nonnegativity ⟹ every zero on the line is exercised with a true antecedent at a two-point configuration,
through the theorem Epstein's own conclusion goes through; it says nothing of ζ or of Z_Q.
-/
import SIDEExplicitFormula.Schema.Wide.StripFree
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Wide

open Zeta23

/-! ## P1 -- the carrier and its six fields -/

/-- The two points `1/2 + i` and `1/2 - i`. -/
def pcCarrier : Set ℂ := {⟨1 / 2, 1⟩, ⟨1 / 2, -1⟩}

/-- Both points lie on the line. -/
theorem pc_re {ρ : ℂ} (h : ρ ∈ pcCarrier) : ρ.re = 1 / 2 := by
  rcases h with rfl | rfl <;> rfl

/-- On the line, `reflect ρ = 1 - conj ρ` is `ρ` itself. -/
theorem pc_reflect {ρ : ℂ} (h : ρ.re = 1 / 2) : reflect ρ = ρ := by
  apply Complex.ext
  · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]

/-- The carrier is finite. -/
theorem pcCarrier_finite : pcCarrier.Finite := (Set.finite_singleton _).insert _

/-- **The positive control's configuration:** the two points, each of multiplicity one. -/
def pcConfig : WideConfig where
  carrier := pcCarrier
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := fun ρ h => by
    rw [pc_re h]
    norm_num
  reflect_mem := fun ρ h => by
    rw [pc_reflect (pc_re h)]
    exact h
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => pcCarrier_finite.subset Set.inter_subset_left

/-! ## P2 -- the local count -/

/-- The carrier has at most two points. -/
theorem pcCarrier_ncard_le : pcCarrier.ncard ≤ 2 := by
  unfold pcCarrier
  calc ({⟨1 / 2, 1⟩, ⟨1 / 2, -1⟩} : Set ℂ).ncard ≤ ({⟨1 / 2, -1⟩} : Set ℂ).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- Every window holds at most two points, counted with multiplicity (SaltCheckEpstein.lean :72's form). -/
theorem pc_N_le (T₁ T₂ : ℝ) : N pcConfig T₁ T₂ ≤ 2 := by
  show (∑ᶠ ρ ∈ window pcConfig T₁ T₂, (1 : ℕ)) ≤ 2
  rw [finsum_one]
  calc (window pcConfig T₁ T₂).ncard ≤ pcCarrier.ncard :=
        Set.ncard_le_ncard Set.inter_subset_left pcCarrier_finite
    _ ≤ 2 := pcCarrier_ncard_le

/-- `1 ≤ log (|t| + 3)`, from `exp 1 < 3` (SaltCheckEpstein.lean :65's form). -/
theorem pc_one_le_log (t : ℝ) : 1 ≤ Real.log (|t| + 3) := by
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hle : Real.log 3 ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  linarith

/-- **The count:** `N(t, t + 1) ≤ 2 log (|t| + 3)`. -/
theorem pc_count : HCount pcConfig 2 := by
  refine ⟨by norm_num, fun t => ?_⟩
  have hN : (N pcConfig t (t + 1) : ℝ) ≤ 2 := by exact_mod_cast pc_N_le t (t + 1)
  have hl := pc_one_le_log t
  linarith

/-! ## P3 -- no point at `0` -/

/-- **No point at `0`:** each point has real part `1/2`. -/
theorem pc_ne_zero : ∀ ρ ∈ pcConfig.carrier, ρ ≠ 0 := by
  intro ρ hρ e
  have h := pc_re hρ
  rw [e, Complex.zero_re] at h
  norm_num at h

/-! ## P4 -- Li-nonnegativity, the Wide form of the forward half -/

/-- **The forward half over the widened class** (LiCfg.lean :86's proof): every point on the line makes every Li coefficient
nonnegative; each term's real part is nonnegative (LiWeil.lean :109) and `tsum_nonneg` closes it, no summability needed. -/
theorem online_imp_liCoeff_nonneg (Z : WideConfig) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) → ∀ n : ℕ, 0 ≤ liCoeff Z n := by
  intro h n
  unfold liCoeff
  exact mul_nonneg (by norm_num) (tsum_nonneg fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (LiWeil.pairTerm_re_nonneg_of_re_half n (h ρ ρ.2)))

/-- **Li-nonnegativity at the control:** `0 ≤ λ_n` for every `n` (`λ_n = 2 (1 - cos nθ)`, `θ = atan (4/3)`). -/
theorem pc_li_nonneg : ∀ n : ℕ, 0 ≤ Wide.liCoeff pcConfig n :=
  online_imp_liCoeff_nonneg pcConfig fun _ h => pc_re h

/-! ## P5 -- the conclusion, through the schema's theorem -/

/-- **The positive control:** the conclusion drawn through `Wide.li_nonneg_cfg_imp_online_ne_zero` with all three hypotheses met. -/
theorem pc_online : ∀ ρ ∈ pcConfig.carrier, ρ.re = 1 / 2 :=
  Wide.li_nonneg_cfg_imp_online_ne_zero pcConfig pc_count pc_ne_zero pc_li_nonneg

end Wide
end Schema
end SIDEExplicitFormula
