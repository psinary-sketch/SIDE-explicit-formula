/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Frame.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (4) G0) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G0, THE FRAME ON `F`. `lamF s = Λ₀ s − 1/(s (1 − s))` (`= Λ s`, Continuation.lean :116), complex-differentiable off `0` and `1` (Λ₀ entire,
Mathlib `WeakFEPair.differentiable_Λ₀`), so `DiffContOnCl` on box A and on the far disc `ball cI 3`, `cI = 1/2 + 16.290216 i`, whose closure lies
above `Im = 13`. `zqFn s = qBase^s Γ(s)⁻¹ lamF s` off `0` and `1`, so a zero of `lamF` in the closure of box A is a zero of `zqFn` there. SP1' is
S3 on `lamF`: a point of box A where `‖lamF‖ < m` with `m ≤ ‖lamF‖` on the frontier gives a member of `zqZeroConfig.carrier` off `Re = 1/2`,
and with `zq_li_nonneg_imp_online_instance` its contrapositive. The numeric hypotheses stay open here: nothing in this file locates a zero.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Main
import SIDEExplicitFormula.Schema.ZQ.OffZero.Split

open Metric Set

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- `F = Λ₀ − 1/(s (1 − s))`, the completed function less its two poles' parts. -/
def lamF (s : ℂ) : ℂ := zqPair.Λ₀ s - 1 / (s * (1 - s))

/-- The far circle's centre, `1/2 + 16.290216 i`. -/
def cI : ℂ := ⟨1 / 2, 16290216 / 1000000⟩

theorem lamF_eq_split (s : ℂ) : lamF s = lamM s + lamM (1 - s) - 1 / (s * (1 - s)) := by
  rw [lamF, zq_Λ₀_split]

theorem lamF_differentiableOn : DifferentiableOn ℂ lamF {s : ℂ | s ≠ 0 ∧ s ≠ 1} := by
  show DifferentiableOn ℂ (fun s => zqPair.Λ₀ s - 1 / (s * (1 - s))) _
  refine zqPair.differentiable_Λ₀.differentiableOn.sub ((differentiableOn_const 1).div
    (differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id)) fun s hs => ?_)
  exact mul_ne_zero hs.1 (sub_ne_zero.2 (Ne.symm hs.2))

/-- `lamF` is `DiffContOnCl` on any set whose closure misses `0` and `1`. -/
theorem lamF_diffContOnCl {U : Set ℂ} (hU : ∀ z ∈ closure U, z ≠ 0 ∧ z ≠ 1) : DiffContOnCl ℂ lamF U :=
  DifferentiableOn.diffContOnCl (lamF_differentiableOn.mono hU)

theorem ne_zero_of_mem_closure_boxA {z : ℂ} (hz : z ∈ closure boxA) : z ≠ 0 := by
  intro h
  have hy := (mem_closure_boxA hz).2.2.1
  rw [h, Complex.zero_im] at hy
  norm_num [y0] at hy

theorem lamF_diffContOnCl_boxA : DiffContOnCl ℂ lamF boxA :=
  lamF_diffContOnCl fun _ hz => ⟨ne_zero_of_mem_closure_boxA hz, ne_one_of_mem_closure_boxA hz⟩

theorem im_ge_of_mem_closedBall_cI {z : ℂ} (hz : z ∈ closedBall cI 3) : 13 ≤ z.im := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := (abs_le.1 ((Complex.abs_im_le_norm (z - cI)).trans hz)).1
  rw [Complex.sub_im] at h
  have hc : cI.im = 16290216 / 1000000 := rfl
  rw [hc] at h
  linarith

theorem lamF_diffContOnCl_ball : DiffContOnCl ℂ lamF (ball cI 3) := by
  refine lamF_diffContOnCl fun z hz => ?_
  rw [closure_ball cI (by norm_num : (3 : ℝ) ≠ 0)] at hz
  have h := im_ge_of_mem_closedBall_cI hz
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [h0, Complex.zero_im] at h
    norm_num at h
  · rw [h1, Complex.one_im] at h
    norm_num at h

/-- `zqFn s = qBase^s Γ(s)⁻¹ lamF s` for `s ≠ 0, 1`. -/
theorem zqFn_eq_lamF {s : ℂ} (h0 : s ≠ 0) (h1 : 1 - s ≠ 0) :
    zqFn s = qBase ^ s * (Complex.Gamma s)⁻¹ * lamF s := by
  have key : 1 / (1 - s) + s⁻¹ = 1 / (s * (1 - s)) := by
    field_simp
    ring
  unfold zqFn lamF
  rw [Complex.Gamma_add_one s h0, mul_inv]
  linear_combination (-(qBase ^ s * (Complex.Gamma s)⁻¹)) * key

theorem zqFn_eq_zero_of_lamF {z : ℂ} (h0 : z ≠ 0) (h1 : 1 - z ≠ 0) (h : lamF z = 0) : zqFn z = 0 := by
  rw [zqFn_eq_lamF h0 h1, h, mul_zero]

/-- **SP1'**: S3 on `lamF`, its numeric hypotheses `hcm` and `hfr` open. -/
theorem lamF_min_modulus_zero (c : ℂ) (hc : c ∈ boxA) (m : ℝ) (hcm : ‖lamF c‖ < m)
    (hfr : ∀ z ∈ frontier boxA, m ≤ ‖lamF z‖) :
    ∃ ρ ∈ zqZeroConfig.carrier, ρ.re ≠ 1 / 2 := by
  obtain ⟨z, hz, h0⟩ := min_modulus_zero boxA_isBounded lamF_diffContOnCl_boxA hc hcm hfr
  exact ⟨z, carrier_of_box hz (zqFn_eq_zero_of_lamF (ne_zero_of_mem_closure_boxA hz)
    (sub_ne_zero.2 (ne_one_of_mem_closure_boxA hz).symm) h0)⟩

/-- **(e) on `lamF`**: the contrapositive of `zq_li_nonneg_imp_online_instance` under SP1''s hypotheses, open. -/
theorem lamF_li_not_nonneg (c : ℂ) (hc : c ∈ boxA) (m : ℝ) (hcm : ‖lamF c‖ < m)
    (hfr : ∀ z ∈ frontier boxA, m ≤ ‖lamF z‖) :
    ¬ ∀ n : ℕ, 0 ≤ Wide.liCoeff zqZeroConfig n := by
  intro hli
  obtain ⟨ρ, hρ, hre⟩ := lamF_min_modulus_zero c hc m hcm hfr
  exact hre (EF.zq_li_nonneg_imp_online_instance hli ρ hρ)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
