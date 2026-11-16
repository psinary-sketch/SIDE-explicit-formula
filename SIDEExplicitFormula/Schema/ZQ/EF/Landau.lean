/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/EF/Landau.lean
THIS PROGRAMME'S WORK (act b735, ruling (R345)(3), relay data/b734_explicitformula_plan.txt row E5, group B) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

LANDAU'S PARTIAL FRACTION AT `zqFn`, Chi/Landau.lean's proof from the generic `logDeriv_partial_fraction_disk`, centre `2 + it`, radii `91/50`, `3/2`. For `|t| ≥ 6` the
disc avoids the pole at `1`; the lower bound at the centre is `zq_norm_ge`, the upper bound `aE_growth` over `|1 − s| ≥ 1`. Break point (4): the centre `Re = 2` stands.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.ZQ.EF.Xi

open Complex Set Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace EF

/-- Off the pole and on `Re s ≥ −1/2`, with `1 ≤ |Im s|`, `zqFn` is bounded by the growth of `aE`. -/
theorem norm_zqFn_le {M : ℝ} (hM : ∀ s : ℂ, -1 / 2 ≤ s.re → ‖aE s‖ ≤ M * ‖s + 2‖ ^ 3) {s : ℂ} (hre : -1 / 2 ≤ s.re)
    (him : 1 ≤ |s.im|) : ‖zqFn s‖ ≤ M * ‖s + 2‖ ^ 3 := by
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_im, abs_zero] at him
    linarith
  have hge : 1 ≤ ‖1 - s‖ := by
    have h := Complex.abs_im_le_norm (1 - s)
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    linarith
  have e := aE_eq hs1
  have hn : ‖aE s‖ = ‖1 - s‖ * ‖zqFn s‖ := by
    rw [e, norm_mul]
  have h0 : 0 ≤ ‖zqFn s‖ := norm_nonneg _
  calc ‖zqFn s‖ ≤ ‖1 - s‖ * ‖zqFn s‖ := by nlinarith
    _ = ‖aE s‖ := hn.symm
    _ ≤ M * ‖s + 2‖ ^ 3 := hM s hre

/-- **E5. Landau's partial fraction at `zqFn`** (`|t| ≥ 6`): the finite set `Z` of the zeros within `(22/25)(91/50)` of `2 + it`, and on the ball of radius `3/2` about `2 + it`,
away from zeros, `Z'/Z(s) = Σ_{ρ ∈ Z} m_ρ/(s − ρ) + O(log(|t| + 3))`. -/
theorem zq_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22 / 25 * (91 / 50)) | zqFn ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt zqFn ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3 / 2), zqFn s ≠ 0 →
        ‖logDeriv zqFn s - ∑ ρ ∈ Z, (analyticOrderNatAt zqFn ρ : ℂ) / (s - ρ)‖ ≤ C * Real.log (|t| + 3) := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := aE_growth
  set δ : ℝ := 4 - totQ with hδ
  have hδ0 : 0 < δ := by
    have := totQ_lt
    rw [hδ]
    linarith
  -- `B` is `K (|t| + 2)³`, the constant `K` carrying `M/δ`
  set K : ℝ := M₀ / δ * 216 + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ M₀ / δ * 216 := mul_nonneg (div_nonneg hM₀0 hδ0.le) (by norm_num)
    rw [hK]
    linarith
  have hK0 : K ≠ 0 := (lt_of_lt_of_le one_pos hK1).ne'
  have hδne : δ ≠ 0 := hδ0.ne'
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  set D : ℝ := Real.log K + 3 + 1 with hD
  have hD0 : 0 < D := by
    rw [hD]
    linarith
  refine ⟨(44795000 * 50 / 91) * D, mul_pos (by norm_num) hD0, fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hlow : δ ≤ ‖zqFn s₀‖ := zq_norm_ge (by rw [hs₀re]; norm_num)
  have hzs₀ : zqFn s₀ ≠ 0 := zq_ne_zero_of_three_halves_le s₀ (by rw [hs₀re]; norm_num)
  -- the ball of radius 91/50 misses the pole
  have him_ball : ∀ w ∈ Metric.closedBall s₀ (91 / 50), 1 ≤ |w.im| := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have h1 := Complex.abs_im_le_norm (w - s₀)
    have him : (w - s₀).im = w.im - t := by simp [hs₀]
    rw [him] at h1
    have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
    have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
    linarith
  have hfa : AnalyticOnNhd ℂ zqFn (Metric.closedBall s₀ (91 / 50)) := by
    intro w hw
    refine zq_analyticAt (fun h => ?_)
    have h1 := him_ball w hw
    rw [h, Complex.one_im, abs_zero] at h1
    linarith
  set B : ℝ := K * (|t| + 2) ^ 3 with hB
  have ht2 : (6 : ℝ) ≤ |t| + 2 := by linarith
  have hB2 : 2 ≤ B := by
    rw [hB]
    have h216 : (216 : ℝ) ≤ (|t| + 2) ^ 3 :=
      calc (216 : ℝ) = 6 ^ 3 := by norm_num
        _ ≤ (|t| + 2) ^ 3 := pow_le_pow_left₀ (by norm_num) ht2 3
    nlinarith
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24 / 25 * (91 / 50)), ‖zqFn w‖ ≤ B * ‖zqFn s₀‖ := by
    intro w hw
    have hwR : w ∈ Metric.closedBall s₀ (91 / 50) :=
      Metric.closedBall_subset_closedBall (by norm_num) hw
    have him1 := him_ball w hwR
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : -1 / 2 ≤ w.re := by
      have h1 := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre, abs_le] at h1
      linarith [h1.1]
    have hbd := norm_zqFn_le hM₀ hwre him1
    -- `‖w + 2‖ ≤ 6 (|t| + 2)`
    have hnw : ‖w + 2‖ ≤ 6 * (|t| + 2) := by
      have h1 : ‖w + 2‖ ≤ ‖w - s₀‖ + ‖s₀ + 2‖ := by
        have e : w + 2 = (w - s₀) + (s₀ + 2) := by ring
        rw [e]
        exact norm_add_le _ _
      have h2 : ‖s₀ + 2‖ ≤ 4 + |t| := by
        have e : s₀ + 2 = ((4 : ℝ) : ℂ) + t * I := by
          rw [hs₀]
          push_cast
          ring
        rw [e]
        calc ‖((4 : ℝ) : ℂ) + t * I‖ ≤ ‖((4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = 4 + |t| := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith [abs_nonneg t]
    have hcube : ‖w + 2‖ ^ 3 ≤ 216 * (|t| + 2) ^ 3 :=
      calc ‖w + 2‖ ^ 3 ≤ (6 * (|t| + 2)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hnw 3
        _ = 216 * (|t| + 2) ^ 3 := by ring
    calc ‖zqFn w‖ ≤ M₀ * ‖w + 2‖ ^ 3 := hbd
      _ ≤ M₀ * (216 * (|t| + 2) ^ 3) := mul_le_mul_of_nonneg_left hcube hM₀0
      _ = (M₀ / δ * δ) * (216 * (|t| + 2) ^ 3) := by rw [div_mul_cancel₀ M₀ hδne]
      _ = (M₀ / δ * 216) * (|t| + 2) ^ 3 * δ := by ring
      _ ≤ K * (|t| + 2) ^ 3 * δ := by
          refine mul_le_mul_of_nonneg_right ?_ hδ0.le
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK]
          linarith
      _ ≤ B * ‖zqFn s₀‖ := by
          rw [hB]
          exact mul_le_mul_of_nonneg_left hlow (mul_nonneg (by linarith) (by positivity))
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk (f := zqFn)
    (by norm_num : (0 : ℝ) < 91 / 50) hfa hzs₀ hB2 hfB
  have hT3 : (2 : ℝ) ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 9 := by norm_num
      _ ≤ |t| + 3 := by linarith
  have hlogB : Real.log B ≤ D * Real.log (|t| + 3) := by
    have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) := Real.log_le_log (by linarith) (by linarith)
    have hBeq : Real.log B = Real.log K + 3 * Real.log (|t| + 2) := by
      have h3c : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [hB, Real.log_mul hK0 (by positivity), Real.log_pow, h3c]
    rw [hBeq, hD]
    nlinarith [mul_nonneg hlogK (by linarith : (0 : ℝ) ≤ Real.log (|t| + 3) - 1)]
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [hZset]
  · refine hZcount.trans ?_
    have hratio : ((24 / 25 : ℝ)) / (22 / 25) = 12 / 11 := by norm_num
    have hlog1211 : (1 : ℝ) / 12 ≤ Real.log ((24 / 25) / (22 / 25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 12 by norm_num)
      rw [show (11 / 12 : ℝ) = (12 / 11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlogpos : (0 : ℝ) < Real.log ((24 / 25) / (22 / 25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0 : ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24 / 25) / (22 / 25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]
          linarith
      _ ≤ 12 * (D * Real.log (|t| + 3)) := mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 44795000 * 50 / 91 * D * Real.log (|t| + 3) := by
          nlinarith [mul_pos hD0 (by linarith : (0 : ℝ) < Real.log (|t| + 3))]
  · intro s hs hzs
    have hs' : s ∈ Metric.closedBall s₀ (83 / 100 * (91 / 50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hzs).trans ?_
    calc 44795000 / (91 / 50) * Real.log B
        ≤ 44795000 / (91 / 50) * (D * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ = (44795000 * 50 / 91) * D * Real.log (|t| + 3) := by ring

end EF
end ZQ
end Schema
end SIDEExplicitFormula
