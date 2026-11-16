/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Shells.lean
THIS PROGRAMME'S WORK (act b741, ruling (R351)(3)(b), relay data/b741_c7_plan.txt (5) G4) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G4, THE BOX SPLIT. `lamM w` against the eight evaluated shells `Q ≤ 18` (24 points, with their counts), for `Re w ≤ 1`; the rest of the box
bounded by (c6): the 16 points with `23 ≤ Q ≤ 27` at `Q = 23`, the 800 with `Q ≥ 32` at `Q = 32`. The counts by `decide +kernel` over the box.
No value of `zqFn` is computed here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.IncGamma
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- The box off the origin. -/
def boxE : Finset (ℤ × ℤ) := trBox.erase 0

/-- The evaluated points, `Q ≤ 18`. -/
def boxS : Finset (ℤ × ℤ) := boxE.filter (fun p => qN p ≤ 18)

/-- The rest of the box. -/
def boxR : Finset (ℤ × ℤ) := boxE.filter (fun p => ¬ qN p ≤ 18)

/-- The rest with `Q ≤ 31`: the shells `23 ≤ Q ≤ 27`. -/
def boxM : Finset (ℤ × ℤ) := boxR.filter (fun p => qN p ≤ 31)

/-- The rest with `Q ≥ 32`. -/
def boxB : Finset (ℤ × ℤ) := boxR.filter (fun p => ¬ qN p ≤ 31)

/-- The form's values on the evaluated points, with their counts. -/
theorem boxS_qN : boxS.val.map qN = 1 ::ₘ 1 ::ₘ 4 ::ₘ 4 ::ₘ 6 ::ₘ 6 ::ₘ 6 ::ₘ 6 ::ₘ 8 ::ₘ 8 ::ₘ 8 ::ₘ 8 ::ₘ 9 ::ₘ 9 ::ₘ 12 ::ₘ 12 ::ₘ 12 ::ₘ 12 ::ₘ
    16 ::ₘ 16 ::ₘ 18 ::ₘ 18 ::ₘ 18 ::ₘ 18 ::ₘ 0 := by
  decide +kernel

theorem boxM_card : boxM.card = 16 := by
  decide +kernel

theorem boxM_ge : ∀ p ∈ boxM, 23 ≤ qN p := by
  decide +kernel

theorem boxB_card : boxB.card = 800 := by
  decide +kernel

theorem boxB_ge : ∀ p ∈ boxB, 32 ≤ qN p := by
  intro p hp
  simp only [boxB, Finset.mem_filter] at hp
  obtain ⟨_, h⟩ := hp
  omega

/-- The eight evaluated shells, with their counts. -/
def shellSum (w : ℂ) : ℂ :=
  2 * incGamma1 w (lam * 1) + 2 * incGamma1 w (lam * 4) + 4 * incGamma1 w (lam * 6) + 4 * incGamma1 w (lam * 8)
    + 2 * incGamma1 w (lam * 9) + 4 * incGamma1 w (lam * 12) + 2 * incGamma1 w (lam * 16) + 4 * incGamma1 w (lam * 18)

theorem incGamma1_qN (w : ℂ) (p : ℤ × ℤ) : incGamma1 w (lam * qR p) = incGamma1 w (lam * ((qN p : ℕ) : ℝ)) := by
  rw [qN_cast]

theorem boxS_sum (w : ℂ) : ∑ p ∈ boxS, incGamma1 w (lam * qR p) = shellSum w := by
  simp only [incGamma1_qN]
  have h : boxS.1.map (fun p => incGamma1 w (lam * ((qN p : ℕ) : ℝ)))
      = (boxS.1.map qN).map (fun k : ℕ => incGamma1 w (lam * (k : ℝ))) := by
    rw [Multiset.map_map]
    rfl
  rw [Finset.sum_eq_multiset_sum, h, boxS_qN]
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_zero, Multiset.sum_zero]
  unfold shellSum
  push_cast
  ring

/-- (c6) off the evaluated shells: a point with `Q ≥ K` is at most `e^(−lam K)/(lam K)`. -/
theorem rest_term_le {w : ℂ} (hw : w.re ≤ 1) {K : ℕ} (hK : 0 < K) {p : ℤ × ℤ} (hp : K ≤ qN p) :
    ‖incGamma1 w (lam * qR p)‖ ≤ Real.exp (-(lam * K)) / (lam * K) := by
  have hl := lam_pos
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hq : (K : ℝ) ≤ qR p := by
    rw [← qN_cast]
    exact_mod_cast hp
  have hb : 0 < lam * K := mul_pos hl hK'
  have hab : lam * K ≤ lam * qR p := mul_le_mul_of_nonneg_left hq hl.le
  calc ‖incGamma1 w (lam * qR p)‖ ≤ Real.exp (-(lam * qR p)) / (lam * qR p) := norm_incGamma1_le hw (hb.trans_le hab)
    _ ≤ Real.exp (-(lam * K)) / (lam * K) :=
        div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) hb hab

theorem norm_rest_le {w : ℂ} (hw : w.re ≤ 1) (s : Finset (ℤ × ℤ)) {K : ℕ} (hK : 0 < K) (h : ∀ p ∈ s, K ≤ qN p) :
    ‖∑ p ∈ s, incGamma1 w (lam * qR p)‖ ≤ s.card * (Real.exp (-(lam * K)) / (lam * K)) := by
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul s (fun p => ‖incGamma1 w (lam * qR p)‖) _ (fun p hp => rest_term_le hw hK (h p hp))
  rwa [nsmul_eq_mul] at this

theorem lam_gt' : 131 / 100 < lam := by
  have h23 : Real.sqrt 23 < 47959 / 10000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs := sqrt23_pos
  unfold lam
  rw [lt_div_iff₀ hs]
  linarith [Real.pi_gt_d4]

theorem exp_neg_nat_le (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 1 / (271828 / 100000) ^ n := by
  have h1 : (271828 / 100000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num) h1 n
  rw [← Real.exp_nat_mul, mul_one] at h
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h

theorem mid_numeric : ((16 : ℕ) : ℝ) * (Real.exp (-(lam * ((23 : ℕ) : ℝ))) / (lam * ((23 : ℕ) : ℝ))) ≤ 5 / 10 ^ 14 := by
  have hl := lam_gt'
  push_cast
  have h1 : Real.exp (-(lam * 23)) ≤ 1 / (271828 / 100000) ^ 30 :=
    (Real.exp_le_exp.mpr (by push_cast; linarith : -(lam * 23) ≤ -((30 : ℕ) : ℝ))).trans (exp_neg_nat_le 30)
  calc (16 : ℝ) * (Real.exp (-(lam * 23)) / (lam * 23)) ≤ 16 * ((1 / (271828 / 100000) ^ 30) / (3013 / 100)) :=
        mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) h1 (by norm_num) (by linarith)) (by norm_num)
    _ ≤ 5 / 10 ^ 14 := by norm_num

theorem big_numeric : ((800 : ℕ) : ℝ) * (Real.exp (-(lam * ((32 : ℕ) : ℝ))) / (lam * ((32 : ℕ) : ℝ))) ≤ 1 / 10 ^ 16 := by
  have hl := lam_gt'
  push_cast
  have h1 : Real.exp (-(lam * 32)) ≤ 1 / (271828 / 100000) ^ 41 :=
    (Real.exp_le_exp.mpr (by push_cast; linarith : -(lam * 32) ≤ -((41 : ℕ) : ℝ))).trans (exp_neg_nat_le 41)
  calc (800 : ℝ) * (Real.exp (-(lam * 32)) / (lam * 32)) ≤ 800 * ((1 / (271828 / 100000) ^ 41) / (4192 / 100)) :=
        mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) h1 (by norm_num) (by linarith)) (by norm_num)
    _ ≤ 1 / 10 ^ 16 := by norm_num

/-- **G4** `lamM w` against the eight evaluated shells, for `Re w ≤ 1`: within `1e-30 + 5e-14 + 1e-16`. -/
theorem lamM_sub_shellSum {w : ℂ} (hw : w.re ≤ 1) :
    ‖lamM w - shellSum w‖ ≤ 1 / 10 ^ 30 + (5 / 10 ^ 14 + 1 / 10 ^ 16) := by
  have hE : ∑ p ∈ trBox.erase 0, incGamma1 w (lam * qR p)
      = shellSum w + ((∑ p ∈ boxM, incGamma1 w (lam * qR p)) + ∑ p ∈ boxB, incGamma1 w (lam * qR p)) := by
    rw [← boxS_sum w, boxM, boxB, Finset.sum_filter_add_sum_filter_not, boxS, boxR, Finset.sum_filter_add_sum_filter_not,
      boxE]
  have hM : ‖∑ p ∈ boxM, incGamma1 w (lam * qR p)‖ ≤ 5 / 10 ^ 14 := by
    refine (norm_rest_le hw boxM (K := 23) (by norm_num) boxM_ge).trans ?_
    rw [boxM_card]
    exact mid_numeric
  have hB : ‖∑ p ∈ boxB, incGamma1 w (lam * qR p)‖ ≤ 1 / 10 ^ 16 := by
    refine (norm_rest_le hw boxB (K := 32) (by norm_num) boxB_ge).trans ?_
    rw [boxB_card]
    exact big_numeric
  have hT := lamM_sub_trunc hw
  rw [hE] at hT
  generalize ∑ p ∈ boxM, incGamma1 w (lam * qR p) = M at hT hM
  generalize ∑ p ∈ boxB, incGamma1 w (lam * qR p) = B at hT hB
  calc ‖lamM w - shellSum w‖ = ‖(lamM w - (shellSum w + (M + B))) + (M + B)‖ := by
        congr 1
        ring
    _ ≤ ‖lamM w - (shellSum w + (M + B))‖ + ‖M + B‖ := norm_add_le _ _
    _ ≤ ‖lamM w - (shellSum w + (M + B))‖ + (‖M‖ + ‖B‖) := add_le_add le_rfl (norm_add_le _ _)
    _ ≤ 1 / 10 ^ 30 + (5 / 10 ^ 14 + 1 / 10 ^ 16) := add_le_add hT (add_le_add hM hB)

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
