/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/NodeBase.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (3)(2) and (4) G4) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G4, THE HAND PART. The mid shells `23 ≤ Q ≤ 27` (16 points: 2, 4, 2, 4, 4 at Q = 23, …, 27, by `decide +kernel` over the box) bounded shell by
shell by `rest_term_le` (Shells.lean :76, `norm_incGamma1_le` at the point's own `Q`): `1.2e-14` in place of `mid_numeric`'s `5e-14`, so
`‖lamM w − shellSum w‖ ≤ 1e-30 + 1.2e-14 + 1e-16` for `Re w ≤ 1`. And the conjugate of a disc. No value of `zqFn` is computed here.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.GammaVal
import SIDEExplicitFormula.Schema.ZQ.OffZero.Strip

open ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

theorem boxM_qN : boxM.val.map qN = 23 ::ₘ 23 ::ₘ 24 ::ₘ 24 ::ₘ 24 ::ₘ 24 ::ₘ 25 ::ₘ 25 ::ₘ 26 ::ₘ 26 ::ₘ 26 ::ₘ 26 ::ₘ
    27 ::ₘ 27 ::ₘ 27 ::ₘ 27 ::ₘ 0 := by
  decide +kernel

/-- `e^(−lam K)/(lam K) ≤ (1/2.71828^n)/(1.31 K)` for `n ≤ 1.31 K`. -/
theorem shell_bound_le {K n : ℕ} (hK : 0 < K) (hn : (n : ℝ) ≤ 131 / 100 * K) :
    Real.exp (-(lam * K)) / (lam * K) ≤ (1 / (271828 / 100000) ^ n) / (131 / 100 * K) := by
  have hl := lam_gt'
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : Real.exp (-(lam * K)) ≤ 1 / (271828 / 100000) ^ n :=
    (Real.exp_le_exp.mpr (by nlinarith : -(lam * K) ≤ -(n : ℝ))).trans (exp_neg_nat_le n)
  exact div_le_div₀ (by positivity) h1 (by positivity) (by nlinarith)

theorem mid_sum_le {w : ℂ} (hw : w.re ≤ 1) : ‖∑ p ∈ boxM, incGamma1 w (lam * qR p)‖ ≤ 12 / 10 ^ 15 := by
  have hpt : ∀ p ∈ boxM, ‖incGamma1 w (lam * qR p)‖ ≤
      (fun K : ℕ => Real.exp (-(lam * (K : ℝ))) / (lam * (K : ℝ))) (qN p) := fun p hp =>
    rest_term_le hw (lt_of_lt_of_le (by norm_num) (boxM_ge p hp)) le_rfl
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  have h : boxM.1.map (fun p => (fun K : ℕ => Real.exp (-(lam * (K : ℝ))) / (lam * (K : ℝ))) (qN p))
      = (boxM.1.map qN).map (fun K : ℕ => Real.exp (-(lam * (K : ℝ))) / (lam * (K : ℝ))) := by
    rw [Multiset.map_map]
    rfl
  rw [Finset.sum_eq_multiset_sum, h, boxM_qN]
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_zero, Multiset.sum_zero]
  have b23 := (shell_bound_le (K := 23) (n := 30) (by norm_num) (by norm_num)).trans
    (show (1 / (271828 / 100000 : ℝ) ^ 30) / (131 / 100 * ((23 : ℕ) : ℝ)) ≤ 311 / 10 ^ 17 by norm_num)
  have b24 := (shell_bound_le (K := 24) (n := 31) (by norm_num) (by norm_num)).trans
    (show (1 / (271828 / 100000 : ℝ) ^ 31) / (131 / 100 * ((24 : ℕ) : ℝ)) ≤ 110 / 10 ^ 17 by norm_num)
  have b25 := (shell_bound_le (K := 25) (n := 32) (by norm_num) (by norm_num)).trans
    (show (1 / (271828 / 100000 : ℝ) ^ 32) / (131 / 100 * ((25 : ℕ) : ℝ)) ≤ 39 / 10 ^ 17 by norm_num)
  have b26 := (shell_bound_le (K := 26) (n := 34) (by norm_num) (by norm_num)).trans
    (show (1 / (271828 / 100000 : ℝ) ^ 34) / (131 / 100 * ((26 : ℕ) : ℝ)) ≤ 6 / 10 ^ 17 by norm_num)
  have b27 := (shell_bound_le (K := 27) (n := 35) (by norm_num) (by norm_num)).trans
    (show (1 / (271828 / 100000 : ℝ) ^ 35) / (131 / 100 * ((27 : ℕ) : ℝ)) ≤ 2 / 10 ^ 17 by norm_num)
  linarith

/-- **G4's tail** `lamM w` against the eight evaluated shells, for `Re w ≤ 1`: within `1e-30 + 1.2e-14 + 1e-16`. -/
theorem lamM_sub_shellSum_fine {w : ℂ} (hw : w.re ≤ 1) :
    ‖lamM w - shellSum w‖ ≤ 1 / 10 ^ 30 + (12 / 10 ^ 15 + 1 / 10 ^ 16) := by
  have hE : ∑ p ∈ trBox.erase 0, incGamma1 w (lam * qR p)
      = shellSum w + ((∑ p ∈ boxM, incGamma1 w (lam * qR p)) + ∑ p ∈ boxB, incGamma1 w (lam * qR p)) := by
    rw [← boxS_sum w, boxM, boxB, Finset.sum_filter_add_sum_filter_not, boxS, boxR, Finset.sum_filter_add_sum_filter_not,
      boxE]
  have hM := mid_sum_le hw
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
    _ ≤ 1 / 10 ^ 30 + (12 / 10 ^ 15 + 1 / 10 ^ 16) := add_le_add hT (add_le_add hM hB)

/-- A rational point is in its own disc of radius `0`. -/
theorem inD_self (t : ℚ × ℚ) : inD (qc t) t 0 := by
  unfold inD
  simp

/-- The conjugate of a disc. -/
theorem inD_conj {z : ℂ} {c : ℚ × ℚ} {r : ℚ} (h : inD z c r) : inD (conj z) (c.1, -c.2) r := by
  unfold inD at *
  have e : conj z - qc (c.1, -c.2) = conj (z - qc c) := by
    apply Complex.ext <;> simp [qc_re, qc_im]
  rw [e, Complex.norm_conj]
  exact h

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
