/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Frontier.lean
THIS PROGRAMME'S WORK (act b742, ruling (R352)(3)(b) as amended by the author's word, relay data/b742_s6_plan.txt (4) G5) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G5, THE FRONTIER BOUND. For `z` on the frontier of box A and a check point `p` within `1/200`, with `u = z − cI`, `u' = p − cI`:
`‖lamF z‖ ≥ ‖P̂(u')‖ − ‖P̂(u') − P̂(u)‖ − ‖P̂(u) − T(u)‖ − ‖T(u) − D(u)‖ − ‖D(u) − lamF z‖`, where `D` is the discrete Cauchy
interpolant of `lamF` on `cI + ρ ω^j` (Interp.lean, `B 120`, `R 3`, `ρ 49/100`, `r 5623/10000`), `T` the interpolant of the table values
(Amplify.lean (i), `DELq`), `P̂` the polynomial of the table `ctab` (`ECq`), `L_P` proved at `LPq` (`lp_le`), and `‖P̂(u')‖ ≥ MLO` at the 80
check points (`check_*`). The margin (`margin`) gives `1/10^12 ≤ ‖lamF z‖` on the whole frontier.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.FrontierData

open Complex Metric Set Finset

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- Five-step triangle inequality. -/
theorem chain_le {F D T P P' : ℂ} {a b c d m : ℝ} (h1 : ‖F - D‖ ≤ a) (h2 : ‖D - T‖ ≤ b) (h3 : ‖T - P‖ ≤ c)
    (h4 : ‖P' - P‖ ≤ d) (h5 : m ≤ ‖P'‖) : m - d - c - b - a ≤ ‖F‖ := by
  have e : P' = (P' - P) + (P - T) + (T - D) + (D - F) + F := by ring
  have k1 := norm_add_le ((P' - P) + (P - T) + (T - D) + (D - F)) F
  have k2 := norm_add_le ((P' - P) + (P - T) + (T - D)) (D - F)
  have k3 := norm_add_le ((P' - P) + (P - T)) (T - D)
  have k4 := norm_add_le (P' - P) (P - T)
  rw [← e] at k1
  rw [norm_sub_rev] at h1 h2 h3
  linarith

/-- **The bound at one check point.** -/
theorem bound_at {z : ℂ} {p : ℚ × ℚ} (hz : z ∈ closure boxA) (hp : qc p ∈ closure boxA) (hzp : ‖z - qc p‖ ≤ 1 / 200)
    (hc : MLO ^ 2 ≤ normSqQ (polyQ ctab (qsub p cIq))) : (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  have hu : ‖z - cI‖ ≤ 5623 / 10000 := norm_sub_cI_le hz
  have hu' : ‖qc p - cI‖ ≤ 5623 / 10000 := norm_sub_cI_le hp
  have h1 := DiffContOnCl.norm_sub_discreteCauchy_le (f := lamF) (c := cI) (ω := omg) (u := z - cI) (R := 3)
    (ρ := 49 / 100) (r := 5623 / 10000) (B := 120) (M := 20) (by norm_num) omg_prim (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) lamF_diffContOnCl_ball lamF_sphere_le hu
  have ez : cI + (z - cI) = z := by ring
  rw [ez, discreteCauchy_eq_dcVec] at h1
  have h2 := norm_dcVec_sub_le (E := ℂ) (ω := omg) (u := z - cI) (ρ := 49 / 100) (r := 5623 / 10000) (δ := (DELq : ℝ))
    (M := 20) (by norm_num) omg_prim (by norm_num) hu (v := fun j => lamF (cI + ((49 / 100 : ℝ) : ℂ) * omg ^ j))
    (v' := fun j => qc (vtab.getD j 0)) (fun j hj => V_all j hj)
  have hT : dcVec (fun j => qc (vtab.getD j 0)) omg (49 / 100) 20 (z - cI) = ∑ k ∈ range 20, coefA k * (z - cI) ^ k := by
    rw [dcVec_eq_sum]
    rfl
  rw [hT] at h2
  have h3 := (norm_poly_sub_poly_le (a := coefA) (b := fun k => qc (ctab.getD k 0))
    (e := fun k => ((etab.getD k 0 : ℚ) : ℝ)) 20 hu coef_le).trans ecoef_le
  have hdu : ‖(qc p - cI) - (z - cI)‖ ≤ 1 / 200 := by
    rw [show qc p - cI - (z - cI) = -(z - qc p) by ring, norm_neg]
    exact hzp
  have hLP0 : (0 : ℝ) ≤ (LPq : ℝ) := le_trans (by positivity) lp_le
  have h4 := (norm_poly_sub_le (fun k => qc (ctab.getD k 0)) 20 hu' hu).trans
    (mul_le_mul lp_le hdu (norm_nonneg _) hLP0)
  have hP : polyC ctab (qc p - cI) = qc (polyQ ctab (qsub p cIq)) := by
    rw [qc_polyQ, qc_sub, cI_eq]
    rfl
  have hMLO0 : (0 : ℚ) ≤ MLO := by
    unfold MLO
    norm_num
  have h5 : (MLO : ℝ) ≤ ‖polyC ctab (qc p - cI)‖ := by
    rw [hP]
    exact le_norm_qc hMLO0 hc
  have hch := chain_le h1 h2 h3 h4 h5
  have hm := margin
  linarith

/-- A check point on the closed box, near `z` coordinate by coordinate. -/
theorem edge_close {z : ℂ} {p : ℚ × ℚ} (d1 d2 : ℝ) (hd : d1 + d2 ≤ 1 / 200) (hzc : z ∈ closure boxA)
    (hp1 : x0 ≤ (p.1 : ℝ)) (hp2 : (p.1 : ℝ) ≤ x1) (hp3 : y0 ≤ (p.2 : ℝ)) (hp4 : (p.2 : ℝ) ≤ y1)
    (hx1 : (p.1 : ℝ) - d1 ≤ z.re) (hx2 : z.re ≤ (p.1 : ℝ) + d1) (hy1 : (p.2 : ℝ) - d2 ≤ z.im) (hy2 : z.im ≤ (p.2 : ℝ) + d2)
    (hc : MLO ^ 2 ≤ normSqQ (polyQ ctab (qsub p cIq))) : (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  refine bound_at hzc ?_ ?_ hc
  · rw [closure_boxA, Complex.mem_reProdIm, qc_re, qc_im]
    exact ⟨⟨hp1, hp2⟩, hp3, hp4⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, qc_re, qc_im]
    have e1 : |z.re - (p.1 : ℝ)| ≤ d1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e2 : |z.im - (p.2 : ℝ)| ≤ d2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

theorem edge_bottom {z : ℂ} (hzc : z ∈ closure boxA) (hre : z.re ∈ Icc x0 x1) (him : z.im = y0) :
    (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  obtain ⟨i, hi, hn⟩ := exists_near_grid (a := x0) (h := 1 / 100) (n := 20) (by norm_num) (by norm_num) hre.1
    (by have h := hre.2; simp only [x0, x1] at h ⊢; push_cast; linarith)
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℝ) ≤ 19 := by exact_mod_cast (by omega : i ≤ 19)
  obtain ⟨a1, a2⟩ := abs_le.mp hn
  simp only [x0] at a1 a2
  have him' : z.im = 16190216 / 1000000 := him
  refine edge_close (1 / 200) 0 (by norm_num) hzc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (check_bottom i hi)
  all_goals (try dsimp only)
  all_goals (push_cast [x0, x1, y0, y1]; linarith)

theorem edge_top {z : ℂ} (hzc : z ∈ closure boxA) (hre : z.re ∈ Icc x0 x1) (him : z.im = y1) :
    (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  obtain ⟨i, hi, hn⟩ := exists_near_grid (a := x0) (h := 1 / 100) (n := 20) (by norm_num) (by norm_num) hre.1
    (by have h := hre.2; simp only [x0, x1] at h ⊢; push_cast; linarith)
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℝ) ≤ 19 := by exact_mod_cast (by omega : i ≤ 19)
  obtain ⟨a1, a2⟩ := abs_le.mp hn
  simp only [x0] at a1 a2
  have him' : z.im = 16390216 / 1000000 := him
  refine edge_close (1 / 200) 0 (by norm_num) hzc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (check_top i hi)
  all_goals (try dsimp only)
  all_goals (push_cast [x0, x1, y0, y1]; linarith)

theorem edge_left {z : ℂ} (hzc : z ∈ closure boxA) (hre : z.re = x0) (him : z.im ∈ Icc y0 y1) :
    (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  obtain ⟨i, hi, hn⟩ := exists_near_grid (a := y0) (h := 1 / 100) (n := 20) (by norm_num) (by norm_num) him.1
    (by have h := him.2; simp only [y0, y1] at h ⊢; push_cast; linarith)
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℝ) ≤ 19 := by exact_mod_cast (by omega : i ≤ 19)
  obtain ⟨a1, a2⟩ := abs_le.mp hn
  simp only [y0] at a1 a2
  have hre' : z.re = 85326 / 100000 := hre
  refine edge_close 0 (1 / 200) (by norm_num) hzc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (check_left i hi)
  all_goals (try dsimp only)
  all_goals (push_cast [x0, x1, y0, y1]; linarith)

theorem edge_right {z : ℂ} (hzc : z ∈ closure boxA) (hre : z.re = x1) (him : z.im ∈ Icc y0 y1) :
    (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  obtain ⟨i, hi, hn⟩ := exists_near_grid (a := y0) (h := 1 / 100) (n := 20) (by norm_num) (by norm_num) him.1
    (by have h := him.2; simp only [y0, y1] at h ⊢; push_cast; linarith)
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℝ) ≤ 19 := by exact_mod_cast (by omega : i ≤ 19)
  obtain ⟨a1, a2⟩ := abs_le.mp hn
  simp only [y0] at a1 a2
  have hre' : z.re = 105326 / 100000 := hre
  refine edge_close 0 (1 / 200) (by norm_num) hzc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (check_right i hi)
  all_goals (try dsimp only)
  all_goals (push_cast [x0, x1, y0, y1]; linarith)

/-- **G5, the frontier**: `1/10^12 ≤ ‖lamF z‖` on the whole frontier of box A. -/
theorem lamF_frontier_ge : ∀ z ∈ frontier boxA, (1 : ℝ) / 10 ^ 12 ≤ ‖lamF z‖ := by
  intro z hz
  have hzc : z ∈ closure boxA := frontier_subset_closure hz
  rcases frontier_boxA_cases hz with ⟨hre, him | him⟩ | ⟨hre | hre, him⟩
  · exact edge_bottom hzc hre him
  · exact edge_top hzc hre him
  · exact edge_left hzc hre him
  · exact edge_right hzc hre him

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
