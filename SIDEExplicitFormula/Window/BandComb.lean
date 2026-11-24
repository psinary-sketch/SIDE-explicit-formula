import SIDEExplicitFormula.Window.BandJoin
import SIDEExplicitFormula.Window.ArchBandLocal
import SIDEExplicitFormula.Window.PoleComb
import SIDEExplicitFormula.Window.AutoConv

/-!
# L9c3: the band as a constant and a coefficient of each `log n`, `n ≤ 16384`

Each row of the band holds the pairs `i, i + D - 3`, `D ≤ 6` (`band_row7`); `lgI i (3 - D)` is a sum of the vectors
`bVec v` against `fPiece` at `i + s` by the closed forms and `lgI_neg` (`band_row16`, the sixteen blocks of `BandWin.lean`).
Each block is shifted to the place `c = i + s` (`shift_pad`, `band_rows`), `fPiece` split into its parts at `log (1 + c)`,
`log c` and none (`band_split`), the `log (1 + c)` part read at `n = c + 1`, and the sums regrouped by `n` (`band_comb`). Each
coefficient is then the place `n` of `bandNumL` over `bandDEN` (`band_coef`, with `bandNumL_place`), each product of two
numerators read at the window of `coeffPad` (`pair_pad`), and the constant the sum of `bandGL` over `bandDEN`.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The pair of a block with offset `D`: `coeff i * coeff (i + D - 3)`. -/
noncomputable def bandPair (i D : ℕ) : ℝ := coeff i * coeff (i + D - 3)

/-- The vector `bVec v` against `fPiece` at `x`. -/
noncomputable def vP (v : ℕ) (x : ℝ) : ℝ := ∑ l : Fin 7, bVec v l * fPiece l x

theorem lgI_v3 {x : ℝ} (hx : 0 < x) : lgI x 3 = vP 0 x := by
  rw [lgI_closed_three hx]
  simp only [vP, bVec]

theorem lgI_v2 {x : ℝ} (hx : 0 < x) : lgI x 2 = vP 1 x + vP 2 (x + 1) := by
  rw [lgI_closed_two hx, add_comm (1 : ℝ) x]
  simp only [vP, bVec]

theorem lgI_v1 {x : ℝ} (hx : 0 < x) : lgI x 1 = vP 3 x + vP 4 (x + 1) + vP 5 (x + 2) := by
  rw [lgI_closed_one hx, add_comm (1 : ℝ) x, add_comm (2 : ℝ) x]
  simp only [vP, bVec]

theorem lgI_v0 {x : ℝ} (hx : 0 < x) : lgI x 0 = vP 6 x + vP 7 (x + 1) + vP 8 (x + 2) + vP 9 (x + 3) := by
  rw [lgI_closed_zero hx, add_comm (1 : ℝ) x, add_comm (2 : ℝ) x, add_comm (3 : ℝ) x]
  simp only [vP, bVec]

theorem lgI_m1 {x : ℝ} (hx : 0 < x) : lgI x (-1) = vP 3 (x + 1) + vP 4 (x + 2) + vP 5 (x + 3) := by
  rw [lgI_neg, lgI_v1 (show (0 : ℝ) < x + 1 by linarith), show x + 1 + 1 = x + 2 by ring,
    show x + 1 + 2 = x + 3 by ring]

theorem lgI_m2 {x : ℝ} (hx : 0 < x) : lgI x (-2) = vP 1 (x + 2) + vP 2 (x + 3) := by
  rw [lgI_neg, lgI_v2 (show (0 : ℝ) < x + 2 by linarith), show x + 2 + 1 = x + 3 by ring]

theorem lgI_m3 {x : ℝ} (hx : 0 < x) : lgI x (-3) = vP 0 (x + 3) := by
  rw [lgI_neg, lgI_v3 (show (0 : ℝ) < x + 3 by linarith)]

/-- One row of the band over the seven offsets `D`. -/
theorem band_row7 (i : ℕ) (hi : 16 ≤ i) :
    ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3), coeff i * coeff j * lgI i ((i : ℝ) - j) =
      ∑ d ∈ Finset.range 7, bandPair i d * lgI i (3 - (d : ℝ)) := by
  have hsub : (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3) ⊆ Finset.Ico (i - 3) (i + 4) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_Ico]
    constructor <;> omega
  have hz : ∀ j ∈ Finset.Ico (i - 3) (i + 4), j ∉ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3) →
      coeff i * coeff j * lgI i ((i : ℝ) - j) = 0 := by
    intro j hj hn
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [coeff_eq_zero_of_not j (fun h => hn ⟨h, by constructor <;> omega⟩), mul_zero, zero_mul]
  rw [Finset.sum_subset hsub hz, Finset.sum_Ico_eq_sum_range, show i + 4 - (i - 3) = 7 by omega]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have e1 : i - 3 + d = i + d - 3 := by omega
  have h3 : ((i - 3 + d : ℕ) : ℝ) = (i : ℝ) - 3 + d := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 3 ≤ i)]
    norm_num
  have e2 : (i : ℝ) - ((i - 3 + d : ℕ) : ℝ) = 3 - (d : ℝ) := by
    rw [h3]
    ring
  unfold bandPair
  rw [e2, e1]

/-- One row of the band as its sixteen blocks. -/
theorem band_row16 (i : ℕ) (hi : 1 ≤ i) :
    ∑ d ∈ Finset.range 7, bandPair i d * lgI i (3 - (d : ℝ)) =
      ∑ b ∈ Finset.range 16, bandPair i (bD b) * vP (bVi b) ((i : ℝ) + (bS b : ℝ)) := by
  have hx : (0 : ℝ) < i := by exact_mod_cast hi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, bS, bD, bVi, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero, show (3 : ℝ) - 0 = 3 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num,
    show (3 : ℝ) - 2 = 1 by norm_num, show (3 : ℝ) - 3 = 0 by norm_num, show (3 : ℝ) - 4 = -1 by norm_num,
    show (3 : ℝ) - 5 = -2 by norm_num, show (3 : ℝ) - 6 = -3 by norm_num]
  rw [lgI_v3 hx, lgI_v2 hx, lgI_v1 hx, lgI_v0 hx, lgI_m1 hx, lgI_m2 hx, lgI_m3 hx]
  ring

theorem shift_pad (f L : ℕ → ℝ) (N s M : ℕ) (hf0 : f 0 = 0) (hfN : ∀ i, N ≤ i → f i = 0) (hM : N + s ≤ M) :
    ∑ i ∈ Finset.range N, f i * L (i + s) = ∑ c ∈ Finset.range M, f (c - s) * L c := by
  have h1 : ∑ c ∈ Finset.range M, f (c - s) * L c = ∑ c ∈ Finset.range (s + (M - s)), f (c - s) * L c := by
    rw [show s + (M - s) = M by omega]
  rw [h1, Finset.sum_range_add]
  have h0 : ∑ c ∈ Finset.range s, f (c - s) * L c = 0 :=
    Finset.sum_eq_zero (fun c hc => by
      rw [Finset.mem_range] at hc
      rw [show c - s = 0 by omega, hf0, zero_mul])
  rw [h0, zero_add]
  have hpad : ∑ i ∈ Finset.range N, f i * L (i + s) = ∑ i ∈ Finset.range (M - s), f i * L (i + s) :=
    sum_range_pad N (M - s) (by omega) _ (fun i hi => by
      show f i * L (i + s) = 0
      rw [hfN i hi, zero_mul])
  rw [hpad]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [show s + c - s = c by omega, add_comm s c]

theorem bandPair_low (i D : ℕ) (h : i < 16) : bandPair i D = 0 := by
  unfold bandPair
  rw [coeff_eq_zero_of_not i (by omega), zero_mul]

theorem bandPair_high (i D : ℕ) (h : 16380 < i) : bandPair i D = 0 := by
  unfold bandPair
  rw [coeff_eq_zero_of_not i (by omega), zero_mul]

/-- The band as its sixteen blocks, each shifted to the place of its vector. -/
theorem band_rows :
    ∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3),
        coeff i * coeff j * lgI i ((i : ℝ) - j) =
      ∑ b ∈ Finset.range 16, ∑ c ∈ Finset.range 16384, bandPair (c - bS b) (bD b) * vP (bVi b) (c : ℝ) := by
  have h1 : ∀ i ∈ Finset.Icc 16 16380,
      ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3), coeff i * coeff j * lgI i ((i : ℝ) - j) =
        ∑ b ∈ Finset.range 16, bandPair i (bD b) * vP (bVi b) ((i + bS b : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨hlo, -⟩ := hi
    rw [band_row7 i hlo, band_row16 i (by omega)]
    simp only [Nat.cast_add]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ i ∈ Finset.Icc 16 16380, ∑ b ∈ Finset.range 16, bandPair i (bD b) * vP (bVi b) ((i + bS b : ℕ) : ℝ) =
      ∑ i ∈ Finset.range 16381, ∑ b ∈ Finset.range 16, bandPair i (bD b) * vP (bVi b) ((i + bS b : ℕ) : ℝ) := by
    refine Finset.sum_subset (fun i hi => ?_) (fun i hr hi => ?_)
    · rw [Finset.mem_Icc] at hi
      rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range] at hr
      rw [Finset.mem_Icc] at hi
      exact Finset.sum_eq_zero (fun b _ => by rw [bandPair_low i (bD b) (by omega), zero_mul])
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨hs, -, -, -⟩ := band_table b (Finset.mem_range.mp hb)
  exact shift_pad (fun i => bandPair i (bD b)) (fun c => vP (bVi b) (c : ℝ)) 16381 (bS b) 16384
    (bandPair_low 0 (bD b) (by norm_num)) (fun i hi => bandPair_high i (bD b) (by omega)) (by omega)

theorem vP_split (v : ℕ) {x : ℝ} (hx : 0 < x) :
    vP v x = bqA v x * Real.log (1 + x) + bqB v x * Real.log x + bqG v x := by
  unfold vP bqA bqB bqG
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [fPiece_form_pos (l : ℕ) hx]
  ring

/-- The coefficient of `log (1 + c)` at the place `c`. -/
noncomputable def bandA (c : ℕ) : ℝ := ∑ b ∈ Finset.range 16, bandPair (c - bS b) (bD b) * bqA (bVi b) (c : ℝ)

/-- The coefficient of `log c` at the place `c`. -/
noncomputable def bandB (c : ℕ) : ℝ := ∑ b ∈ Finset.range 16, bandPair (c - bS b) (bD b) * bqB (bVi b) (c : ℝ)

/-- The part with no logarithm at the place `c`. -/
noncomputable def bandG (c : ℕ) : ℝ := ∑ b ∈ Finset.range 16, bandPair (c - bS b) (bD b) * bqG (bVi b) (c : ℝ)

theorem band_split (c : ℕ) :
    ∑ b ∈ Finset.range 16, bandPair (c - bS b) (bD b) * vP (bVi b) (c : ℝ) =
      bandA c * Real.log (1 + (c : ℝ)) + bandB c * Real.log (c : ℝ) + bandG c := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    have hp : ∀ b, bandPair (0 - bS b) (bD b) = 0 := fun b => by
      rw [Nat.zero_sub]
      exact bandPair_low 0 (bD b) (by norm_num)
    unfold bandA bandB bandG
    simp only [hp, zero_mul, Finset.sum_const_zero, add_zero]
  · have hx : (0 : ℝ) < c := by exact_mod_cast hpos
    unfold bandA bandB bandG
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [vP_split (bVi b) hx]
    ring

theorem bandB_high : bandB 16384 = 0 := by
  unfold bandB
  refine Finset.sum_eq_zero (fun b hb => ?_)
  obtain ⟨hs, -, -, -⟩ := band_table b (Finset.mem_range.mp hb)
  rw [bandPair_high (16384 - bS b) (bD b) (by omega), zero_mul]

/-- The band collected by `n`, as a coefficient of each `log n` and a constant. -/
theorem band_comb :
    ∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3),
        coeff i * coeff j * lgI i ((i : ℝ) - j) =
      ∑ n ∈ Finset.range (16384 + 1), (bandA (n - 1) + bandB n) * Real.log (n : ℝ) +
        ∑ c ∈ Finset.range 16384, bandG c := by
  rw [band_rows, Finset.sum_comm]
  have h2 : ∀ c ∈ Finset.range 16384, ∑ b ∈ Finset.range 16, bandPair (c - bS b) (bD b) * vP (bVi b) (c : ℝ) =
      bandA c * Real.log (1 + (c : ℝ)) + bandB c * Real.log (c : ℝ) + bandG c := fun c _ => band_split c
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_succ]
  have hB : ∑ c ∈ Finset.range 16384, bandB c * Real.log (c : ℝ) =
      ∑ n ∈ Finset.range (16384 + 1), bandB n * Real.log (n : ℝ) := by
    rw [Finset.sum_range_succ _ 16384, bandB_high, zero_mul, add_zero]
  rw [hB, ← Finset.sum_add_distrib, add_left_inj]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem coeffPad_getD_lt (x : ℕ) (hx : x < 20) : coeffPad.getD x 0 = 0 := by
  have hl : x < (List.replicate 20 (0 : ℤ)).length := by
    rw [List.length_replicate]
    exact hx
  rw [coeffPad_eq, List.getD_append _ _ _ _ hl, List.getD_replicate _ hx]

theorem coeffPad_getD (m : ℕ) : coeffPad.getD (m + 4) 0 = coeffInt m := by
  rcases Nat.lt_or_ge m 16 with h1 | h1
  · rw [coeffPad_getD_lt (m + 4) (by omega), coeffInt_eq_zero m (by omega)]
  · have hl : (List.replicate 20 (0 : ℤ)).length ≤ m + 4 := by
      rw [List.length_replicate]
      omega
    rw [coeffPad_eq, List.getD_append_right _ _ _ _ hl, List.length_replicate, show m + 4 - 20 = m - 16 by omega]
    rcases Nat.lt_or_ge 16380 m with h2 | h2
    · have hd : coeffList.length ≤ m - 16 := by
        rw [coeffList_len]
        omega
      rw [List.getD_eq_default _ _ hd, coeffInt_eq_zero m (by omega)]
    · unfold coeffInt
      rw [if_pos ⟨h1, h2⟩]

theorem coeffInt_pad (n u : ℕ) (hu : u ≤ 4) : coeffInt (n - u) = coeffPad.getD (n + (4 - u)) 0 := by
  by_cases h : u ≤ n
  · rw [show n + (4 - u) = n - u + 4 by omega, coeffPad_getD]
  · rw [show n - u = 0 by omega, coeffInt_eq_zero 0 (by omega), coeffPad_getD_lt (n + (4 - u)) (by omega)]

/-- A pair of a block read at the window of `coeffPad`. -/
theorem pair_pad (n u u' D p q : ℕ) (hu : u ≤ 4) (hu' : u' ≤ 4) (hD : u + 3 = u' + D) (hp : p = 4 - u)
    (hq : q = 4 - u') :
    bandPair (n - u) D = ((coeffPad.getD (n + p) 0 : ℤ) : ℝ) * ((coeffPad.getD (n + q) 0 : ℤ) : ℝ) *
      ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  subst hp hq
  unfold bandPair coeff
  by_cases h : u ≤ n
  · rw [show n - u + D - 3 = n - u' by omega, coeffInt_pad n u hu, coeffInt_pad n u' hu']
    ring
  · rw [show n - u = 0 by omega, coeffInt_eq_zero 0 (by omega), coeffPad_getD_lt (n + (4 - u)) (by omega)]
    simp only [Int.cast_zero, zero_div, zero_mul]

theorem pair_padA (n s D : ℕ) (h1 : s ≤ 3) (h2 : s ≤ D) (h3 : D ≤ s + 3) :
    bandPair (n - 1 - s) D = ((coeffPad.getD (n + (3 - s)) 0 : ℤ) : ℝ) * ((coeffPad.getD (n + (D - s)) 0 : ℤ) : ℝ) *
      ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  rw [Nat.sub_sub]
  exact pair_pad n (1 + s) (4 + s - D) D (3 - s) (D - s) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem pair_padB (n s D : ℕ) (h1 : s ≤ 3) (h2 : s ≤ D) (h3 : D ≤ s + 3) :
    bandPair (n - s) D = ((coeffPad.getD (n + (4 - s)) 0 : ℤ) : ℝ) * ((coeffPad.getD (n + (D - s + 1)) 0 : ℤ) : ℝ) *
      ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  exact pair_pad n s (s + 3 - D) D (4 - s) (D - s + 1) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The coefficient of `log n` as the window`s value `bandW n` over `bandDEN`. -/
theorem band_coef (n : ℕ) :
    bandA (n - 1) + bandB n =
      (bandW n (coeffPad.drop n) : ℝ) / (bandDEN : ℝ) * ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  rw [bandW_eq]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, getD_drop_add]
  unfold bandA bandB
  rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := band_table b (Finset.mem_range.mp hb)
  rw [bqA_poly (bVi b) h4 (n - 1), bqB_poly (bVi b) h4 n, pair_padA n (bS b) (bD b) h1 h2 h3,
    pair_padB n (bS b) (bD b) h1 h2 h3]
  ring

/-- The constant`s term at `c` as the window`s value `gWb c` over `bandDEN`. -/
theorem band_gam (c : ℕ) :
    bandG c = (gWb c (coeffPad.drop c) : ℝ) / (bandDEN : ℝ) * ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  rw [gWb_eq]
  simp only [Int.cast_sum, Int.cast_mul, getD_drop_add]
  unfold bandG
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := band_table b (Finset.mem_range.mp hb)
  rw [bqG_poly (bVi b) h4 c, pair_padB c (bS b) (bD b) h1 h2 h3]
  ring

theorem bandNumL_place (n : ℕ) (hn : n < 16385) : bandNumL.getD n 0 = bandW n (coeffPad.drop n) := by
  have h := winOK_spec bandW bandNumL (coeffPad.drop 0) 0 bandNumL_all n (by rw [bandNumL_len]; exact hn)
  rw [h, drop_drop_add, zero_add]

theorem bandGL_place (c : ℕ) (hc : c < 16384) : bandGL.getD c 0 = gWb c (coeffPad.drop c) := by
  have h := winOK_spec gWb bandGL (coeffPad.drop 0) 0 bandGL_all c (by rw [bandGL_len]; exact hc)
  rw [h, drop_drop_add, zero_add]

/-- **L9c3**: the band of `archJ_basis_local` as a coefficient of each `log n`, `n ≤ 16384`, and a constant, read from
the data `bandNumL` and `bandGL` over `bandDEN`, times the square of the numerators' scale. -/
theorem band_final :
    ∑ i ∈ Finset.Icc 16 16380, ∑ j ∈ (Finset.Icc 16 16380).filter (fun j => j ≤ i + 3 ∧ i ≤ j + 3),
        coeff i * coeff j * lgI i ((i : ℝ) - j) =
      (∑ n ∈ Finset.range (16384 + 1), (bandNumL.getD n 0 : ℝ) / (bandDEN : ℝ) * Real.log (n : ℝ) +
        ∑ c ∈ Finset.range 16384, (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ)) *
        ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  rw [band_comb, add_mul, Finset.sum_mul, Finset.sum_mul]
  have hN : ∀ n ∈ Finset.range (16384 + 1), (bandA (n - 1) + bandB n) * Real.log (n : ℝ) =
      (bandNumL.getD n 0 : ℝ) / (bandDEN : ℝ) * Real.log (n : ℝ) * ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
    intro n hn
    have hlt : n < 16385 := by
      have := Finset.mem_range.mp hn
      omega
    rw [band_coef n, bandNumL_place n hlt]
    ring
  have hG : ∀ c ∈ Finset.range 16384, bandG c =
      (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ) * ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
    intro c hc
    rw [band_gam c, bandGL_place c (Finset.mem_range.mp hc)]
  rw [Finset.sum_congr rfl hN, Finset.sum_congr rfl hG]

end Window
end SIDEExplicitFormula
