/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/PowerSum.lean
THIS PROGRAMME'S WORK (act b673, ruling (R283)(3)-(5); the plan relay data/b673_v4v5_plan.txt == 2) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

(V4) THE POWER-SUM LEMMA, GENERIC, IN BOTH SIGNS. For finitely many `w_i` of modulus `1`, none equal to `1`, with
multiplicities `m_i ≥ 1`, `B = Σ m_i`, `Q = Σ m_i ^ 2` and `c = Q / (4 B)`: the real part of `s_n = Σ m_i w_i ^ n` is at least
`c` for infinitely many `n` (`powerSum_re_ge_infinitely`, the sign the converse consumes) and at most `-c` for infinitely many
`n` (`powerSum_re_le_neg_infinitely`). The proof is finite, over a window `[N, N + M)`: (i) the window sum of `s_n` is bounded
uniformly in `N` and `M` (`norm_window_le`); (ii) and (ii′) `2 (Re s) ^ 2 = |s| ^ 2 + Re (s ^ 2)`, and the window sums of
`|s_n| ^ 2` and `Re (s_n ^ 2)` expand over pairs into geometric sums of unimodular products, the diagonal of `|s_n| ^ 2`
contributing `M Q` and every other pair a bounded amount (`powerSum_window_sq_ge`); (iii) the squeeze: if `Re s_n < c` across
the window, the chord of `x ^ 2` on `[-B, c]` holds the window's mean square at `B c = Q / 4` and a bounded error, below the
`Q / 2` of (ii) for `M` large (`exists_ge_of_mean_sq`). The sign `-c` is the same squeeze on `-Re s_n`.
Moved here from Schema/LiConverseCfg.lean at b673 with (i)'s two lemmas `norm_geom_sum_le` and `norm_sum_powerSum_le`, their
statements unchanged. A lemma of finite sums: no configuration and no zeta object. The injectivity hypothesis is carried in
the statement as the plan writes it; the bound of (ii) does not consume it.
-/
import SIDEExplicitFormula.Schema.LiCfg

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open Classical

/-! ## (i) the partial sums over a window -/

/-- The partial geometric sums of a unimodular `w ≠ 1` are bounded: `‖Σ_{n<N} w ^ n‖ ≤ 2 / ‖w - 1‖`. -/
theorem norm_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ 2 / ‖w - 1‖ := by
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  rw [geom_sum_eq hw1 N, norm_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num

/-- The power sum's partial sums are bounded uniformly in `N`: `‖Σ_{n<N} Σ_i m_i w_i ^ n‖ ≤ Σ_i m_i (2 / ‖w_i - 1‖)` --
the mean of the power sum over `n < N` tends to `0`. -/
theorem norm_sum_powerSum_le {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (hw1 : ∀ i ∈ s, w i ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ∑ i ∈ s, (m i : ℂ) * w i ^ n‖ ≤ ∑ i ∈ s, (m i : ℝ) * (2 / ‖w i - 1‖) := by
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [← Finset.mul_sum, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_geom_sum_le (hw i hi) (hw1 i hi) N) (Nat.cast_nonneg _)

/-- **(i), over a window:** for a unimodular `w ≠ 1`, `‖Σ_{k<M} w ^ (N + k)‖ ≤ 2 / ‖w - 1‖`, uniformly in `N` and `M`. -/
theorem norm_window_le {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N M : ℕ) :
    ‖∑ k ∈ Finset.range M, w ^ (N + k)‖ ≤ 2 / ‖w - 1‖ := by
  have he : ∑ k ∈ Finset.range M, w ^ (N + k) = w ^ N * ∑ k ∈ Finset.range M, w ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => pow_add w N k
  rw [he, norm_mul, norm_pow, hw, one_pow, one_mul]
  exact norm_geom_sum_le hw hw1 M

/-- The error of a unimodular point in a window: `0` at `1`, `2 / ‖z - 1‖` elsewhere. -/
def eW (z : ℂ) : ℝ := if z = 1 then 0 else 2 / ‖z - 1‖

/-- The real part of a window sum of a unimodular `z`: `M` at `z = 1`, at least `-2 / ‖z - 1‖` elsewhere. -/
theorem re_window_ge (z : ℂ) (hz : ‖z‖ = 1) (N M : ℕ) :
    (if z = 1 then (M : ℝ) else 0) - eW z ≤ (∑ k ∈ Finset.range M, z ^ (N + k)).re := by
  by_cases h : z = 1
  · subst h
    simp [eW]
  · have hle := norm_window_le hz h N M
    have h2 := (abs_le.mp (Complex.abs_re_le_norm (∑ k ∈ Finset.range M, z ^ (N + k)))).1
    simp only [eW, if_neg h]
    linarith

/-! ## (ii) and (ii′) the window sum of the square of the real part -/

/-- `2 (Re S) ^ 2 = Re (S conj S) + Re (S ^ 2)`. -/
theorem two_re_sq (S : ℂ) : 2 * S.re ^ 2 = (S * (starRingEnd ℂ) S).re + (S ^ 2).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_apply, sq, sq, Complex.mul_re]
  ring

/-- `|s_n| ^ 2` over pairs. -/
theorem powerSum_mul_conj {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (n : ℕ) :
    (∑ i ∈ s, (m i : ℂ) * w i ^ n) * (starRingEnd ℂ) (∑ i ∈ s, (m i : ℂ) * w i ^ n) =
      ∑ i ∈ s, ∑ j ∈ s, (((m i : ℝ) * m j : ℝ) : ℂ) * (w i * (starRingEnd ℂ) (w j)) ^ n := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  rw [mul_pow]
  push_cast
  ring

/-- `s_n ^ 2` over pairs. -/
theorem powerSum_sq {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (n : ℕ) :
    (∑ i ∈ s, (m i : ℂ) * w i ^ n) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (((m i : ℝ) * m j : ℝ) : ℂ) * (w i * w j) ^ n := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]
  push_cast
  ring

/-- A window sum of the real part of a double sum, exchanged. -/
theorem re_window_double {ι : Type*} (s : Finset ι) (a : ι → ι → ℝ) (u : ι → ι → ℂ) (N M : ℕ) :
    ∑ k ∈ Finset.range M, (∑ i ∈ s, ∑ j ∈ s, (a i j : ℂ) * u i j ^ (N + k)).re =
      ∑ i ∈ s, ∑ j ∈ s, a i j * (∑ k ∈ Finset.range M, u i j ^ (N + k)).re := by
  simp only [Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)

/-- The bounded error of (ii): `Σ_{i,j} m_i m_j (eW (w_i conj w_j) + eW (w_i w_j))`, independent of the window. -/
def powerSumErr {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, (m i : ℝ) * m j * (eW (w i * (starRingEnd ℂ) (w j)) + eW (w i * w j))

/-- **(ii) and (ii′):** over any window `[N, N + M)`, `2 Σ (Re s_n) ^ 2 ≥ M Σ m_i ^ 2 - powerSumErr`. -/
theorem powerSum_window_sq_ge {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (N M : ℕ) :
    (M : ℝ) * (∑ i ∈ s, (m i : ℝ) ^ 2) - powerSumErr s w m ≤
      2 * ∑ k ∈ Finset.range M, ((∑ i ∈ s, (m i : ℂ) * w i ^ (N + k)).re) ^ 2 := by
  have h1 : 2 * ∑ k ∈ Finset.range M, ((∑ i ∈ s, (m i : ℂ) * w i ^ (N + k)).re) ^ 2 =
      ∑ k ∈ Finset.range M,
          (∑ i ∈ s, ∑ j ∈ s, (((m i : ℝ) * m j : ℝ) : ℂ) * (w i * (starRingEnd ℂ) (w j)) ^ (N + k)).re +
        ∑ k ∈ Finset.range M, (∑ i ∈ s, ∑ j ∈ s, (((m i : ℝ) * m j : ℝ) : ℂ) * (w i * w j) ^ (N + k)).re := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [two_re_sq, powerSum_mul_conj, powerSum_sq]
  rw [h1, re_window_double s (fun i j => (m i : ℝ) * m j) (fun i j => w i * (starRingEnd ℂ) (w j)) N M,
    re_window_double s (fun i j => (m i : ℝ) * m j) (fun i j => w i * w j) N M, ← Finset.sum_add_distrib]
  have hpair : ∀ i ∈ s, ∀ j ∈ s, (if i = j then (m j : ℝ) ^ 2 * M else 0) -
      (m i : ℝ) * m j * (eW (w i * (starRingEnd ℂ) (w j)) + eW (w i * w j)) ≤
      (m i : ℝ) * m j * (∑ k ∈ Finset.range M, (w i * (starRingEnd ℂ) (w j)) ^ (N + k)).re +
        (m i : ℝ) * m j * (∑ k ∈ Finset.range M, (w i * w j) ^ (N + k)).re := by
    intro i hi j hj
    have hu : ‖w i * (starRingEnd ℂ) (w j)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hw i hi, hw j hj, one_mul]
    have hv : ‖w i * w j‖ = 1 := by rw [norm_mul, hw i hi, hw j hj, one_mul]
    have hu1 := re_window_ge _ hu N M
    have hv1 := re_window_ge _ hv N M
    have hmm : (0 : ℝ) ≤ (m i : ℝ) * m j := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hd : (if i = j then (m j : ℝ) ^ 2 * M else 0) ≤
        (m i : ℝ) * m j * (if w i * (starRingEnd ℂ) (w j) = 1 then (M : ℝ) else 0) := by
      by_cases hij : i = j
      · have h11 : w i * (starRingEnd ℂ) (w j) = 1 := by
          rw [← hij, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw i hi]
          norm_num
        rw [if_pos hij, if_pos h11, ← hij]
        exact le_of_eq (by ring)
      · rw [if_neg hij]
        split_ifs <;> positivity
    have hv0 : (0 : ℝ) ≤ (m i : ℝ) * m j * (if w i * w j = 1 then (M : ℝ) else 0) := by
      split_ifs <;> positivity
    have hu2 := mul_le_mul_of_nonneg_left hu1 hmm
    have hv2 := mul_le_mul_of_nonneg_left hv1 hmm
    nlinarith
  have hdiag : ∀ i ∈ s, ∑ j ∈ s, ((if i = j then (m j : ℝ) ^ 2 * M else 0) -
      (m i : ℝ) * m j * (eW (w i * (starRingEnd ℂ) (w j)) + eW (w i * w j))) =
      (m i : ℝ) ^ 2 * M - ∑ j ∈ s, (m i : ℝ) * m j * (eW (w i * (starRingEnd ℂ) (w j)) + eW (w i * w j)) := by
    intro i hi
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, hi, if_true, ↓reduceIte]
  calc (M : ℝ) * (∑ i ∈ s, (m i : ℝ) ^ 2) - powerSumErr s w m
      = ∑ i ∈ s, ∑ j ∈ s, ((if i = j then (m j : ℝ) ^ 2 * M else 0) -
          (m i : ℝ) * m j * (eW (w i * (starRingEnd ℂ) (w j)) + eW (w i * w j))) := by
        rw [Finset.sum_congr rfl hdiag, Finset.sum_sub_distrib, ← Finset.sum_mul, powerSumErr]
        ring
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((m i : ℝ) * m j * (∑ k ∈ Finset.range M, (w i * (starRingEnd ℂ) (w j)) ^ (N + k)).re +
          (m i : ℝ) * m j * (∑ k ∈ Finset.range M, (w i * w j) ^ (N + k)).re) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

/-! ## (iii) the squeeze -/

/-- **(iii), the squeeze, for a real sequence:** if `|x n| ≤ B`, every window sum of `x` is at most `A` in absolute value, and
twice every window sum of `x ^ 2` is at least `M Q - E`, with `0 < Q` and `B c = Q / 4`, then `c ≤ x n` for infinitely
many `n`. -/
theorem exists_ge_of_mean_sq {x : ℕ → ℝ} {B c A E Q : ℝ} (hB : ∀ n, |x n| ≤ B)
    (hA : ∀ N M : ℕ, |∑ k ∈ Finset.range M, x (N + k)| ≤ A)
    (hE : ∀ N M : ℕ, (M : ℝ) * Q - E ≤ 2 * ∑ k ∈ Finset.range M, x (N + k) ^ 2)
    (hQ : 0 < Q) (hBc : B * c = Q / 4) : ∀ N : ℕ, ∃ n ≥ N, c ≤ x n := by
  intro N
  by_contra hno
  push_neg at hno
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 * |c - B| * A + E) / (Q / 2))
  have hM' : 2 * |c - B| * A + E < M * (Q / 2) := by
    rwa [div_lt_iff₀ (by linarith)] at hM
  have hchord : ∀ k ∈ Finset.range M, x (N + k) ^ 2 ≤ (c - B) * x (N + k) + B * c := by
    intro k _
    have h1 := hno (N + k) (Nat.le_add_right N k)
    have h2 := (abs_le.mp (hB (N + k))).1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ x (N + k) + B by linarith) (show (0 : ℝ) ≤ c - x (N + k) by linarith)]
  have hsum : ∑ k ∈ Finset.range M, x (N + k) ^ 2 ≤
      (c - B) * ∑ k ∈ Finset.range M, x (N + k) + M * (B * c) := by
    calc ∑ k ∈ Finset.range M, x (N + k) ^ 2 ≤ ∑ k ∈ Finset.range M, ((c - B) * x (N + k) + B * c) :=
          Finset.sum_le_sum hchord
      _ = (c - B) * ∑ k ∈ Finset.range M, x (N + k) + M * (B * c) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have habs : (c - B) * ∑ k ∈ Finset.range M, x (N + k) ≤ |c - B| * A := by
    calc (c - B) * ∑ k ∈ Finset.range M, x (N + k) ≤ |(c - B) * ∑ k ∈ Finset.range M, x (N + k)| := le_abs_self _
      _ = |c - B| * |∑ k ∈ Finset.range M, x (N + k)| := abs_mul _ _
      _ ≤ |c - B| * A := mul_le_mul_of_nonneg_left (hA N M) (abs_nonneg _)
  have h5 := hE N M
  rw [hBc] at hsum
  nlinarith

/-! ## (V4) the power-sum lemma, both signs -/

/-- The three facts the squeeze consumes, for the power sum. -/
theorem powerSum_facts {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) (hw1 : ∀ i ∈ s, w i ≠ 1) :
    (∀ n, |(∑ i ∈ s, (m i : ℂ) * w i ^ n).re| ≤ ∑ i ∈ s, (m i : ℝ)) ∧
    (∀ N M : ℕ, |∑ k ∈ Finset.range M, (∑ i ∈ s, (m i : ℂ) * w i ^ (N + k)).re| ≤
      ∑ i ∈ s, (m i : ℝ) * (2 / ‖w i - 1‖)) := by
  refine ⟨fun n => ?_, fun N M => ?_⟩
  · refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)))
    rw [norm_mul, norm_pow, hw i hi, one_pow, mul_one, Complex.norm_natCast]
  · rw [← Complex.re_sum]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [Finset.sum_comm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← Finset.mul_sum, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_window_le (hw i hi) (hw1 i hi) N M) (Nat.cast_nonneg _)

/-- The positivity of `Σ m_i` and `Σ m_i ^ 2`, and `B c = Q / 4` at `c = Q / (4 B)`. -/
theorem powerSum_consts {ι : Type*} (s : Finset ι) (m : ι → ℕ) (hs : s.Nonempty) (hm : ∀ i ∈ s, 1 ≤ m i) :
    0 < ∑ i ∈ s, (m i : ℝ) ∧ 0 < ∑ i ∈ s, (m i : ℝ) ^ 2 ∧
      (∑ i ∈ s, (m i : ℝ)) * ((∑ i ∈ s, (m i : ℝ) ^ 2) / (4 * ∑ i ∈ s, (m i : ℝ))) = (∑ i ∈ s, (m i : ℝ) ^ 2) / 4 := by
  have hpos : ∀ i ∈ s, (0 : ℝ) < m i := fun i hi => by
    have : (1 : ℝ) ≤ m i := by exact_mod_cast hm i hi
    linarith
  have hB : 0 < ∑ i ∈ s, (m i : ℝ) := Finset.sum_pos hpos hs
  have hQ : 0 < ∑ i ∈ s, (m i : ℝ) ^ 2 := Finset.sum_pos (fun i hi => pow_pos (hpos i hi) 2) hs
  refine ⟨hB, hQ, ?_⟩
  have hB0 : (∑ i ∈ s, (m i : ℝ)) ≠ 0 := hB.ne'
  field_simp
  try ring

/-- **(V4+), the sign the converse consumes:** for finitely many distinct `w_i` of modulus `1`, none equal to `1`, with
multiplicities `m_i ≥ 1`, the real part of `Σ_i m_i w_i ^ n` is at least `(Σ m_i ^ 2) / (4 Σ m_i)` for infinitely many `n`. -/
theorem powerSum_re_ge_infinitely {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) (hw1 : ∀ i ∈ s, w i ≠ 1) (hinj : Set.InjOn w s) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∀ N : ℕ, ∃ n ≥ N, (∑ i ∈ s, (m i : ℝ) ^ 2) / (4 * ∑ i ∈ s, (m i : ℝ)) ≤
      (∑ i ∈ s, (m i : ℂ) * w i ^ n).re := by
  obtain ⟨_, hQ, hBc⟩ := powerSum_consts s m hs hm
  obtain ⟨hxB, hA⟩ := powerSum_facts s w m hw hw1
  exact exists_ge_of_mean_sq (x := fun n => (∑ i ∈ s, (m i : ℂ) * w i ^ n).re) hxB hA
    (powerSum_window_sq_ge s w m hw) hQ hBc

/-- **(V4−), the power-sum lemma in the other sign:** under the same hypotheses, the real part of `Σ_i m_i w_i ^ n` is at most
`-(Σ m_i ^ 2) / (4 Σ m_i)` for infinitely many `n`. A lemma of finite sums: no configuration and no zeta object. -/
theorem powerSum_re_le_neg_infinitely {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℕ) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) (hw1 : ∀ i ∈ s, w i ≠ 1) (hinj : Set.InjOn w s) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∀ N : ℕ, ∃ n ≥ N, (∑ i ∈ s, (m i : ℂ) * w i ^ n).re ≤
      -((∑ i ∈ s, (m i : ℝ) ^ 2) / (4 * ∑ i ∈ s, (m i : ℝ))) := by
  obtain ⟨_, hQ, hBc⟩ := powerSum_consts s m hs hm
  obtain ⟨hxB, hA⟩ := powerSum_facts s w m hw hw1
  intro N
  obtain ⟨n, hn, h⟩ := exists_ge_of_mean_sq (x := fun n => -(∑ i ∈ s, (m i : ℂ) * w i ^ n).re)
    (B := ∑ i ∈ s, (m i : ℝ)) (A := ∑ i ∈ s, (m i : ℝ) * (2 / ‖w i - 1‖)) (E := powerSumErr s w m)
    (Q := ∑ i ∈ s, (m i : ℝ) ^ 2)
    (fun n => by simp only [abs_neg]; exact hxB n)
    (fun N M => by simp only [Finset.sum_neg_distrib, abs_neg]; exact hA N M)
    (fun N M => by simp only [neg_sq]; exact powerSum_window_sq_ge s w m hw N M) hQ hBc N
  exact ⟨n, hn, by linarith⟩

end Schema
end SIDEExplicitFormula
