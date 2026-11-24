import SIDEExplicitFormula.Window.ArithComb
import SIDEExplicitFormula.Window.LogNat
import SIDEExplicitFormula.Window.LogConst
import SIDEExplicitFormula.Window.ArithData

/-!
# L11d, its frame: the three parts of the arithmetic side bounded, reading no datum

By `arith_eq_comb` (L11c) the real part of the arithmetic side at the window is a constant in `k(0)`, `log 23`, `log 2`, `log π`
and Euler's constant, a coefficient `combCoef m` of each `log m` with `2 archC0` beside them, and the prime-power side's terms.
Each part is bounded here by an integer the kernel evaluates, each logarithm taken at the end of its interval of L10 that its
coefficient's sign gives:

* the `m` side (`arithM_le`): `combCoef m` is the integer `arCI m` over `arDc` and `2 archC0` the sum of the integers `arGI` over
  `arDc` (`ar_combCoef_eq`, `ar_archC0_eq`); at each `m ≥ 2`, `log m` lies between the ends of its factorization `nfac m`
  (`logNat_bounds`), and `arSelU` takes the upper end for a coefficient `≥ 0` and the lower for one `< 0`; the integers are read
  from a window of five lists walked over `m` (`arWalk`), so that no list is read at a large index;
* the prime-power side (`arithP_le`): `cQ n` is `∑_p z(n, p) log p` (`cQ_eq_comb`), `Kt n` is read from ktTable, and `arSelL`
  takes the lower end for a coefficient `≥ 0` and the upper for one `< 0`; the bound at each `n` is floored to the integer
  `arTq n` of the table arTqTab, its check `arTqOK` a hypothesis here, evaluated in ArithJoin.lean;
* the constants (`arithK_le`): `k(0) > 0`, so `log 23` at its upper end and `log 2`, `log π` and Euler's constant at their lower.
-/

namespace SIDEExplicitFormula
namespace Window

/-! ## The window of five lists walked over `m` -/

/-- The band's and the far sum's coefficients, `coeffPad`, and the two constants' terms, each read from its head. -/
structure AWin where
  b : List ℤ
  f : List ℤ
  w : List ℤ
  g : List ℤ
  h : List ℤ

/-- Each list moved by one place. -/
def AWin.tl (x : AWin) : AWin := ⟨x.b.tail, x.f.tail, x.w.tail, x.g.tail, x.h.tail⟩

/-- Each list moved by `k` places. -/
def AWin.dr (x : AWin) (k : ℕ) : AWin := ⟨x.b.drop k, x.f.drop k, x.w.drop k, x.g.drop k, x.h.drop k⟩

/-- The window at `m = 0`. -/
def arX0 : AWin := ⟨bandNumL, farNumL, coeffPad, bandGL, farGL⟩

theorem ar_drop_tail {α : Type} : ∀ (l : List α) (k : ℕ), (l.drop k).tail = l.drop (k + 1)
  | [], k => by cases k <;> rfl
  | _ :: _, 0 => rfl
  | _ :: r, k + 1 => by
    show (r.drop k).tail = r.drop (k + 1)
    exact ar_drop_tail r k

theorem ar_dr_tl (x : AWin) (k : ℕ) : (x.dr k).tl = x.dr (k + 1) := by
  simp only [AWin.dr, AWin.tl, ar_drop_tail]

/-! ## The integers at each place -/

/-- The end the sign gives for an upper bound. -/
def arSelU (c L H : ℤ) : ℤ := if 0 ≤ c then c * H else c * L

/-- The end the sign gives for a lower bound. -/
def arSelL (c L H : ℤ) : ℤ := if 0 ≤ c then c * L else c * H

/-- The lower end's numerator over `lpD` at a key of L10's table. -/
def arLo (q : ℕ) : ℤ :=
  match lpTree.find q with
  | some e => (e.L : ℤ)
  | none => 0

/-- The upper end's numerator over `lpD` at a key of L10's table. -/
def arHi (q : ℕ) : ℤ :=
  match lpTree.find q with
  | some e => (e.H : ℤ)
  | none => 0

/-- The factors' lower numerators, each times its exponent, summed. -/
def arFLo : List (ℕ × ℕ) → ℤ
  | [] => 0
  | x :: r => (x.2 : ℤ) * arLo x.1 + arFLo r

/-- The factors' upper numerators, each times its exponent, summed. -/
def arFHi : List (ℕ × ℕ) → ℤ
  | [] => 0
  | x :: r => (x.2 : ℤ) * arHi x.1 + arFHi r

/-- `poleNum m` read at the window of `coeffPad` from `m`. -/
def arPNum (m : ℕ) (w : List ℤ) : ℤ :=
  (m : ℤ) ^ 3 * (bw 0 * w.getD 4 0 + bw 1 * w.getD 3 0 + bw 2 * w.getD 2 0 + bw 3 * w.getD 1 0 + bw 4 * w.getD 0 0)

/-- The numerator of `combCoef m` over `arDc`. -/
def arCI (m : ℕ) (x : AWin) : ℤ :=
  intHNum * (bandDEN : ℤ) * (farDEN : ℤ) * arPNum m x.w + 6 * (farDEN : ℤ) * x.b.getD 0 0 - (bandDEN : ℤ) * x.f.getD 0 0

/-- The numerator of the place's term in `2 archC0` over `arDc`. -/
def arGI (x : AWin) : ℤ := 6 * (farDEN : ℤ) * x.g.getD 0 0 - (bandDEN : ℤ) * x.h.getD 0 0

/-- The upper end of `arCI m * log m`, over `lpD`. -/
def arT (m : ℕ) (x : AWin) : ℤ := if m ≤ 1 then 0 else arSelU (arCI m x) (arFLo (nfac m)) (arFHi (nfac m))

/-- The place's integer: over `arDc * lpD`, an upper end of its two terms. -/
def arP (m : ℕ) (x : AWin) : ℤ := arT m x + arGI x * (lpD : ℤ)

/-- The walk: `k` places from `m`. -/
def arWalk : ℕ → ℕ → AWin → ℤ
  | 0, _, _ => 0
  | k + 1, m, x => arP m x + arWalk k (m + 1) x.tl

/-- A sum of `k` places from `a`. -/
def arSum (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 0
  | a, k + 1 => f a + arSum f (a + 1) k

/-! ## The walk and the sum, read as sums, and their chunks -/

theorem ar_walk_sum : ∀ (k m : ℕ) (x0 : AWin),
    arWalk k m (x0.dr m) = ∑ i ∈ Finset.range k, arP (m + i) (x0.dr (m + i))
  | 0, m, x0 => by
    rw [Finset.sum_range_zero]
    rfl
  | k + 1, m, x0 => by
    have h1 : arWalk (k + 1) m (x0.dr m) = arP m (x0.dr m) + arWalk k (m + 1) (x0.dr (m + 1)) := by
      show arP m (x0.dr m) + arWalk k (m + 1) (x0.dr m).tl = _
      rw [ar_dr_tl]
    rw [h1, ar_walk_sum k (m + 1) x0, Finset.sum_range_succ', Nat.add_zero]
    have h2 : ∑ i ∈ Finset.range k, arP (m + 1 + i) (x0.dr (m + 1 + i)) =
        ∑ i ∈ Finset.range k, arP (m + (i + 1)) (x0.dr (m + (i + 1))) :=
      Finset.sum_congr rfl (fun i _ => by rw [show m + 1 + i = m + (i + 1) by omega])
    rw [h2]
    ring

theorem ar_walk_split (x0 : AWin) (k r a : ℕ) :
    arWalk (k + r) a (x0.dr a) = arWalk k a (x0.dr a) + arWalk r (a + k) (x0.dr (a + k)) := by
  rw [ar_walk_sum (k + r) a x0, ar_walk_sum k a x0, ar_walk_sum r (a + k) x0, Finset.sum_range_add, add_right_inj]
  exact Finset.sum_congr rfl (fun i _ => by rw [show a + (k + i) = a + k + i by omega])

/-- Two chunks of the walk joined. -/
theorem ar_walk_chunk (x0 : AWin) (k r a a' : ℕ) (S1 S2 S : ℤ) (ha : a + k = a')
    (h1 : arWalk k a (x0.dr a) = S1) (h2 : arWalk r a' (x0.dr a') = S2) (hs : S1 + S2 = S) :
    arWalk (k + r) a (x0.dr a) = S := by
  rw [ar_walk_split, ha, h1, h2, hs]

theorem ar_sum_eq (f : ℕ → ℤ) : ∀ (a k : ℕ), arSum f a k = ∑ i ∈ Finset.range k, f (a + i)
  | a, 0 => by
    rw [Finset.sum_range_zero]
    rfl
  | a, k + 1 => by
    show f a + arSum f (a + 1) k = _
    rw [ar_sum_eq f (a + 1) k, Finset.sum_range_succ', Nat.add_zero]
    have h2 : ∑ i ∈ Finset.range k, f (a + 1 + i) = ∑ i ∈ Finset.range k, f (a + (i + 1)) :=
      Finset.sum_congr rfl (fun i _ => by rw [show a + 1 + i = a + (i + 1) by omega])
    rw [h2]
    ring

theorem ar_sum_split (f : ℕ → ℤ) (a k r : ℕ) : arSum f a (k + r) = arSum f a k + arSum f (a + k) r := by
  rw [ar_sum_eq f a (k + r), ar_sum_eq f a k, ar_sum_eq f (a + k) r, Finset.sum_range_add, add_right_inj]
  exact Finset.sum_congr rfl (fun i _ => by rw [show a + (k + i) = a + k + i by omega])

/-- Two chunks of the sum joined. -/
theorem ar_sum_chunk (f : ℕ → ℤ) (k r a a' : ℕ) (S1 S2 S : ℤ) (ha : a + k = a')
    (h1 : arSum f a k = S1) (h2 : arSum f a' r = S2) (hs : S1 + S2 = S) : arSum f a (k + r) = S := by
  rw [ar_sum_split, ha, h1, h2, hs]

/-! ## The ends of L10 as integers over `lpD` -/

theorem ar_lpD_pos : (0 : ℝ) < (lpD : ℝ) := by
  unfold lpD
  norm_num

theorem ar_lo_eq (q : ℕ) : lpTree.lo q = ((arLo q : ℤ) : ℚ) / (lpD : ℚ) := by
  rcases h : lpTree.find q with _ | e
  · simp [LPTree.lo, arLo, h]
  · simp [LPTree.lo, arLo, h]

theorem ar_hi_eq (q : ℕ) : lpTree.hi q = ((arHi q : ℤ) : ℚ) / (lpD : ℚ) := by
  rcases h : lpTree.find q with _ | e
  · simp [LPTree.hi, arHi, h]
  · simp [LPTree.hi, arHi, h]

theorem ar_facLo_eq : ∀ l : List (ℕ × ℕ), lpTree.facLo l = ((arFLo l : ℤ) : ℚ) / (lpD : ℚ)
  | [] => by simp [LPTree.facLo, arFLo]
  | x :: r => by
    simp only [LPTree.facLo, arFLo]
    rw [ar_facLo_eq r, ar_lo_eq x.1]
    push_cast
    ring

theorem ar_facHi_eq : ∀ l : List (ℕ × ℕ), lpTree.facHi l = ((arFHi l : ℤ) : ℚ) / (lpD : ℚ)
  | [] => by simp [LPTree.facHi, arFHi]
  | x :: r => by
    simp only [LPTree.facHi, arFHi]
    rw [ar_facHi_eq r, ar_hi_eq x.1]
    push_cast
    ring

/-- A coefficient times a number in an interval, at most the end its sign gives. -/
theorem ar_selU_le (c L H : ℤ) (x : ℝ) (hL : (L : ℝ) / (lpD : ℝ) ≤ x) (hH : x ≤ (H : ℝ) / (lpD : ℝ)) :
    (c : ℝ) * x ≤ ((arSelU c L H : ℤ) : ℝ) / (lpD : ℝ) := by
  unfold arSelU
  split_ifs with h
  · have hc : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
    rw [Int.cast_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hH hc
  · have hc : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp h))
    rw [Int.cast_mul, mul_div_assoc]
    exact mul_le_mul_of_nonpos_left hL hc

/-- A coefficient times a number in an interval, at least the end its sign gives. -/
theorem ar_selL_le (c L H : ℤ) (x : ℝ) (hL : (L : ℝ) / (lpD : ℝ) ≤ x) (hH : x ≤ (H : ℝ) / (lpD : ℝ)) :
    ((arSelL c L H : ℤ) : ℝ) / (lpD : ℝ) ≤ (c : ℝ) * x := by
  unfold arSelL
  split_ifs with h
  · have hc : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
    rw [Int.cast_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hL hc
  · have hc : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp h))
    rw [Int.cast_mul, mul_div_assoc]
    exact mul_le_mul_of_nonpos_left hH hc

/-! ## The `m` side -/

/-- The common denominator of `combCoef` and `2 archC0`. -/
noncomputable def arDc : ℝ := 48 * 10 ^ coeffScale * 10 ^ coeffScale * (bandDEN : ℝ) * (farDEN : ℝ)

theorem ar_dc_pos : (0 : ℝ) < arDc := by
  unfold arDc bandDEN farDEN
  positivity

theorem ar_pNum_eq (m : ℕ) : arPNum m (coeffPad.drop m) = poleNum m := by
  have h0 : coeffInt (m - 0) = coeffPad.getD (m + 4) 0 := coeffInt_pad m 0 (by norm_num)
  have h1 : coeffInt (m - 1) = coeffPad.getD (m + 3) 0 := coeffInt_pad m 1 (by norm_num)
  have h2 : coeffInt (m - 2) = coeffPad.getD (m + 2) 0 := coeffInt_pad m 2 (by norm_num)
  have h3 : coeffInt (m - 3) = coeffPad.getD (m + 1) 0 := coeffInt_pad m 3 (by norm_num)
  have h4 : coeffInt (m - 4) = coeffPad.getD (m + 0) 0 := coeffInt_pad m 4 (by norm_num)
  unfold arPNum poleNum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, getD_drop_add, h0, h1, h2, h3, h4] <;> ring

theorem ar_cI_eq (m : ℕ) : arCI m (arX0.dr m) =
    intHNum * (bandDEN : ℤ) * (farDEN : ℤ) * poleNum m + 6 * (farDEN : ℤ) * bandNumL.getD m 0 -
      (bandDEN : ℤ) * farNumL.getD m 0 := by
  have hb := getD_drop_add bandNumL m 0
  have hf := getD_drop_add farNumL m 0
  rw [Nat.add_zero] at hb hf
  show intHNum * (bandDEN : ℤ) * (farDEN : ℤ) * arPNum m (coeffPad.drop m) + 6 * (farDEN : ℤ) * (bandNumL.drop m).getD 0 0 -
    (bandDEN : ℤ) * (farNumL.drop m).getD 0 0 = _
  rw [ar_pNum_eq, hb, hf]

theorem ar_gI_eq (m : ℕ) : arGI (arX0.dr m) = 6 * (farDEN : ℤ) * bandGL.getD m 0 - (bandDEN : ℤ) * farGL.getD m 0 := by
  have hb := getD_drop_add bandGL m 0
  have hf := getD_drop_add farGL m 0
  rw [Nat.add_zero] at hb hf
  show 6 * (farDEN : ℤ) * (bandGL.drop m).getD 0 0 - (bandDEN : ℤ) * (farGL.drop m).getD 0 0 = _
  rw [hb, hf]

theorem ar_combCoef_eq (m : ℕ) : combCoef m = ((arCI m (arX0.dr m) : ℤ) : ℝ) / arDc := by
  have hB : (bandDEN : ℝ) ≠ 0 := by
    unfold bandDEN
    norm_num
  have hF : (farDEN : ℝ) ≠ 0 := by
    unfold farDEN
    norm_num
  have hS : (10 : ℝ) ^ coeffScale ≠ 0 := by positivity
  rw [ar_cI_eq]
  unfold combCoef archCoef arDc
  rw [poleCoef_eq]
  push_cast
  first
  | (field_simp; ring)
  | field_simp

theorem ar_archC0_eq : 2 * archC0 = (∑ c ∈ Finset.range 16390, ((arGI (arX0.dr c) : ℤ) : ℝ)) / arDc := by
  have hB : (bandDEN : ℝ) ≠ 0 := by
    unfold bandDEN
    norm_num
  have hF : (farDEN : ℝ) ≠ 0 := by
    unfold farDEN
    norm_num
  have hS : (10 : ℝ) ^ coeffScale ≠ 0 := by positivity
  have hb : ∑ c ∈ Finset.range 16384, (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ) =
      ∑ c ∈ Finset.range 16390, (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ) := by
    refine sum_range_pad 16384 16390 (by norm_num) _ (fun c hc => ?_)
    show (bandGL.getD c 0 : ℝ) / (bandDEN : ℝ) = 0
    have hl : bandGL.length ≤ c := by
      rw [bandGL_len]
      omega
    rw [List.getD_eq_default bandGL 0 hl, Int.cast_zero, zero_div]
  have hf : ∑ c ∈ Finset.range 16369, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) =
      ∑ c ∈ Finset.range 16390, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) := by
    refine sum_range_pad 16369 16390 (by norm_num) _ (fun c hc => ?_)
    show (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) = 0
    have hl : farGL.length ≤ c := by
      rw [farGL_len]
      omega
    rw [List.getD_eq_default farGL 0 hl, Int.cast_zero, zero_div]
  unfold archC0
  rw [hb, hf, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ar_gI_eq]
  unfold arDc
  push_cast
  first
  | (field_simp; ring)
  | field_simp

/-- At each `m`, the place's two terms at most its integer over `arDc * lpD`. -/
theorem ar_termT (m : ℕ) (hm : m ≤ 16389) :
    combCoef m * Real.log m ≤ ((arT m (arX0.dr m) : ℤ) : ℝ) / (lpD : ℝ) / arDc := by
  have hDc : (0 : ℝ) < arDc := ar_dc_pos
  rw [ar_combCoef_eq, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hDc.le
  unfold arT
  split_ifs with h1
  · have hl : Real.log (m : ℝ) = 0 := by
      rcases (by omega : m = 0 ∨ m = 1) with h | h
      · rw [h, Nat.cast_zero, Real.log_zero]
      · rw [h, Nat.cast_one, Real.log_one]
    simp only [hl, mul_zero, Int.cast_zero, zero_div, le_refl]
  · have hb := logNat_bounds m (by omega) (by omega)
    rw [ar_facLo_eq, ar_facHi_eq] at hb
    push_cast at hb
    obtain ⟨hb1, hb2⟩ := hb
    exact ar_selU_le _ _ _ _ hb1 hb2

theorem ar_P_split (m : ℕ) :
    ((arP m (arX0.dr m) : ℤ) : ℝ) / (arDc * (lpD : ℝ)) =
      ((arT m (arX0.dr m) : ℤ) : ℝ) / (lpD : ℝ) / arDc + ((arGI (arX0.dr m) : ℤ) : ℝ) / arDc := by
  have hD : (lpD : ℝ) ≠ 0 := ar_lpD_pos.ne'
  have hDc : arDc ≠ 0 := ar_dc_pos.ne'
  unfold arP
  push_cast
  first
  | (field_simp; ring)
  | field_simp

/-- The walk's integer over `arDc * lpD`. -/
noncomputable def arithA : ℝ := ((arWalk 16390 0 (arX0.dr 0) : ℤ) : ℝ) / (arDc * (lpD : ℝ))

/-- **The `m` side bounded**: `2 archC0` and the coefficients of the `log m`, at most the walk's integer over `arDc * lpD`. -/
theorem arithM_le : 2 * archC0 + ∑ m ∈ Finset.range 16390, combCoef m * Real.log m ≤ arithA := by
  unfold arithA
  rw [ar_walk_sum, ar_archC0_eq, Int.cast_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hm' : m ≤ 16389 := by
    have := Finset.mem_range.mp hm
    omega
  rw [Nat.zero_add, ar_P_split]
  have hT := ar_termT m hm'
  linarith

/-! ## The prime-power side -/

/-- The entry of a table at `n`. -/
def arKtFind : List (ℕ × ℤ) → ℕ → Option ℤ
  | [], _ => none
  | q :: t, n => if q.1 = n then some q.2 else arKtFind t n

theorem ar_ktFind_mem : ∀ (l : List (ℕ × ℤ)) (n : ℕ) (v : ℤ), arKtFind l n = some v → (n, v) ∈ l
  | [], n, v, h => by simp [arKtFind] at h
  | q :: t, n, v, h => by
    simp only [arKtFind] at h
    split_ifs at h with h1
    · have hv : v = q.2 := (Option.some.inj h).symm
      subst hv
      subst h1
      rw [List.mem_cons]
      exact Or.inl rfl
    · exact List.mem_cons_of_mem q (ar_ktFind_mem t n v h)

theorem ar_kt_of_find {n : ℕ} {v : ℤ} (h : arKtFind ktTable n = some v) : Kt n = v := by
  have hm := ar_ktFind_mem ktTable n v h
  have h2 := List.all_eq_true.1 kt_all (n, v) hm
  simp only [ktOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨h3, h4⟩ := h2
  rw [Kt_eq_fast n h3, h4]

/-- `Kt n` as ktTable holds it, `0` off the table. -/
def arKtV (n : ℕ) : ℤ := (arKtFind ktTable n).getD 0

/-- The lower end of `2 z(n, p) Kt(n) log p`, over `lpD`. -/
def arGB (n p : ℕ) : ℤ := if cqZ n p = 0 then 0 else arSelL (2 * cqZ n p * arKtV n) (arLo p) (arHi p)

/-- The lower end of `2 cQ(n) Kt(n)`, over `lpD`. -/
def arBB (n : ℕ) : ℤ := ∑ p ∈ cqPF, arGB n p

/-- The table's entry at `n`. -/
def arTq (n : ℕ) : ℤ := arTqTab.getD (n - 2) 0

/-- The table's entry at `n` at most its bound. -/
def arTqOK (n : ℕ) : Bool := decide (arTq n * (n : ℤ) ^ 4 ≤ arBB n)

/-- The coefficients at `n` all `0`, or `n` in ktTable. -/
def arKtCov (n : ℕ) : Bool := primeList.all (fun p => cqZ n p == 0) || (arKtFind ktTable n).isSome

/-- At each `n`, the table's entry over `80640 * 10 ^ 34 * lpD` at most the prime-power side's term. -/
theorem ar_termB (n : ℕ) (h2 : 2 ≤ n) (hn : n ≤ 1023) (hcov : arKtCov n = true) (htq : arTqOK n = true)
    (hpf : ∀ p ∈ primeList, (lpTree.find p).isSome = true) :
    ((arTq n : ℤ) : ℝ) / (80640 * 10 ^ 34 * (lpD : ℝ)) ≤
      2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) := by
  have hD : (0 : ℝ) < (lpD : ℝ) := ar_lpD_pos
  have hD' : (lpD : ℝ) ≠ 0 := hD.ne'
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn4 : (n : ℝ) ^ 4 ≠ 0 := (pow_pos hn0 4).ne'
  have hp : ∀ p ∈ cqPF, ((arGB n p : ℤ) : ℝ) / (lpD : ℝ) ≤ 2 * (cqZ n p : ℝ) * (Kt n : ℝ) * Real.log p := by
    intro p hp
    unfold arGB
    split_ifs with hz
    · rw [hz]
      simp
    · have hc := hcov
      unfold arKtCov at hc
      rw [Bool.or_eq_true] at hc
      rcases hc with hall | hfind
      · exfalso
        have h0 := List.all_eq_true.1 hall p (mem_cqPF.mp hp)
        simp only [beq_iff_eq] at h0
        exact hz h0
      · rcases hfv : arKtFind ktTable n with _ | v
        · rw [hfv] at hfind
          simp at hfind
        · have hK : Kt n = v := ar_kt_of_find hfv
          have hV : arKtV n = v := by simp [arKtV, hfv]
          have hb := LPTree.bounds lpTree lp_all p (hpf p (mem_cqPF.mp hp))
          rw [ar_lo_eq, ar_hi_eq] at hb
          push_cast at hb
          obtain ⟨hb1, hb2⟩ := hb
          rw [hV, hK]
          have hs := ar_selL_le (2 * cqZ n p * v) (arLo p) (arHi p) (Real.log p) hb1 hb2
          push_cast at hs
          linarith
  have hsum : ((arBB n : ℤ) : ℝ) / (lpD : ℝ) ≤ 2 * Schema.ZQ.cQ n * (Kt n : ℝ) := by
    rw [cQ_eq_comb n hn]
    unfold arBB
    rw [Int.cast_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun p hp' => ?_)
    have h0 := hp p hp'
    linarith
  have htq' : ((arTq n : ℤ) : ℝ) * (n : ℝ) ^ 4 ≤ ((arBB n : ℤ) : ℝ) := by
    simp only [arTqOK, decide_eq_true_eq] at htq
    exact_mod_cast htq
  have hX : ((arTq n : ℤ) : ℝ) * (n : ℝ) ^ 4 / (lpD : ℝ) ≤ 2 * Schema.ZQ.cQ n * (Kt n : ℝ) :=
    le_trans (div_le_div_of_nonneg_right htq' hD.le) hsum
  have e1 : 2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) =
      2 * Schema.ZQ.cQ n * (Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34) := by
    ring
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have e2 : ((arTq n : ℤ) : ℝ) / (80640 * 10 ^ 34 * (lpD : ℝ)) =
      ((arTq n : ℤ) : ℝ) * (n : ℝ) ^ 4 / (lpD : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34) := by
    first
    | (field_simp; ring)
    | field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right hX (by positivity)

/-- The table's sum over `80640 * 10 ^ 34 * lpD`. -/
noncomputable def arithB : ℝ := ((arSum arTq 2 1022 : ℤ) : ℝ) / (80640 * 10 ^ 34 * (lpD : ℝ))

/-- **The prime-power side bounded below** by the table's sum, the checks of ArithJoin.lean as hypotheses. -/
theorem arithP_le (hcov : ∀ n, 2 ≤ n → n ≤ 1023 → arKtCov n = true)
    (htq : ∀ n, 2 ≤ n → n ≤ 1023 → arTqOK n = true)
    (hpf : ∀ p ∈ primeList, (lpTree.find p).isSome = true) :
    arithB ≤ ∑ n ∈ Finset.Ico 2 1024, 2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) := by
  unfold arithB
  rw [ar_sum_eq, Int.cast_sum, Finset.sum_div, Finset.sum_Ico_eq_sum_range, show (1024 : ℕ) - 2 = 1022 from rfl]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  exact ar_termB (2 + i) (by omega) (by omega) (hcov _ (by omega) (by omega)) (htq _ (by omega) (by omega)) hpf

/-! ## The constants -/

theorem ar_kap0_pos : 0 < kap0 := by
  have h : (0 : ℤ) < k0Num := by decide +kernel
  have h' : (0 : ℝ) < (k0Num : ℝ) := by exact_mod_cast h
  unfold kap0
  exact div_pos h' (by positivity)

/-- The constants' upper end. -/
noncomputable def arithE : ℝ :=
  kap0 * (11 / 3 + ((arHi 23 : ℤ) : ℝ) / (lpD : ℝ) - 2 * (((arLo 2 : ℤ) : ℝ) / (lpD : ℝ)) - 2 * ((pLo : ℚ) : ℝ) -
    2 * ((gLo : ℚ) : ℝ))

/-- **The constants bounded**: `k(0) > 0`, `log 23` at its upper end, `log 2`, `log π` and Euler's constant at their lower. -/
theorem arithK_le :
    11 / 3 * kap0 + kap0 * Real.log 23 - 2 * kap0 * Real.log 2 - 2 * kap0 * Real.log Real.pi -
      2 * kap0 * Real.eulerMascheroniConstant ≤ arithE := by
  have hk := ar_kap0_pos
  have k23 : (lpTree.find 23).isSome = true := by decide +kernel
  have k2 : (lpTree.find 2).isSome = true := by decide +kernel
  have b23 := LPTree.bounds lpTree lp_all 23 k23
  have b2 := LPTree.bounds lpTree lp_all 2 k2
  rw [ar_lo_eq, ar_hi_eq] at b23
  rw [ar_lo_eq, ar_hi_eq] at b2
  push_cast at b23 b2
  obtain ⟨-, b23h⟩ := b23
  obtain ⟨b2l, -⟩ := b2
  obtain ⟨hpl, -⟩ := logPi_bounds
  obtain ⟨hgl, -⟩ := gamma_bounds
  have h1 : kap0 * Real.log 23 ≤ kap0 * (((arHi 23 : ℤ) : ℝ) / (lpD : ℝ)) := mul_le_mul_of_nonneg_left b23h hk.le
  have h2 : kap0 * (((arLo 2 : ℤ) : ℝ) / (lpD : ℝ)) ≤ kap0 * Real.log 2 := mul_le_mul_of_nonneg_left b2l hk.le
  have h3 : kap0 * ((pLo : ℚ) : ℝ) ≤ kap0 * Real.log Real.pi := mul_le_mul_of_nonneg_left hpl.le hk.le
  have h4 : kap0 * ((gLo : ℚ) : ℝ) ≤ kap0 * Real.eulerMascheroniConstant := mul_le_mul_of_nonneg_left hgl.le hk.le
  unfold arithE
  linarith

end Window
end SIDEExplicitFormula
