import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# L10a's frame: rational enclosures of the logarithms of the primes, checked by the kernel

An entry of a table holds a key `p`, the numerators `L` and `H` of its ends over `2 ^ 100`, a series' length `K` and the
factors of `p - 1` as pairs `(q, e)`. The entry's check reads `p - 1` as the product of its factors, each the key of an entry
and below `p`, and `log p = log (p - 1) - log (1 - 1 / p)`, the last within the series' first `K` terms plus or minus Mathlib's
remainder bound (`Real.abs_log_sub_add_sum_range_le`). Where the check holds at every entry, each key's ends hold its logarithm
(`LPTree.bounds`, by strong induction on the key), and each interval is within `2 / 10 ^ 22` (`LPTree.width`).
-/

namespace SIDEExplicitFormula.Window

/-- An entry: the key `p`, the numerators `L` and `H` over `2 ^ 100`, the series' length `K`, the factors of `p - 1`. -/
structure LPEntry where
  p : ℕ
  L : ℕ
  H : ℕ
  K : ℕ
  fac : List (ℕ × ℕ)

/-- The table, a search tree keyed by `p`. -/
inductive LPTree where
  | leaf : LPTree
  | node : LPEntry → LPTree → LPTree → LPTree

/-- The scale of the numerators. -/
def lpD : ℕ := 2 ^ 100

/-- The width each interval is checked within. -/
def lpW : ℚ := 2 / 10 ^ 22

/-- The product of the factors. -/
def facProd : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: r => x.1 ^ x.2 * facProd r

/-- The series' first `k` terms at `1 / p`: `∑_{i < k} (1 / p) ^ (i + 1) / (i + 1)`. -/
def serS (p : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => serS p k + (1 / (p : ℚ)) ^ (k + 1) / ((k : ℚ) + 1)

/-- The remainder bound after `K` terms at `1 / p`. -/
def serE (p K : ℕ) : ℚ := (1 / (p : ℚ)) ^ (K + 1) / (1 - 1 / (p : ℚ))

namespace LPTree

/-- The entry keyed `q`. -/
def find : LPTree → ℕ → Option LPEntry
  | leaf, _ => none
  | node e l r, q => if q = e.p then some e else if q < e.p then find l q else find r q

/-- Every entry meets `f`. -/
def all (f : LPEntry → Bool) : LPTree → Bool
  | leaf => true
  | node e l r => f e && all f l && all f r

/-- The lower end at the key `q`, `0` off the table. -/
def lo (t : LPTree) (q : ℕ) : ℚ :=
  match t.find q with
  | some e => (e.L : ℚ) / lpD
  | none => 0

/-- The upper end at the key `q`, `0` off the table. -/
def hi (t : LPTree) (q : ℕ) : ℚ :=
  match t.find q with
  | some e => (e.H : ℚ) / lpD
  | none => 0

/-- The factors' lower ends, each times its exponent, summed. -/
def facLo (t : LPTree) : List (ℕ × ℕ) → ℚ
  | [] => 0
  | x :: r => (x.2 : ℚ) * t.lo x.1 + facLo t r

/-- The factors' upper ends, each times its exponent, summed. -/
def facHi (t : LPTree) : List (ℕ × ℕ) → ℚ
  | [] => 0
  | x :: r => (x.2 : ℚ) * t.hi x.1 + facHi t r

/-- Each factor a key of the table and below `p`. -/
def facOK (t : LPTree) (p : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | x :: r => (t.find x.1).isSome && decide (x.1 < p) && facOK t p r

/-- The check at an entry. -/
def chk (t : LPTree) (e : LPEntry) : Bool :=
  decide (2 ≤ e.p) && decide (facProd e.fac = e.p - 1) && t.facOK e.p e.fac &&
    decide ((e.L : ℚ) / lpD ≤ t.facLo e.fac + serS e.p e.K - serE e.p e.K) &&
    decide (t.facHi e.fac + serS e.p e.K + serE e.p e.K ≤ (e.H : ℚ) / lpD) &&
    decide ((e.H : ℚ) / lpD - (e.L : ℚ) / lpD ≤ lpW)

theorem find_p (t : LPTree) (q : ℕ) (e : LPEntry) (h : t.find q = some e) : e.p = q := by
  induction t with
  | leaf => simp [find] at h
  | node e' l r ihl ihr =>
    simp only [find] at h
    split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h
      exact h1.symm
    · exact ihl h
    · exact ihr h

theorem all_find (f : LPEntry → Bool) (t : LPTree) (q : ℕ) (e : LPEntry) (ha : t.all f = true)
    (h : t.find q = some e) : f e = true := by
  induction t with
  | leaf => simp [find] at h
  | node e' l r ihl ihr =>
    simp only [all, Bool.and_eq_true] at ha
    obtain ⟨⟨h0, hl⟩, hr⟩ := ha
    simp only [find] at h
    split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h
      exact h0
    · exact ihl hl h
    · exact ihr hr h

theorem lo_eq (t : LPTree) {q : ℕ} {e : LPEntry} (h : t.find q = some e) : t.lo q = (e.L : ℚ) / lpD := by
  simp [lo, h]

theorem hi_eq (t : LPTree) {q : ℕ} {e : LPEntry} (h : t.find q = some e) : t.hi q = (e.H : ℚ) / lpD := by
  simp [hi, h]

end LPTree

theorem serS_cast (p : ℕ) : ∀ K : ℕ,
    ((serS p K : ℚ) : ℝ) = ∑ i ∈ Finset.range K, (1 / (p : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)
  | 0 => by simp [serS]
  | K + 1 => by
    have h : serS p (K + 1) = serS p K + (1 / (p : ℚ)) ^ (K + 1) / ((K : ℚ) + 1) := rfl
    rw [h, Finset.sum_range_succ, ← serS_cast p K]
    push_cast
    try ring

theorem serE_cast (p K : ℕ) : ((serE p K : ℚ) : ℝ) = (1 / (p : ℝ)) ^ (K + 1) / (1 - 1 / (p : ℝ)) := by
  simp only [serE]
  push_cast
  try ring

namespace LPTree

/-- The factors' ends hold the logarithm of their product, given each smaller key's ends hold its logarithm. -/
theorem fac_bounds (t : LPTree) (ht : t.all t.chk = true) (p : ℕ)
    (ih : ∀ q, q < p → (t.find q).isSome = true →
      ((t.lo q : ℚ) : ℝ) ≤ Real.log q ∧ Real.log q ≤ ((t.hi q : ℚ) : ℝ)) :
    ∀ fac : List (ℕ × ℕ), t.facOK p fac = true →
      0 < facProd fac ∧ ((t.facLo fac : ℚ) : ℝ) ≤ Real.log (facProd fac) ∧
        Real.log (facProd fac) ≤ ((t.facHi fac : ℚ) : ℝ)
  | [], _ => by simp [facProd, facLo, facHi]
  | x :: r, hf => by
    simp only [facOK, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨hs, hlt⟩, hr⟩ := hf
    obtain ⟨hP, hrl, hru⟩ := fac_bounds t ht p ih r hr
    obtain ⟨hql, hqu⟩ := ih x.1 hlt hs
    have hx2 : 2 ≤ x.1 := by
      rcases hq : t.find x.1 with _ | e
      · rw [hq] at hs
        simp at hs
      · have hc := all_find _ t x.1 e ht hq
        have hp := find_p t x.1 e hq
        simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨h2, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
        rw [hp] at h2
        exact h2
    have hx0 : (0 : ℝ) < x.1 := by exact_mod_cast (by omega : 0 < x.1)
    have hP0 : (0 : ℝ) < facProd r := by exact_mod_cast hP
    have hprod : ((facProd (x :: r) : ℕ) : ℝ) = (x.1 : ℝ) ^ x.2 * (facProd r : ℝ) := by
      simp [facProd]
    have hlog : Real.log (facProd (x :: r)) = (x.2 : ℝ) * Real.log x.1 + Real.log (facProd r) := by
      rw [hprod, Real.log_mul (pow_pos hx0 _).ne' hP0.ne', Real.log_pow]
    have hlo : ((t.facLo (x :: r) : ℚ) : ℝ) = (x.2 : ℝ) * ((t.lo x.1 : ℚ) : ℝ) + ((t.facLo r : ℚ) : ℝ) := by
      simp [facLo]
    have hhi : ((t.facHi (x :: r) : ℚ) : ℝ) = (x.2 : ℝ) * ((t.hi x.1 : ℚ) : ℝ) + ((t.facHi r : ℚ) : ℝ) := by
      simp [facHi]
    have hx2' : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.mul_pos (pow_pos (by omega) _) hP
    · rw [hlog, hlo]
      exact add_le_add (mul_le_mul_of_nonneg_left hql hx2') hrl
    · rw [hlog, hhi]
      exact add_le_add (mul_le_mul_of_nonneg_left hqu hx2') hru

/-- **Each key's ends hold its logarithm**, where the check holds at every entry. -/
theorem bounds (t : LPTree) (ht : t.all t.chk = true) :
    ∀ q : ℕ, (t.find q).isSome = true →
      ((t.lo q : ℚ) : ℝ) ≤ Real.log q ∧ Real.log q ≤ ((t.hi q : ℚ) : ℝ) := by
  intro q
  refine Nat.strong_induction_on q ?_
  intro q ih hq
  rcases hfq : t.find q with _ | e
  · rw [hfq] at hq
    simp at hq
  have hep : e.p = q := find_p t q e hfq
  have hc : t.chk e = true := all_find _ t q e ht hfq
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h2, hprod⟩, hfac⟩, hlo⟩, hhi⟩, -⟩ := hc
  rw [hep] at h2 hprod hfac hlo hhi
  obtain ⟨-, hFl, hFu⟩ := fac_bounds t ht q (fun q' hq' hs => ih q' hq' hs) e.fac hfac
  rw [lo_eq t hfq, hi_eq t hfq]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hx0 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hx1 : 1 / (q : ℝ) < 1 := by rw [div_lt_one hq0]; exact hq1
  have hab := Real.abs_log_sub_add_sum_range_le (show |1 / (q : ℝ)| < 1 by rw [abs_of_pos hx0]; exact hx1) e.K
  rw [abs_of_pos hx0] at hab
  have hab1 := le_abs_self ((∑ i ∈ Finset.range e.K, (1 / (q : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - 1 / (q : ℝ)))
  have hab2 := neg_abs_le ((∑ i ∈ Finset.range e.K, (1 / (q : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - 1 / (q : ℝ)))
  have hF : ((facProd e.fac : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [hprod, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  have h1x : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by
    rw [sub_div, div_self hq0.ne']
  have hlog1 : Real.log (1 - 1 / (q : ℝ)) = Real.log ((facProd e.fac : ℕ) : ℝ) - Real.log q := by
    rw [h1x, hF, Real.log_div (sub_pos.mpr hq1).ne' hq0.ne']
  have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhi' := (Rat.cast_le (K := ℝ)).mpr hhi
  rw [Rat.cast_sub, Rat.cast_add, serS_cast, serE_cast] at hlo'
  rw [Rat.cast_add, Rat.cast_add, serS_cast, serE_cast] at hhi'
  constructor
  · linarith
  · linarith

/-- **Each key's interval within `2 / 10 ^ 22`**, where the check holds at every entry. -/
theorem width (t : LPTree) (ht : t.all t.chk = true) (q : ℕ) (hq : (t.find q).isSome = true) :
    t.hi q - t.lo q ≤ lpW := by
  rcases hfq : t.find q with _ | e
  · rw [hfq] at hq
    simp at hq
  have hc := all_find _ t q e ht hfq
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [lo_eq t hfq, hi_eq t hfq]
  exact hc.2

/-- The logarithm of a product of keys, between its factors' summed ends. -/
theorem log_facProd (t : LPTree) (ht : t.all t.chk = true) (N : ℕ) (fac : List (ℕ × ℕ))
    (hf : t.facOK N fac = true) :
    ((t.facLo fac : ℚ) : ℝ) ≤ Real.log (facProd fac) ∧ Real.log (facProd fac) ≤ ((t.facHi fac : ℚ) : ℝ) :=
  (fac_bounds t ht N (fun q _ hs => bounds t ht q hs) fac hf).2

end LPTree

end SIDEExplicitFormula.Window
