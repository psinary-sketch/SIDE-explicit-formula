/-
b729, (R339)(3): (L2) AND THE JOIN. The table loop's values are the Omega recursion's, so `Tab.get (wTab a N) n = Omega(n) · L · b(n)`; with (L1) a
certificate at (D, n0, v, q) concludes the value law at that field. The eighteen certificates are joined in C2Theorem.lean.
-/
import SIDEExplicitFormula.C2Probe.Stub
import Mathlib

namespace C2Walk

theorem wStep_eq (a : Nat → Int) (W : Tab) (n : Nat) (h2 : 2 ≤ n) (hn : n < 65536)
    (hinv : ∀ m, 2 ≤ m → m < n → Tab.get W m = wf a m) : wStep a W n = wf a n := by
  unfold wStep
  rw [divSum_full a W n (by omega), bigOmega_eq n (by omega), wf_rec a n h2 hn]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨⟨hxy, _⟩, h1, h3⟩ := mem_Spair.mp hp
  have hlt : p.1 < n := by
    have hmul : p.1 * 2 ≤ p.1 * p.2 := Nat.mul_le_mul_left p.1 h3
    rw [hxy] at hmul
    omega
  rw [hinv p.1 h1 hlt]

theorem wLoop_inv (a : Nat → Int) : ∀ (k n : Nat) (W : Tab), 2 ≤ n → n + k ≤ 65536 →
    (∀ m, 2 ≤ m → m < n → Tab.get W m = wf a m) →
    ∀ m, 2 ≤ m → m < n + k → Tab.get (wLoop a k n W) m = wf a m := by
  intro k
  induction k with
  | zero =>
    intro n W _ _ hinv m h2 hm
    have h0 : wLoop a 0 n W = W := by
      first
        | rfl
        | simp [wLoop]
    rw [h0]
    exact hinv m h2 (by omega)
  | succ k ih =>
    intro n W h2n hn hinv m h2 hm
    rw [wLoop_succ]
    refine ih (n + 1) _ (by omega) (by omega) ?_ m h2 (by omega)
    intro j h2j hj
    rw [get_set 64 W n j (wStep a W n) (by omega)]
    by_cases hjn : j = n
    · rw [if_pos hjn, hjn]
      exact wStep_eq a W n h2n (by omega) hinv
    · rw [if_neg hjn]
      exact hinv j h2j (by omega)

/-- the loop's table at any a: Omega(n) · L · b(n) for 2 ≤ n ≤ N < 2^16 -/
theorem wTab_get (a : Nat → Int) (N n : Nat) (hN : N < 65536) (h2 : 2 ≤ n) (hn : n ≤ N) : Tab.get (wTab a N) n = wf a n := by
  unfold wTab
  exact wLoop_inv a (N - 1) 2 Tab.leaf le_rfl (by omega) (fun m h1 h3 => by omega) n h2 (by omega)

/-- (L2), PROVED -/
theorem L2_holds : L2 := by
  intro D N n hN h2 hn
  rw [wTab_get (aQ D) N n hN h2 hn, bigOmega_eq n (by omega), bL_eq]
  rfl

theorem allNonneg_spec (W : Tab) : ∀ (k n : Nat), allNonneg W k n = true → ∀ m, n ≤ m → m < n + k → 0 ≤ Tab.get W m := by
  intro k
  induction k with
  | zero =>
    intro n _ m h1 h2
    omega
  | succ k ih =>
    intro n h m h1 h2
    have h0 : allNonneg W (k + 1) n = if 0 ≤ Tab.get W n then allNonneg W k (n + 1) else false := by
      first
        | rfl
        | simp [allNonneg]
        | rw [allNonneg]
    rw [h0] at h
    by_cases hc : 0 ≤ Tab.get W n
    · rw [if_pos hc] at h
      by_cases hm : m = n
      · rw [hm]
        exact hc
      · exact ih (n + 1) h m (by omega) (by omega)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- A CERTIFICATE CONCLUDES THE VALUE LAW AT ITS FIELD -/
theorem law_of_cert (D : Int) (n0 : Nat) (v : Int) (q : Nat) (hD : D ≤ -15) (h2 : 2 ≤ n0) (hN : n0 < 65536) (hc : cert D n0 v q = true) :
    ((q : Int) * bL D n0 = v * 360360) ∧ ∀ n, 2 ≤ n → n < n0 → 0 ≤ bL D n := by
  have hag : ∀ m, m ≤ n0 → aOf (rTab D n0) m = aQ D m := by
    intro m hm
    unfold aOf aQ
    rw [get_rTab_eq D n0 m hD hm (by omega)]
  have hT : ∀ m, 2 ≤ m → m ≤ n0 →
      Tab.get (wTab (aOf (rTab D n0)) n0) m = (ArithmeticFunction.cardFactors m : Int) * bL D m := by
    intro m h2m hm
    rw [wTab_get _ n0 m hN h2m hm, bL_eq]
    unfold wf
    rw [bLa_congr _ _ n0 m hag hm]
  unfold cert at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨_, h1⟩, h3⟩ := hc
  have hpos : ∀ m, 2 ≤ m → (0 : Int) < (ArithmeticFunction.cardFactors m : Int) := by
    intro m hm
    exact_mod_cast cardFactors_pos m hm
  constructor
  · rw [hT n0 h2 le_rfl, bigOmega_eq n0 (by omega), Int.mul_ediv_cancel_left _ (ne_of_gt (hpos n0 h2))] at h1
    exact h1
  · intro n h2n hn
    have h4 := allNonneg_spec _ _ _ h3 n h2n (by omega)
    rw [hT n h2n (by omega)] at h4
    by_contra hneg
    have h5 : bL D n < 0 := by omega
    have h6 := mul_neg_of_pos_of_neg (hpos n h2n) h5
    exact absurd h4 (not_le.mpr h6)

/-- every row of the walk: D ≤ -15, 2 ≤ n0 < 2^16, v < 0, 0 < q -/
theorem walk_facts : ∀ p ∈ walk, p.1 ≤ -15 ∧ 2 ≤ p.2.1 ∧ p.2.1 < 65536 ∧ p.2.2.1 < 0 ∧ 0 < p.2.2.2 := by
  first
    | decide
    | decide +kernel

/-- (L1), PROVED -/
theorem L1_holds : L1 := by
  intro D n0 v q hw n hn
  have h := walk_facts _ hw
  have hlt : n0 < 65536 := h.2.2.1
  exact get_rTab_eq D n0 n h.1 hn (by omega)

/-- THE VALUE LAW FROM THE EIGHTEEN CERTIFICATES -/
theorem value_law_of_certs (hc : ∀ (D : Int) (n0 : Nat) (v : Int) (q : Nat), (D, n0, v, q) ∈ walk → cert D n0 v q = true) : C2ValueLaw := by
  intro D n0 v q hw
  have h := walk_facts _ hw
  exact law_of_cert D n0 v q h.1 h.2.1 h.2.2.1 (hc D n0 v q hw)

theorem bL_low (D : Int) (n : Nat) (hn : n < 2) : bL D n = 0 := by
  rw [bL_eq, bLa_low _ n hn]

/-- THE STATEMENT AS THE RULING WORDS IT: at each row, b(n) ≥ 0 below n0 and b(n0) = v / q < 0, so n0 is the least n with b(n) < 0 and b(n0) is the
    walk's value. -/
theorem least_negative_of_law (hl : C2ValueLaw) (D : Int) (n0 : Nat) (v : Int) (q : Nat) (hw : (D, n0, v, q) ∈ walk) :
    ((q : Int) * bL D n0 = v * 360360) ∧ bL D n0 < 0 ∧ ∀ n, n < n0 → 0 ≤ bL D n := by
  have h := walk_facts _ hw
  obtain ⟨hv, hnn⟩ := hl D n0 v q hw
  have hvneg : v < 0 := h.2.2.2.1
  have hq : (0 : Nat) < q := h.2.2.2.2
  have hq' : (0 : Int) < (q : Int) := by exact_mod_cast hq
  refine ⟨hv, ?_, ?_⟩
  · by_contra hc
    have h0 : 0 ≤ bL D n0 := by omega
    have h1 : 0 ≤ (q : Int) * bL D n0 := mul_nonneg (le_of_lt hq') h0
    rw [hv] at h1
    omega
  · intro n hn
    by_cases h2 : 2 ≤ n
    · exact hnn n h2 hn
    · rw [bL_low D n (by omega)]

end C2Walk
