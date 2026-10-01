/-
SIDE-explicit-formula -- SIDEExplicitFormula/Chi/ZetaBoundsStrip.lean
THIS PROGRAMME'S WORK (act b567, ruling (R177)(6); W-ORD-GRH-WEIL, act three) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE HELD POINT OF Chi/ZetaBounds.lean, CROSSED: THE REPRESENTATION OF `LFunction χ` ON `0 < re s`. For `χ ≠ 1` the partial
sums `S_χ` are bounded (`norm_charPartialSum_le`), and Abel summation gives, where the Dirichlet series converges absolutely,
  `LFunction χ s = s · ∫_{(1,∞)} S_χ(t) t^{−s−1} dt`        (re s > 1; Mathlib's `LSeries_eq_mul_integral`, SumCoeff.lean :137)
(C2). The right side is `s · mellin S_χ (−s)`, and Mathlib's Mellin differentiability (`mellin_differentiableAt_of_isBigO_rpow`,
MellinTransform.lean :401) makes it analytic wherever `S_χ = O(1)` at `∞` and `S_χ = 0` near `0` allow, that is on `0 < re s`
(C3). Both sides analytic on the convex half-plane and equal near `2`, the identity theorem gives the representation on all of
`0 < re s` (C4, `LFunction_eq_mul_integral`). No differentiation under the integral is written here.

Nothing here proves GRH, RH, or any bound on `LFunction χ` in the strip beyond these theorems' own words.
-/
import SIDEExplicitFormula.Chi.ZetaBounds
import Mathlib.NumberTheory.LSeries.SumCoeff

open Complex Filter Topology Set MeasureTheory Asymptotics

noncomputable section

namespace SIDEExplicitFormula
namespace GRHWeil

open DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## (C1) the partial-sum function -/

omit [NeZero N] in
/-- `S_χ` vanishes below `1`: the sum over `Icc 1 ⌊x⌋₊` is empty. -/
theorem charPartialSum_eq_zero_of_lt_one (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : x < 1) :
    charPartialSum χ x = 0 := by
  unfold charPartialSum
  rw [Nat.floor_eq_zero.mpr hx]
  simp

omit [NeZero N] in
/-- `S_χ` is measurable: a function of `⌊x⌋₊`. -/
theorem measurable_charPartialSum (χ : DirichletCharacter ℂ N) : Measurable (charPartialSum χ) :=
  (measurable_from_nat (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, χ (n : ZMod N))).comp Nat.measurable_floor

/-- `S_χ` is locally integrable on `(0, ∞)`: measurable and bounded. -/
theorem locallyIntegrableOn_charPartialSum {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    LocallyIntegrableOn (charPartialSum χ) (Ioi 0) := by
  have hm : MemLp (charPartialSum χ) ⊤ volume :=
    memLp_top_of_bound (measurable_charPartialSum χ).aestronglyMeasurable ((N : ℝ) + 1)
      (Eventually.of_forall fun x => norm_charPartialSum_le h1 x)
  exact (hm.locallyIntegrable le_top).locallyIntegrableOn _

/-! ## (C2) agreement with the L-series on `re s > 1` -/

/-- The partial sums of `χ ≠ 1` at the integers are `O(n⁰)`. -/
theorem charPartialSum_isBigO {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
  refine IsBigO.of_bound ((N : ℝ) + 1) (Eventually.of_forall fun n => ?_)
  have h := norm_charPartialSum_le h1 (n : ℝ)
  unfold charPartialSum at h
  rw [Nat.floor_natCast] at h
  simpa using h

/-- **(C2)** On `re s > 1`: `LFunction χ s = s · ∫_{(1,∞)} S_χ(t) t^{−s−1} dt`, from `LFunction_eq_LSeries` and Mathlib's
`LSeries_eq_mul_integral` with the bounded partial sums. -/
theorem LFunction_eq_mul_integral_of_one_lt_re {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = s * ∫ t in Ioi (1 : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  rw [LFunction_eq_LSeries χ hs,
    LSeries_eq_mul_integral (fun n : ℕ => χ (n : ZMod N)) le_rfl (by linarith)
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) (charPartialSum_isBigO h1)]
  rfl

/-! ## (C3) the right side, analytic on `0 < re s` -/

omit [NeZero N] in
/-- The integral over `(1, ∞)` is the Mellin transform of `S_χ` at `−s` (`S_χ` vanishes on `(0, 1)`). -/
theorem integral_Ioi_one_eq_mellin (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ∫ t in Ioi (1 : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) = mellin (charPartialSum χ) (-s) := by
  unfold mellin
  rw [← integral_Ici_eq_integral_Ioi]
  symm
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ici_subset_Ioi.mpr one_pos)
    fun x hx => ?_).trans ?_
  · have : x < 1 := by simpa using hx.2
    rw [charPartialSum_eq_zero_of_lt_one χ this, smul_zero]
  · refine setIntegral_congr_fun measurableSet_Ici fun x _ => ?_
    rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]

/-- `mellin S_χ` is complex-differentiable at `−s` for `0 < re s`: `S_χ = O(1)` at `∞` and `S_χ = 0` near `0`. -/
theorem differentiableAt_mellin_charPartialSum {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (charPartialSum χ)) (-s) := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrableOn_charPartialSum h1) ?_ (by rw [neg_re]; linarith) ?_ (by rw [neg_re]; linarith)
  · refine IsBigO.of_bound ((N : ℝ) + 1) (Eventually.of_forall fun x => ?_)
    simpa using norm_charPartialSum_le h1 x
  · have h0 : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] charPartialSum χ := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with x hx
      exact (charPartialSum_eq_zero_of_lt_one χ hx).symm
    exact (isBigO_zero _ _).congr' h0 EventuallyEq.rfl

/-- The representation's right side, `s · ∫_{(1,∞)} S_χ(t) t^{−s−1} dt`. -/
def abelRep (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  s * ∫ t in Ioi (1 : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1))

/-- **(C3)** `abelRep χ` is complex-differentiable on `0 < re s`. -/
theorem differentiableOn_abelRep {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) :
    DifferentiableOn ℂ (abelRep χ) {s : ℂ | 0 < s.re} := by
  intro s hs
  have e : abelRep χ = fun z => z * mellin (charPartialSum χ) (-z) := by
    funext z
    unfold abelRep
    rw [integral_Ioi_one_eq_mellin]
  rw [e]
  have hd : DifferentiableAt ℂ (fun z : ℂ => mellin (charPartialSum χ) (-z)) s :=
    (differentiableAt_mellin_charPartialSum h1 hs).comp s
      (differentiableAt_id.neg : DifferentiableAt ℂ (fun z : ℂ => -z) s)
  exact (differentiableAt_id.mul hd).differentiableWithinAt

/-! ## (C4) the representation on `0 < re s` -/

/-- **(C4) THE REPRESENTATION.** For `χ ≠ 1` and `0 < re s`:
`LFunction χ s = s · ∫_{(1,∞)} S_χ(t) t^{−s−1} dt` -- the identity theorem on the convex half-plane, from (C2) near `2`. -/
theorem LFunction_eq_mul_integral {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * ∫ t in Ioi (1 : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} := fun z _ => analyticAt_LFunction h1 z
  have hg : AnalyticOnNhd ℂ (abelRep χ) {z : ℂ | 0 < z.re} := (differentiableOn_abelRep h1).analyticOnNhd hU
  have hpc : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
  have hagree : LFunction χ =ᶠ[𝓝 (2 : ℂ)] abelRep χ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact LFunction_eq_mul_integral_of_one_lt_re h1 hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h2 hagree hs

/-! ## (C5) the HasDerivAt analogue -/

/-- The tail kernel: `S_χ` on `(M, ∞)`, `0` elsewhere. -/
def tailKernel (χ : DirichletCharacter ℂ N) (M : ℕ) : ℝ → ℂ := (Ioi (M : ℝ)).indicator (charPartialSum χ)

/-- A Mellin-form integral of an `(M, ∞)`-restriction is the integral over `(M, ∞)`, for `0 < M`. -/
theorem integral_Ioi_indicator_eq {M : ℝ} (hM : 0 < M) (f : ℝ → ℂ) (w : ℂ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • (Ioi M).indicator f t = ∫ t in Ioi M, (t : ℂ) ^ (w - 1) • f t := by
  have e : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • (Ioi M).indicator f t =
      (Ioi M).indicator (fun t => (t : ℂ) ^ (w - 1) • f t) t := fun t => by
    by_cases h : t ∈ Ioi M
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr hM.le]

omit [NeZero N] in
/-- The tail integral is the Mellin transform of the tail kernel at `−s`. -/
theorem integral_Ioi_eq_mellin_tail (χ : DirichletCharacter ℂ N) {M : ℕ} (hM : 0 < M) (s : ℂ) :
    ∫ t in Ioi (M : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) = mellin (tailKernel χ M) (-s) := by
  unfold mellin tailKernel
  rw [integral_Ioi_indicator_eq (Nat.cast_pos.mpr hM)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]

omit [NeZero N] in
/-- The tail integral with the factor `−log x` is minus the Mellin transform of `log · (tail kernel)` at `−s`. -/
theorem integral_Ioi_log_eq_mellin_tail (χ : DirichletCharacter ℂ N) {M : ℕ} (hM : 0 < M) (s : ℂ) :
    ∫ t in Ioi (M : ℝ), charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) * (-(Real.log t : ℂ)) =
      -mellin (fun t => Real.log t • tailKernel χ M t) (-s) := by
  unfold mellin tailKernel
  have e : ∀ t : ℝ, Real.log t • (Ioi (M : ℝ)).indicator (charPartialSum χ) t =
      (Ioi (M : ℝ)).indicator (fun t => Real.log t • charPartialSum χ t) t := fun t => by
    by_cases h : t ∈ Ioi (M : ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  simp_rw [e]
  rw [integral_Ioi_indicator_eq (Nat.cast_pos.mpr hM), ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, Complex.real_smul, show -s - 1 = -(s + 1) by ring]
  ring

/-- The tail kernel is essentially bounded by `N + 1`. -/
theorem tailKernel_memLp {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (M : ℕ) : MemLp (tailKernel χ M) ⊤ volume :=
  memLp_top_of_bound ((measurable_charPartialSum χ).indicator measurableSet_Ioi).aestronglyMeasurable ((N : ℝ) + 1)
    (Eventually.of_forall fun x => by
      unfold tailKernel
      exact (norm_indicator_le_norm_self (charPartialSum χ) x).trans (norm_charPartialSum_le h1 x))

/-- `s ↦ mellin (tail kernel) (−s)` has derivative `−mellin (log · tail kernel) (−s)` on `0 < re s` (Mathlib's
`mellin_hasDerivAt_of_isBigO_rpow`, MellinTransform.lean :320). -/
theorem hasDerivAt_mellin_tail {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => mellin (tailKernel χ M) (-z))
      (-mellin (fun t => Real.log t • tailKernel χ M t) (-s)) s := by
  have hloc : LocallyIntegrableOn (tailKernel χ M) (Ioi 0) :=
    ((tailKernel_memLp h1 M).locallyIntegrable le_top).locallyIntegrableOn _
  have htop : tailKernel χ M =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound ((N : ℝ) + 1) (Eventually.of_forall fun x => ?_)
    have h : ‖tailKernel χ M x‖ ≤ (N : ℝ) + 1 := by
      unfold tailKernel
      exact (norm_indicator_le_norm_self (charPartialSum χ) x).trans (norm_charPartialSum_le h1 x)
    simpa using h
  have hbot : tailKernel χ M =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    have h0 : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] tailKernel χ M := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (Nat.cast_pos.mpr hM : (0 : ℝ) < M))] with x hx
      show (0 : ℂ) = (Ioi (M : ℝ)).indicator (charPartialSum χ) x
      rw [Set.indicator_of_notMem (notMem_Ioi.mpr (le_of_lt hx))]
    exact (isBigO_zero _ _).congr' h0 EventuallyEq.rfl
  have hd := (mellin_hasDerivAt_of_isBigO_rpow hloc htop (by rw [neg_re]; linarith) hbot
    (by rw [neg_re]; linarith)).2
  have hc := hd.comp s (hasDerivAt_neg' (x := s))
  rw [Function.comp_def] at hc
  exact hc.congr_deriv (by ring)

/-- The analogue of Zeta23's `ζ₀'`: the derivative of `LFunction0 χ M`, term by term. -/
def LFunction0' (χ : DirichletCharacter ℂ N) (M : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) / (n : ℂ) ^ s * (-(Real.log n : ℂ)))
    + charPartialSum χ M * ((Real.log M : ℂ) * (M : ℂ) ^ (-s))
    + (∫ x in Ioi (M : ℝ), charPartialSum χ x * (x : ℂ) ^ (-(s + 1)))
    + s * ∫ x in Ioi (M : ℝ), charPartialSum χ x * (x : ℂ) ^ (-(s + 1)) * (-(Real.log x : ℂ))

/-- **(C5) THE ANALOGUE OF `HasDerivAtZeta0`.** For `χ ≠ 1`, `0 < M` and `0 < re s`, `LFunction0 χ M` has derivative
`LFunction0' χ M s` at `s`: the finite sum and the boundary term by `const_cpow`, the tail integral by Mathlib's Mellin
derivative. -/
theorem hasDerivAt_LFunction0 {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : 0 < s.re) : HasDerivAt (LFunction0 χ M) (LFunction0' χ M s) s := by
  have e : LFunction0 χ M = fun z => (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) * (n : ℂ) ^ (-z))
      - charPartialSum χ M * (M : ℂ) ^ (-z) + z * mellin (tailKernel χ M) (-z) := by
    funext z
    unfold LFunction0
    rw [integral_Ioi_eq_mellin_tail χ hM z]
    simp only [div_eq_mul_inv, Complex.cpow_neg]
  rw [e]
  have hsum : HasDerivAt (fun z => ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) * (n : ℂ) ^ (-z))
      (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) / (n : ℂ) ^ s * (-(Real.log n : ℂ))) s := by
    refine HasDerivAt.fun_sum fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
    refine (((hasDerivAt_neg' (x := s)).const_cpow (c := (n : ℂ)) (Or.inl hn0)).const_mul (χ (n : ZMod N))).congr_deriv ?_
    rw [Complex.natCast_log, div_eq_mul_inv, ← Complex.cpow_neg]
    ring
  have hbd : HasDerivAt (fun z : ℂ => charPartialSum χ M * (M : ℂ) ^ (-z))
      (charPartialSum χ M * ((M : ℂ) ^ (-s) * Complex.log M * (-1))) s :=
    ((hasDerivAt_neg' (x := s)).const_cpow (c := (M : ℂ)) (Or.inl (Nat.cast_ne_zero.mpr hM.ne'))).const_mul _
  have hprod := (hasDerivAt_id s).mul (hasDerivAt_mellin_tail h1 hM hs)
  refine ((hsum.sub hbd).add hprod).congr_deriv ?_
  unfold LFunction0'
  rw [integral_Ioi_eq_mellin_tail χ hM s, integral_Ioi_log_eq_mellin_tail χ hM s, Complex.natCast_log]
  simp only [id]
  ring

/-! ## (C6) the analogue of `Zeta0EqZeta` -/

/-- `χ(0) = 0` for `χ ≠ 1`, so the partial sums from `0` and from `1` agree. -/
theorem sum_Icc_zero_char {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, χ (k : ZMod N) = ∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N) := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (ne_one_of_ne_one h1)
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc, Nat.cast_zero, MulChar.map_nonunit χ not_isUnit_zero, zero_add]

/-- **Abel summation on `[1, M]`** (Mathlib's `sum_mul_eq_sub_sub_integral_mul'`, AbelSummation.lean :175): for `s ≠ 0`,
`Σ_{1 ≤ n ≤ M} χ(n) n^{−s} = S_χ(M) M^{−s} + s ∫_{(1, M]} S_χ(t) t^{−s−1} dt`. -/
theorem sum_eq_abel {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 1 ≤ M) {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) / (n : ℂ) ^ s =
      charPartialSum χ M * (M : ℂ) ^ (-s) + s * ∫ t in Ioc (1 : ℝ) M, charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hf
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (-s * (t : ℂ) ^ (-s - 1)) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hs)
  have hdiff : ∀ t ∈ Icc (1 : ℝ) M, DifferentiableAt ℝ f t := fun t ht =>
    (hderiv t (by linarith [ht.1])).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Icc (1 : ℝ) M) := fun t ht =>
    (continuousAt_const.mul (continuousAt_ofReal_cpow_const t (-s - 1) (Or.inr (by linarith [ht.1])))).continuousWithinAt
  have hint : IntegrableOn (deriv f) (Icc (1 : ℝ) M) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => ((hderiv t (by linarith [ht.1])).deriv).symm) measurableSet_Icc
  have hdiff' : ∀ t ∈ Icc ((1 : ℕ) : ℝ) M, DifferentiableAt ℝ f t := by simpa only [Nat.cast_one] using hdiff
  have hint' : IntegrableOn (deriv f) (Icc ((1 : ℕ) : ℝ) M) := by simpa only [Nat.cast_one] using hint
  have hA := sum_mul_eq_sub_sub_integral_mul' (fun k : ℕ => χ (k : ZMod N)) hM hdiff' hint'
  simp only [Nat.cast_one] at hA
  have hL : ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc 1 M, f n * χ (n : ZMod N) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
    ring
  have hI : ∫ t in Ioc (1 : ℝ) M, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod N) =
      -s * ∫ t in Ioc (1 : ℝ) M, charPartialSum χ t * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hderiv t (by linarith [ht.1])).deriv, sum_Icc_zero_char h1, show -s - 1 = -(s + 1) by ring]
    unfold charPartialSum
    ring
  have hSM : charPartialSum χ M = ∑ k ∈ Finset.Icc 1 M, χ (k : ZMod N) := by
    unfold charPartialSum
    rw [Nat.floor_natCast]
  have h11 : ∑ k ∈ Finset.Icc (1 : ℕ) 1, χ (k : ZMod N) = 1 := by simp
  rw [hL, Finset.Icc_eq_cons_Ioc hM, Finset.sum_cons, hA, hI, sum_Icc_zero_char h1, sum_Icc_zero_char h1, h11, hSM]
  simp only [hf, Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_natCast, map_one]
  ring

/-- `S_χ(t) t^{−s−1}` is integrable on `(1, ∞)` for `0 < re s`: `‖·‖ ≤ (N + 1) t^{−re s − 1}`. -/
theorem integrableOn_Ioi_charPartialSum_cpow {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => charPartialSum χ t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => ((N : ℝ) + 1) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine Integrable.mono' hg ((measurable_charPartialSum χ).mul
    (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have hre : (-(s + 1)).re = -s.re - 1 := by rw [neg_re, add_re, one_re]; ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
  exact mul_le_mul_of_nonneg_right (norm_charPartialSum_le h1 t) (Real.rpow_nonneg ht0.le _)

/-- **(C6) THE ANALOGUE OF `Zeta0EqZeta`.** For `χ ≠ 1`, `1 ≤ M` and `0 < re s`: `LFunction0 χ M s = LFunction χ s`. -/
theorem LFunction0_eq_LFunction {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : LFunction0 χ M s = LFunction χ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rw [LFunction_eq_mul_integral h1 hs, LFunction0, sum_eq_abel h1 hM hs0, ← Ioc_union_Ioi_eq_Ioi hM1,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((integrableOn_Ioi_charPartialSum_cpow h1 hs).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_Ioi_charPartialSum_cpow h1 hs).mono_set (Ioi_subset_Ioi hM1))]
  ring

/-! ## (C7) the analogue of `DerivZeta0EqDerivZeta` -/

/-- **(C7)** For `χ ≠ 1`, `1 ≤ M` and `0 < re s`: `deriv (LFunction0 χ M) s = deriv (LFunction χ) s`. -/
theorem deriv_LFunction0_eq {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : deriv (LFunction0 χ M) s = deriv (LFunction χ) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hU.mem_nhds hs] with z hz
  exact LFunction0_eq_LFunction h1 hM hz

/-- With (C5): `L'(s, χ)` on `0 < re s` is `LFunction0' χ M s` for every `M ≥ 1`. -/
theorem deriv_LFunction_eq {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : deriv (LFunction χ) s = LFunction0' χ M s := by
  rw [← deriv_LFunction0_eq h1 hM hs]
  exact (hasDerivAt_LFunction0 h1 (by omega) hs).deriv

/-! ## (C8) the analogue of `ZetaBnd_aux1b` -/

/-- **(C8)** For `χ ≠ 1`, `1 ≤ M` and `σ > 0`:
`‖∫_{(M,∞)} S_χ(x) x^{−(σ+it)−1} dx‖ ≤ (N + 1) M^{−σ} / σ` (Zeta23's bound has `1/2` where `S_χ` has `N + 1`). -/
theorem norm_integral_tail_le {χ : DirichletCharacter ℂ N} (h1 : χ ≠ 1) {M : ℕ} (hM : 1 ≤ M) {σ t : ℝ}
    (hσ : 0 < σ) :
    ‖∫ x in Ioi (M : ℝ), charPartialSum χ x * (x : ℂ) ^ (-((σ + t * I) + 1))‖ ≤ ((N : ℝ) + 1) * (M : ℝ) ^ (-σ) / σ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hre : (-(((σ : ℂ) + t * I) + 1)).re = -σ - 1 := by simp; ring
  calc ‖∫ x in Ioi (M : ℝ), charPartialSum χ x * (x : ℂ) ^ (-((σ + t * I) + 1))‖
      ≤ ∫ x in Ioi (M : ℝ), ((N : ℝ) + 1) * x ^ (-σ - 1) := by
        refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by linarith) hM0).const_mul _) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : (0 : ℝ) < x := lt_trans hM0 hx
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
        exact mul_le_mul_of_nonneg_right (norm_charPartialSum_le h1 x) (Real.rpow_nonneg hx0.le _)
    _ = ((N : ℝ) + 1) * (M : ℝ) ^ (-σ) / σ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hM0, show -σ - 1 + 1 = -σ by ring,
          neg_div_neg_eq]
        ring

end GRHWeil
end SIDEExplicitFormula
