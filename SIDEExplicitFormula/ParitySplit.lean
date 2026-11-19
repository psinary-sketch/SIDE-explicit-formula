/-
SIDE-explicit-formula -- SIDEExplicitFormula/ParitySplit.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(6), statement (S4); W-ORD-SIGN-SECTORS) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE SPLIT BY PARITY. A real test function is the sum h = e + o of its even part e and its odd part o; the statements take h in
that form. The autocorrelation of h is the sum of the autocorrelations of e and of o, as functions (`weilTest_parity_split`): at x
it is the integral of h(t) h(t - x) (`weilTest_ofReal_apply`), and the two cross terms cancel, the one by t -> -t and the other by a
shift (`integral_parity_split`). So each of the three terms of the form at h is the sum of its values at e and at o, and so is the
form (`form_parity_split`): the pole term by the additivity of the transform (`poleTerm_parity_split`); the prime sum by (S1)'s
finite sum on one window holding both supports (`primeSum_parity_split`); the archimedean term (`archTerm_parity_split`) by b321's
identity, zeroSide = poleTerm - primeSum + archTerm on each even k twice continuously differentiable with compact support, the zero
side additive by the summability the explicit formula carries unconditionally (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`); no zero is
located or evaluated. The hypotheses are the domain of the form's terms (twice continuously differentiable, compact support) and the
parity of e and o; no premise is bound.
-/
import SIDEExplicitFormula.FormFinite
import SIDEExplicitFormula.TwoPropertyWindow
import Zeta23.ExplicitFormula.Bridge

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-! ### The transform and the three terms, additive -/

/-- The transform is additive on continuous functions with compact support. -/
theorem paperFT_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f)
    (hgs : HasCompactSupport g) (z : ℂ) :
    Zeta23.paperFT (fun u => f u + g u) z = Zeta23.paperFT f z + Zeta23.paperFT g z := by
  have hfi : Integrable (fun u : ℝ => f u * Complex.exp (Complex.I * z * (u : ℂ))) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfs.mul_right
  have hgi : Integrable (fun u : ℝ => g u * Complex.exp (Complex.I * z * (u : ℂ))) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgs.mul_right
  unfold Zeta23.paperFT
  rw [← integral_add hfi hgi]
  congr 1
  ext u
  show (f u + g u) * Complex.exp (Complex.I * z * (u : ℂ)) =
    f u * Complex.exp (Complex.I * z * (u : ℂ)) + g u * Complex.exp (Complex.I * z * (u : ℂ))
  ring

/-- The pole term is additive on continuous functions with compact support. -/
theorem poleTerm_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (hfs : HasCompactSupport f)
    (hgs : HasCompactSupport g) :
    poleTerm (fun x => f x + g x) = poleTerm f + poleTerm g := by
  unfold poleTerm
  rw [paperFT_add hf hg hfs hgs, paperFT_add hf hg hfs hgs]
  ring

/-- A function with compact support vanishes outside some `[-L, L]`. -/
theorem exists_window {k : ℝ → ℂ} (hs : HasCompactSupport k) : ∃ L : ℝ, ∀ u : ℝ, L < |u| → k u = 0 := by
  obtain ⟨Λ, hΛ⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hs
  refine ⟨Λ, fun u hu => ?_⟩
  by_contra h
  exact absurd (hΛ u h) (not_le.mpr hu)

/-- The prime sum is additive on functions with compact support: on one window holding both supports, each is (S1)'s finite sum. -/
theorem primeSum_add {f g : ℝ → ℂ} (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    primeSum (fun x => f x + g x) = primeSum f + primeSum g := by
  obtain ⟨L₁, h₁⟩ := exists_window hfs
  obtain ⟨L₂, h₂⟩ := exists_window hgs
  have hf : ∀ u : ℝ, max L₁ L₂ < |u| → f u = 0 := fun u hu => h₁ u (lt_of_le_of_lt (le_max_left _ _) hu)
  have hg : ∀ u : ℝ, max L₁ L₂ < |u| → g u = 0 := fun u hu => h₂ u (lt_of_le_of_lt (le_max_right _ _) hu)
  have hfg : ∀ u : ℝ, max L₁ L₂ < |u| → f u + g u = 0 := fun u hu => by rw [hf u hu, hg u hu, add_zero]
  rw [primeSum_window (fun x => f x + g x) (max L₁ L₂) hfg, primeSum_window f (max L₁ L₂) hf,
    primeSum_window g (max L₁ L₂) hg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * (f (Real.log n) + g (Real.log n))) =
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * f (Real.log n)) +
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (2 * g (Real.log n))
  ring

/-- The zero side is additive on functions twice continuously differentiable with compact support, each zero sum summable by the
explicit formula. -/
theorem zeroSide_add {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfs : HasCompactSupport f)
    (hgs : HasCompactSupport g) :
    zeroSide (fun x => f x + g x) = zeroSide f + zeroSide g := by
  have Sf := (Zeta23.WeilEF.EF_lit_zetaZeroConfig f hf hfs).1
  have Sg := (Zeta23.WeilEF.EF_lit_zetaZeroConfig g hg hgs).1
  unfold zeroSide
  rw [← Sf.tsum_add Sg]
  congr 1
  ext ρ
  rw [paperFT_add hf.continuous hg.continuous hfs hgs]
  ring

/-- The archimedean term is additive on even functions twice continuously differentiable with compact support: b321's identity at
`f`, at `g` and at their sum, the zero side, the pole term and the prime sum each additive. -/
theorem archTerm_add {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfs : HasCompactSupport f)
    (hgs : HasCompactSupport g) (hfe : ∀ x, f (-x) = f x) (hge : ∀ x, g (-x) = g x) :
    archTerm (fun x => f x + g x) = archTerm f + archTerm g := by
  have hfg : ContDiff ℝ 2 (fun x => f x + g x) := hf.add hg
  have hfgs : HasCompactSupport (fun x => f x + g x) := hfs.add hgs
  have hfge : ∀ x : ℝ, f (-x) + g (-x) = f x + g x := fun x => by rw [hfe, hge]
  have Hs := b321_identity (fun x => f x + g x) hfg hfgs hfge
  have Hf := b321_identity f hf hfs hfe
  have Hg := b321_identity g hg hgs hge
  have HZ := zeroSide_add hf hg hfs hgs
  have HP := poleTerm_add hf.continuous hg.continuous hfs hgs
  have HQ := primeSum_add hfs hgs
  unfold b321Norm at Hs Hf Hg
  linear_combination -Hs + Hf + Hg + HZ - HP + HQ

/-! ### (S4) the split by parity -/

/-- The autocorrelation of real functions at a point is the real integral of `f(t) g(t - x)`. -/
theorem weilTest_ofReal_apply (f g : ℝ → ℝ) (x : ℝ) :
    Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) x = ((∫ t : ℝ, f t * g (t - x) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp only [Zeta23.EF.weilTest, convolution_def, Zeta23.EF.tilde, ContinuousLinearMap.mul_apply',
    Complex.conj_ofReal, neg_sub, Complex.ofReal_mul]

/-- The real integral split by parity: for `e` even and `o` odd, continuous with compact support, the integral of
`(e + o)(t) (e + o)(t - x)` is the sum of the integrals of `e(t) e(t - x)` and `o(t) o(t - x)`; the cross terms cancel. -/
theorem integral_parity_split {e o : ℝ → ℝ} (hec : Continuous e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : Continuous o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) (x : ℝ) :
    ∫ t : ℝ, (e t + o t) * (e (t - x) + o (t - x)) = (∫ t : ℝ, e t * e (t - x)) + ∫ t : ℝ, o t * o (t - x) := by
  have hI : ∀ a b : ℝ → ℝ, Continuous a → Continuous b → HasCompactSupport a →
      Integrable (fun t : ℝ => a t * b (t - x)) := by
    intro a b ha hb has
    exact (ha.mul (hb.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport has.mul_right
  have hEE := hI e e hec hec hes
  have hOO := hI o o hoc hoc hos
  have hEO := hI e o hec hoc hes
  have hOE := hI o e hoc hec hos
  have hA : Integrable (fun t : ℝ => e t * e (t - x) + o t * o (t - x)) := hEE.add hOO
  have hB : Integrable (fun t : ℝ => e t * o (t - x) + o t * e (t - x)) := hEO.add hOE
  have h1 : ∫ t : ℝ, e t * o (t - x) = -∫ t : ℝ, e t * o (t + x) := by
    rw [← integral_neg_eq_self (fun t : ℝ => e t * o (t - x)) volume, ← integral_neg]
    congr 1
    ext t
    show e (-t) * o (-t - x) = -(e t * o (t + x))
    rw [hev, show -t - x = -(t + x) by ring, hodd]
    ring
  have h2 : ∫ t : ℝ, o t * e (t - x) = ∫ t : ℝ, e t * o (t + x) := by
    rw [← integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ => o t * e (t - x)) x]
    congr 1
    ext t
    show o (t + x) * e (t + x - x) = e t * o (t + x)
    rw [add_sub_cancel_right]
    ring
  have hcross : (∫ t : ℝ, e t * o (t - x)) + ∫ t : ℝ, o t * e (t - x) = 0 := by
    rw [h1, h2]
    ring
  have hsplit : (fun t : ℝ => (e t + o t) * (e (t - x) + o (t - x))) =
      fun t => (e t * e (t - x) + o t * o (t - x)) + (e t * o (t - x) + o t * e (t - x)) := by
    ext t
    ring
  rw [hsplit, integral_add hA hB, integral_add hEE hOO, integral_add hEO hOE, hcross, add_zero]

/-- **(S4) The split by parity.** For `e` even and `o` odd, continuous with compact support, the autocorrelation of `h = e + o` is
the sum of the autocorrelations of `e` and of `o`, as functions. -/
theorem weilTest_parity_split {e o : ℝ → ℝ} (hec : Continuous e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : Continuous o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) :
    Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ)) =
      fun x => Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ)) x +
        Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ)) x := by
  funext x
  rw [weilTest_ofReal_apply (fun u => e u + o u) (fun u => e u + o u) x, weilTest_ofReal_apply e e x,
    weilTest_ofReal_apply o o x, integral_parity_split hec hes hev hoc hos hodd x, Complex.ofReal_add]

/-- The autocorrelation of a real function twice continuously differentiable with compact support: twice continuously
differentiable, with compact support, and even. -/
theorem autocorr_facts {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ContDiff ℝ 2 (Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) ∧
      HasCompactSupport (Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) ∧
      ∀ x, Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (-x) =
        Zeta23.EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) x := by
  have hh : ContDiff ℝ 2 (fun u => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hhs : HasCompactSupport (fun u => (g u : ℂ)) := hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  exact ⟨Zeta23.EF.weilTest_contDiff hh hh.continuous hhs, Zeta23.EF.weilTest_hasCompactSupport hhs hhs,
    fun x => weilTest_ofReal_even g x⟩

/-- **(S4), the pole term:** at `h = e + o` it is the sum of its values at `e` and at `o`. -/
theorem poleTerm_parity_split {e o : ℝ → ℝ} (hec : ContDiff ℝ 2 e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : ContDiff ℝ 2 o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) :
    poleTerm (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) =
      poleTerm (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ))) +
        poleTerm (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ))) := by
  obtain ⟨Ke, Kes, -⟩ := autocorr_facts hec hes
  obtain ⟨Ko, Kos, -⟩ := autocorr_facts hoc hos
  rw [weilTest_parity_split hec.continuous hes hev hoc.continuous hos hodd]
  exact poleTerm_add Ke.continuous Ko.continuous Kes Kos

/-- **(S4), the prime sum:** at `h = e + o` it is the sum of its values at `e` and at `o`. -/
theorem primeSum_parity_split {e o : ℝ → ℝ} (hec : ContDiff ℝ 2 e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : ContDiff ℝ 2 o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) :
    primeSum (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) =
      primeSum (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ))) +
        primeSum (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ))) := by
  obtain ⟨-, Kes, -⟩ := autocorr_facts hec hes
  obtain ⟨-, Kos, -⟩ := autocorr_facts hoc hos
  rw [weilTest_parity_split hec.continuous hes hev hoc.continuous hos hodd]
  exact primeSum_add Kes Kos

/-- **(S4), the archimedean term:** at `h = e + o` it is the sum of its values at `e` and at `o`. -/
theorem archTerm_parity_split {e o : ℝ → ℝ} (hec : ContDiff ℝ 2 e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : ContDiff ℝ 2 o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) :
    archTerm (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) =
      archTerm (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ))) +
        archTerm (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ))) := by
  obtain ⟨Ke, Kes, Kee⟩ := autocorr_facts hec hes
  obtain ⟨Ko, Kos, Koe⟩ := autocorr_facts hoc hos
  rw [weilTest_parity_split hec.continuous hes hev hoc.continuous hos hodd]
  exact archTerm_add Ke Ko Kes Kos Kee Koe

/-- **(S4), the form:** for a real test function `h = e + o`, the form at `h` is the sum of its values at the even part and at the
odd part. -/
theorem form_parity_split {e o : ℝ → ℝ} (hec : ContDiff ℝ 2 e) (hes : HasCompactSupport e) (hev : ∀ x, e (-x) = e x)
    (hoc : ContDiff ℝ 2 o) (hos : HasCompactSupport o) (hodd : ∀ x, o (-x) = -o x) :
    poleTerm (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) -
        primeSum (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) +
        archTerm (Zeta23.EF.weilTest (fun u => ((e u + o u : ℝ) : ℂ)) (fun u => ((e u + o u : ℝ) : ℂ))) =
      (poleTerm (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ))) -
          primeSum (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ))) +
          archTerm (Zeta23.EF.weilTest (fun u => (e u : ℂ)) (fun u => (e u : ℂ)))) +
        (poleTerm (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ))) -
          primeSum (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ))) +
          archTerm (Zeta23.EF.weilTest (fun u => (o u : ℂ)) (fun u => (o u : ℂ)))) := by
  rw [poleTerm_parity_split hec hes hev hoc hos hodd, primeSum_parity_split hec hes hev hoc hos hodd,
    archTerm_parity_split hec hes hev hoc hos hodd]
  ring

end B321
end SIDEExplicitFormula
