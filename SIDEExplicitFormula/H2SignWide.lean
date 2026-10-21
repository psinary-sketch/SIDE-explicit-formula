/-
SIDE-explicit-formula -- SIDEExplicitFormula/H2SignWide.lean
THIS PROGRAMME'S WORK (act b701, ruling (R311)(3); the classK widening to W1 ∪ W3, relay data/b701_widening_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE WIDER CLASS AND WHAT COMPILES ON IT. `classK'` (W1 ∪ W3 of relay data/b698_regularity_uses.txt): even, C¹ with an absolutely integrable
second derivative -- `acDeriv`, the derivative an indefinite integral of an integrable `g` -- compactly supported, and a finite sum of
autocorrelations `h ⋆ h~` (`Zeta23.EF.weilTest h h`) of such `h`. `classKsum` (W3 alone) keeps C² and compact support of the summands.
COMPILED HERE: `classK ⊆ classKsum ⊆ classK'`; `h2_sign' → h2_sign` by restriction and so `h2_sign' → RiemannHypothesis`; and the W3
equivalence `h2_sign_sum ↔ RiemannHypothesis` -- its forward half RHChain's argument with the zero term at a real ordinate read as the
finite sum of `|ĥ_i(γ)|²` (`paperFT_finset_sum`, `paperFT_weilTest` at each summand).
NOT STATED HERE, WITH ITS REASON: `RiemannHypothesis → h2_sign'`, the W1 converse -- the vendored explicit formula binds `ContDiff ℝ 2 k`
(`Zeta23.EF.EF_lit`, Zeta23/ExplicitFormula.lean :98, and the binder lines beneath it), so a `classK'` window of `acDeriv` regularity does
not enter it; the re-port is the order W-ORD-EXPLICIT-FORMULA-C1 (PLACE-papers OPEN_TRAILS.md), on the author's word at b701. No sorry.
Nothing here proves RH or h2_sign; the equivalence compiled relates two open statements.
-/
import SIDEExplicitFormula.Seam

open Complex MeasureTheory
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- C¹ with an absolutely integrable second derivative: the derivative is an indefinite integral of an integrable `g`. -/
def acDeriv (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ g : ℝ → ℂ, Integrable g ∧ ∀ x : ℝ, deriv f x = deriv f 0 + ∫ t in (0:ℝ)..x, g t

/-- **The class K' (W1 ∪ W3):** even, `acDeriv`, compactly supported, and a finite sum of autocorrelations `h_i ⋆ h_i~` of `acDeriv`,
compactly supported `h_i`. -/
def classK' (k : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, k (-x) = k x) ∧ acDeriv k ∧ HasCompactSupport k ∧
    ∃ (m : ℕ) (h : Fin m → ℝ → ℂ), (∀ i, acDeriv (h i) ∧ HasCompactSupport (h i)) ∧
      k = fun u => ∑ i, Zeta23.EF.weilTest (h i) (h i) u

/-- **h2 on K', as one Prop:** for every `k` in K', `0 ≤ P(k) - PR(k) + A(k)`. -/
def h2_sign' : Prop :=
  ∀ k : ℝ → ℂ, classK' k → 0 ≤ poleTerm k - primeSum k + archTerm k

/-- **The W3 sub-class:** even, C², compactly supported, and a finite sum of autocorrelations of C², compactly supported `h_i`. -/
def classKsum (k : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, k (-x) = k x) ∧ ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
    ∃ (m : ℕ) (h : Fin m → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (h i) ∧ HasCompactSupport (h i)) ∧
      k = fun u => ∑ i, Zeta23.EF.weilTest (h i) (h i) u

/-- **h2 on the W3 sub-class, as one Prop.** -/
def h2_sign_sum : Prop :=
  ∀ k : ℝ → ℂ, classKsum k → 0 ≤ poleTerm k - primeSum k + archTerm k

/-- A C² function with compact support is `acDeriv`: its second derivative, continuous with compact support, is the density. -/
theorem acDeriv_of_contDiff_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) : acDeriv f := by
  have hint : Integrable (deriv (deriv f)) :=
    (hf.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv.deriv
  refine ⟨hf.of_le (by norm_num), deriv (deriv f), hint, ?_⟩
  intro x
  have hftc := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := x) (deriv f) rfl
    (fun y _ => (hf.deriv'.differentiable le_rfl) y) ((hf.deriv'.continuous_deriv le_rfl).continuousOn)
  rw [hftc]
  ring

/-- **(C1) classK ⊆ classK'.** -/
theorem classK_subset_classK' {k : ℝ → ℂ} (hk : classK k) : classK' k := by
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  refine ⟨he, acDeriv_of_contDiff_two hc hs, hs, 1, fun _ => h, fun _ => ⟨acDeriv_of_contDiff_two hh hhs, hhs⟩, ?_⟩
  funext u
  simp [Fin.sum_univ_one]

/-- classK ⊆ classKsum (one summand). -/
theorem classK_subset_classKsum {k : ℝ → ℂ} (hk : classK k) : classKsum k := by
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  refine ⟨he, hc, hs, 1, fun _ => h, fun _ => ⟨hh, hhs⟩, ?_⟩
  funext u
  simp [Fin.sum_univ_one]

/-- classKsum ⊆ classK' (C² summands are `acDeriv`). -/
theorem classKsum_subset_classK' {k : ℝ → ℂ} (hk : classKsum k) : classK' k := by
  obtain ⟨he, hc, hs, m, h, hh, rfl⟩ := hk
  exact ⟨he, acDeriv_of_contDiff_two hc hs, hs, m, h, fun i => ⟨acDeriv_of_contDiff_two (hh i).1 (hh i).2, (hh i).2⟩, rfl⟩

/-- **(C2) h2 on K' gives h2 on K**, by restriction. -/
theorem h2_sign'_imp_h2_sign : h2_sign' → h2_sign := fun H k hk => H k (classK_subset_classK' hk)

/-- **h2 on K' gives RH**, through `h2_sign_iff_rh`. -/
theorem h2_sign'_imp_rh : h2_sign' → RiemannHypothesis := fun H => h2_sign_iff_rh.mp (h2_sign'_imp_h2_sign H)

/-- `paperFT` is additive over a finite sum of continuous, compactly supported functions. -/
theorem paperFT_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, Continuous (f i))
    (hs : ∀ i ∈ s, HasCompactSupport (f i)) (z : ℂ) :
    Zeta23.paperFT (fun u => ∑ i ∈ s, f i u) z = ∑ i ∈ s, Zeta23.paperFT (f i) z := by
  have hint : ∀ i ∈ s, Integrable (fun u : ℝ => f i u * cexp (I * z * u)) := fun i hi =>
    ((hf i hi).mul (by fun_prop)).integrable_of_hasCompactSupport ((hs i hi).mul_right)
  simp only [Zeta23.paperFT_def]
  calc ∫ u : ℝ, (∑ i ∈ s, f i u) * cexp (I * z * u) = ∫ u : ℝ, ∑ i ∈ s, f i u * cexp (I * z * u) := by
        congr 1
        funext u
        rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∫ u : ℝ, f i u * cexp (I * z * u) := integral_finsetSum s hint

/-- **RH implies h2 on the W3 sub-class.** RHChain's argument: under RH every zero is on the line, so each zero term is `m_ρ Σ_i |ĥ_i(γ_ρ)|²`
(`paperFT_finset_sum`, `paperFT_weilTest` at each summand), and `b321_identity` carries the sign to `poleTerm k - primeSum k + archTerm k`. -/
theorem rh_imp_h2_sign_sum : RiemannHypothesis → h2_sign_sum := by
  intro hRH k hk
  obtain ⟨he, hc, hs, m, h, hh, rfl⟩ := hk
  set k : ℝ → ℂ := fun u => ∑ i, Zeta23.EF.weilTest (h i) (h i) u with hkdef
  have hid := b321_identity k hc hs he
  have hflip : poleTerm k - primeSum k + archTerm k = zeroSide k := by
    rw [hid]
    unfold b321Norm
    rw [one_mul]
  rw [hflip]
  unfold zeroSide
  refine tsum_nonneg fun ρ => ?_
  have hz : Zeta23.IsNontrivialZero (ρ : ℂ) := by
    first
      | exact ρ.2
      | exact (show (ρ : ℂ) ∈ ({z | Zeta23.IsNontrivialZero z} : Set ℂ) by
          rw [← Zeta23.zetaZeroConfig_carrier]; exact ρ.2)
  have hre : (ρ : ℂ).re = 1 / 2 := Zeta23.RH_implies_on_line hRH hz
  have him : (Zeta23.gammaOf (ρ : ℂ)).im = 0 := by
    unfold Zeta23.gammaOf
    rw [Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.sub_re, hre]
    first
      | rw [Complex.div_ofNat_re, Complex.one_re, sub_self, neg_zero]
      | norm_num
  have hcj : conj (Zeta23.gammaOf (ρ : ℂ)) = Zeta23.gammaOf (ρ : ℂ) :=
    Complex.conj_eq_iff_im.mpr him
  have hterm : Zeta23.paperFT k (Zeta23.gammaOf (ρ : ℂ))
      = ∑ i, ((Complex.normSq (Zeta23.paperFT (h i) (Zeta23.gammaOf (ρ : ℂ))) : ℝ) : ℂ) := by
    rw [hkdef, paperFT_finset_sum Finset.univ (fun i => Zeta23.EF.weilTest (h i) (h i))
      (fun i _ => (Zeta23.EF.weilTest_contDiff (hh i).1 (hh i).1.continuous (hh i).2).continuous)
      (fun i _ => Zeta23.EF.weilTest_hasCompactSupport (hh i).2 (hh i).2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Zeta23.EF.paperFT_weilTest (hh i).1.continuous (hh i).1.continuous (hh i).2 (hh i).2, hcj,
      Complex.mul_conj (Zeta23.paperFT (h i) (Zeta23.gammaOf (ρ : ℂ)))]
  have hm : (0 : ℂ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℂ) := by
    first
      | exact Nat.cast_nonneg _
      | (rw [← Complex.ofReal_natCast]; exact Complex.zero_le_real.mpr (Nat.cast_nonneg _))
  have hsum : (0 : ℂ) ≤ Zeta23.paperFT k (Zeta23.gammaOf (ρ : ℂ)) := by
    rw [hterm]
    exact Finset.sum_nonneg fun i _ => Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
  exact mul_nonneg hm hsum

/-- h2 on the W3 sub-class gives h2 on K, by restriction. -/
theorem h2_sign_sum_imp_h2_sign : h2_sign_sum → h2_sign := fun H k hk => H k (classK_subset_classKsum hk)

/-- **THE W3 EQUIVALENCE: h2 on the W3 sub-class is RH**, both directions, no hypothesis. -/
theorem h2_sign_sum_iff_rh : h2_sign_sum ↔ RiemannHypothesis :=
  ⟨fun H => h2_sign_iff_rh.mp (h2_sign_sum_imp_h2_sign H), rh_imp_h2_sign_sum⟩

end B321
end SIDEExplicitFormula
