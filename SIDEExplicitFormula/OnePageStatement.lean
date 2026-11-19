/-
SIDE-explicit-formula -- SIDEExplicitFormula/OnePageStatement.lean
THIS PROGRAMME'S WORK (act b763, ruling (R373)(6), W-ORD-STATEMENT-FILE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE STATEMENT LAYER OF ONE PAGE. Canonical text: PLACE-papers day1/ONE_PAGE_PROOF_v2_0.md, its Correspondence table (:36-:57). Each row of
that table whose declaration stands in this kernel is stated here apart from its proof, as a declaration closed by the name that proves
it, so that a reader checks the page by reading this file and one print of axioms. The two rows that are definitions are stated as their
unfolding, closed by `Iff.rfl`. Nothing here is proved anew: each proof is the cited name.

THE DEFINITIONS THESE STATEMENTS REST ON, by file and line in this kernel:
  `B321.classK` H2Sign.lean :24 ; `B321.h2_sign` H2Sign.lean :29 ; `B321.zeroSide` B321Identity.lean :24 ; `B321.poleTerm` :29 ;
  `B321.primeSum` :33 ; `B321.archTerm` :37 ; `B321.b321Norm` :41 ; `B321.h2_sign_upto` DetectionRegion.lean :29 ;
  `GRHWeil.GRH_chi` GRHWeil.lean :53 ; `GRHWeil.h2_sign_chi` GRHWeil.lean :75 ; `Schema.WeilConfig` Schema/Config.lean :24 ;
  `Schema.h2_sign_cfg` Schema/Config.lean :41 ; `LiWeil.LiCoeff` LiWeil.lean :243 ; `LiWeil.symMember` LiWeilSym.lean :51 ;
  `Zeta23.EF.literatureRHS` Zeta23/ExplicitFormula.lean :86 ; `Schema.rQ` Schema/EpsteinZQ.lean :59 ; `Schema.zeroSideQ` :107 ;
  `Schema.primeTermQ` :112 ; `Schema.archTermQ` :121 ; `Schema.ZQ.cQ` Schema/ZQ/LogDeriv.lean :63 ; `Schema.ZQ.zqZeroConfig`
  Schema/ZQ/Zeros.lean :319 ; `Schema.Wide.liCoeff` Schema/Wide/Converse.lean :32 ; from Mathlib `RiemannHypothesis`, `riemannZeta`,
  `DirichletCharacter`, `ArithmeticFunction.IsMultiplicative`, `ArithmeticFunction.zeta` and `ArithmeticFunction.vonMangoldt`.

THE ROWS OF ANOTHER KERNEL. The table's last three rows stand in SIDE-kernel at its tag v1.5, `Bridge/TheBridgeComplete.lean`:
`MechanismClass` and `seven_classes` (:20, :25), `produces_offline` (:157), `none_produce` (:198). This kernel does not import SIDE-kernel,
so they are named here and not stated; each is checked at its tag there.
-/
import SIDEExplicitFormula.Seam
import SIDEExplicitFormula.Chi.CriterionConverse
import SIDEExplicitFormula.Schema.Converse
import SIDEExplicitFormula.LiCriterionBridge
import SIDEExplicitFormula.DetectionRegion
import SIDEExplicitFormula.KeiperSign
import SIDEExplicitFormula.Schema.ZetaBox.Box
import SIDEExplicitFormula.Schema.ZQ.EF.Main
import SIDEExplicitFormula.Schema.ZQ.OffZero.SP4
import SIDEExplicitFormula.Schema.Wide.HalfScaleControl
import SIDEExplicitFormula.Schema.ZQ.Mechanism.NoEuler
import SIDEExplicitFormula.Schema.ZQ.Mechanism.CoeffSign

open Topology
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace OnePage

/-! ### The criterion for zeta -/

/-- The class of test functions (H2Sign.lean :24), its definition unfolded. -/
theorem classK_def (k : ℝ → ℂ) :
    B321.classK k ↔ ((∀ x : ℝ, k (-x) = k x) ∧ ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
      ∃ h : ℝ → ℂ, ContDiff ℝ 2 h ∧ HasCompactSupport h ∧ k = Zeta23.EF.weilTest h h) :=
  Iff.rfl

/-- The clause (H2Sign.lean :29), its definition unfolded. -/
theorem h2_sign_def :
    B321.h2_sign ↔ ∀ k : ℝ → ℂ, B321.classK k → 0 ≤ B321.poleTerm k - B321.primeSum k + B321.archTerm k :=
  Iff.rfl

/-- The explicit formula for zeta (B321Identity.lean :44). -/
theorem b321_identity (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) (he : ∀ x : ℝ, k (-x) = k x) :
    B321.zeroSide k = B321.b321Norm * (B321.poleTerm k - B321.primeSum k + B321.archTerm k) :=
  B321.b321_identity k hk hs he

/-- The clause is equivalent to the Riemann Hypothesis (Seam.lean :101). -/
theorem h2_sign_iff_rh : B321.h2_sign ↔ RiemannHypothesis :=
  B321.h2_sign_iff_rh

/-- The same at a primitive character other than the trivial one (Chi/CriterionConverse.lean :270). -/
theorem h2_sign_chi_iff_grh_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) :
    GRHWeil.h2_sign_chi χ ↔ GRHWeil.GRH_chi χ :=
  GRHWeil.h2_sign_chi_iff_grh_chi χ hχ h1

/-- The same over a configuration (Schema/Converse.lean :265). -/
theorem h2_sign_cfg_iff_target (C : Schema.WeilConfig) : Schema.h2_sign_cfg C ↔ C.target :=
  Schema.h2_sign_cfg_iff_target C

/-- Li's criterion (LiCriterionBridge.lean :179). -/
theorem li_nonneg_iff_rh : (∀ n : ℕ, 0 ≤ LiWeil.LiCoeff n) ↔ RiemannHypothesis :=
  LiCriterionBridge.li_nonneg_iff_rh

/-- The Bombieri-Lagarias form (LiCriterionBridge.lean :191). -/
theorem arith_limit_nonneg_iff_rh :
    (∀ (n : ℕ) (L : ℂ), Filter.Tendsto (fun δ => Zeta23.EF.literatureRHS (LiWeil.symMember n δ)) (𝓝[>] 0) (𝓝 L) → 0 ≤ L.re) ↔
      RiemannHypothesis :=
  LiCriterionBridge.arith_limit_nonneg_iff_rh

/-- Bounded support (DetectionRegion.lean :47). -/
theorem h2_sign_iff_forall_upto : B321.h2_sign ↔ ∀ L₀ : ℝ, B321.h2_sign_upto L₀ :=
  B321.h2_sign_iff_forall_upto

/-! ### What holds without the clause -/

/-- λ₁ > 0 (KeiperSign.lean :82). -/
theorem liCoeff_one_pos : 0 < LiWeil.LiCoeff 1 :=
  KeiperSign.liCoeff_one_pos

/-- A zero of zeta on the line between heights 12 and 16 (Schema/ZetaBox/Box.lean :21). -/
theorem zeta_box : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ (12 : ℝ) < ρ.im ∧ ρ.im < 16 :=
  Schema.ZetaBox.zeta_box

/-! ### The control, the Epstein zeta function of x² + xy + 6y² -/

/-- The explicit formula for the control (Schema/ZQ/EF/Main.lean :198). -/
theorem zq_explicit_formula_instance (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    (he : ∀ x : ℝ, k (-x) = k x) :
    Schema.zeroSideQ Schema.ZQ.zqZeroConfig k =
      B321.poleTerm k - Schema.primeTermQ (fun n => Schema.ZQ.cQ n) k + Schema.archTermQ k :=
  Schema.ZQ.EF.zq_explicit_formula_instance k hk hs he

/-- A zero of the control off the line (Schema/ZQ/OffZero/SP4.lean :32). -/
theorem zq_offline_zero : ∃ ρ ∈ (Schema.ZQ.zqZeroConfig).carrier, ρ.re ≠ 1 / 2 :=
  Schema.ZQ.OffZero.zq_offline_zero

/-- The inequality fails for the control, on the arithmetic side of its explicit formula (Schema/Wide/HalfScaleControl.lean :44). -/
theorem zq_weil_positivity_fails :
    ¬ ∀ k : ℝ → ℂ, B321.classK k → 0 ≤ B321.poleTerm k - Schema.primeTermQ (fun n => Schema.ZQ.cQ n) k + Schema.archTermQ k :=
  Schema.ZQ.zq_weil_positivity_fails

/-- Li's nonnegativity fails for the control (Schema/ZQ/OffZero/SP4.lean :36). -/
theorem zq_li_nonneg_fails : ¬ (∀ n : ℕ, 0 ≤ Schema.Wide.liCoeff Schema.ZQ.zqZeroConfig n) :=
  Schema.ZQ.OffZero.zq_li_nonneg_fails

/-- The coefficients of the control are not multiplicative (Schema/ZQ/Mechanism/NoEuler.lean :99). -/
theorem zq_coeff_not_multiplicative :
    ¬ ArithmeticFunction.IsMultiplicative
      (⟨fun n => (Schema.rQ n : ℝ) / 2, by simp [Schema.rQ_zero]⟩ : ArithmeticFunction ℝ) :=
  Schema.ZQ.zq_coeff_not_multiplicative

/-- The coefficients of zeta are multiplicative (Schema/ZQ/Mechanism/NoEuler.lean :112). -/
theorem zeta_isMultiplicative_control : ArithmeticFunction.IsMultiplicative ArithmeticFunction.zeta :=
  Schema.ZQ.zeta_isMultiplicative_control

/-- The log-derivative coefficients of the control are not all nonnegative (Schema/ZQ/Mechanism/CoeffSign.lean :291). -/
theorem cQ_not_nonneg : ¬ (∀ n : ℕ, 0 ≤ Schema.ZQ.cQ n) :=
  Schema.ZQ.cQ_not_nonneg

/-- The von Mangoldt function is nonnegative (Schema/ZQ/Mechanism/CoeffSign.lean :301). -/
theorem vonMangoldt_nonneg_control (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n :=
  Schema.ZQ.vonMangoldt_nonneg_control n

end OnePage
end SIDEExplicitFormula
