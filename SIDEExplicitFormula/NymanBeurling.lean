/-
SIDE-explicit-formula -- SIDEExplicitFormula/NymanBeurling.lean
THIS PROGRAMME'S WORK (act b629, ruling (R239)(4); W-ORD-NYMAN-BEURLING-FACE, its opening act) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE NYMAN–BEURLING FACE. `unitMeasure` -- Lebesgue measure restricted to the open unit interval (0, 1), finite.
`rhoFun θ x = {θ/x} − θ·{1/x}` -- the dilation family, `{·}` Mathlib's `Int.fract`, defined for every real θ and x. Its two
obligations, measurability (`rhoFun_measurable`) and square-integrability on the unit interval (`rhoFun_memLp`, from the bound
|rhoFun θ x| ≤ 1 + |θ|), are theorems of this module for every θ, discharged from Mathlib. `rho θ` -- its class in L²(0, 1);
`constOne` -- the class of the constant 1. `NB` -- the constant 1 lies in the closure of the span of the `rho θ`, 0 < θ ≤ 1.
`BD` -- the same with θ = 1/n, n ≥ 1 (written 1/(n + 1), n : ℕ).
`NymanBeurlingPremise` -- the classical equivalence `NB ↔ RiemannHypothesis` (Mathlib's statement) as a NAMED PREMISE (T1-lit), the
works as the registry records read at b629 give them (relay data/b629_citation.txt): Arne Beurling, "A closure problem related to
the Riemann zeta-function", Proceedings of the National Academy of Sciences 41 (5), 312-314 (1955), DOI 10.1073/pnas.41.5.312
(Crossref); Luis Báez-Duarte, "A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis", arXiv math/0202141,
posted 2002-02-15, the record carrying no journal reference; Bertil Nyman's thesis (Uppsala, 1950) is carried by none of the three
records the registry search returned, and is named here on the ferry's recollection alone. `rh_iff_nb` -- the face, INTERFACES on
that structure alone: the equivalence enters this kernel as a premise, not as a theorem of it.
`distN N` -- the distance in L²(0, 1) from the constant 1 to the span of the first N Báez-Duarte dilations, a real (its square the
ruling's d_N²); `distN_antitone` -- d_N is monotone non-increasing in N, from the spans' inclusion alone.
NOTHING HERE PROVES RH, NB OR BD, OR ANY PART OF THE CLASSICAL EQUIVALENCE THE PREMISE NAMES.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

open MeasureTheory Set

namespace SIDEExplicitFormula
namespace NymanBeurling

/-- **The measure:** Lebesgue measure restricted to the open unit interval, finite (`Real.isFiniteMeasure_restrict_Ioo`). -/
abbrev unitMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- **The dilation family:** `rhoFun θ x = {θ/x} − θ·{1/x}`, the fractional part Mathlib's `Int.fract`. -/
def rhoFun (θ x : ℝ) : ℝ := Int.fract (θ / x) - θ * Int.fract (1 / x)

/-- **The first obligation, discharged:** each member of the family is measurable (`measurable_fract`). -/
theorem rhoFun_measurable (θ : ℝ) : Measurable (rhoFun θ) := by
  unfold rhoFun
  exact (measurable_fract.comp (by fun_prop)).sub (measurable_const.mul (measurable_fract.comp (by fun_prop)))

/-- **The bound:** `|rhoFun θ x| ≤ 1 + |θ|` everywhere, from `0 ≤ {·} < 1`. -/
theorem rhoFun_bound (θ x : ℝ) : |rhoFun θ x| ≤ 1 + |θ| := by
  unfold rhoFun
  have h1 := Int.fract_nonneg (θ / x)
  have h2 := Int.fract_lt_one (θ / x)
  have h3 := Int.fract_nonneg (1 / x)
  have h4 := Int.fract_lt_one (1 / x)
  have hθ : |θ * Int.fract (1 / x)| ≤ |θ| := by
    rw [abs_mul, abs_of_nonneg h3]
    exact mul_le_of_le_one_right (abs_nonneg θ) h4.le
  have hθ' := abs_le.mp hθ
  exact abs_le.mpr ⟨by linarith [hθ'.1, hθ'.2], by linarith [hθ'.1, hθ'.2]⟩

/-- **The second obligation, discharged:** each member of the family is square-integrable on the unit interval
(`MemLp.of_bound`, the measure finite). -/
theorem rhoFun_memLp (θ : ℝ) : MemLp (rhoFun θ) 2 unitMeasure :=
  MemLp.of_bound (rhoFun_measurable θ).aestronglyMeasurable (1 + |θ|)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact rhoFun_bound θ x)

/-- **The family in L²(0, 1).** -/
def rho (θ : ℝ) : Lp ℝ 2 unitMeasure := MemLp.toLp (rhoFun θ) (rhoFun_memLp θ)

/-- **The constant 1 in L²(0, 1).** -/
def constOne : Lp ℝ 2 unitMeasure := MemLp.toLp (fun _ => (1 : ℝ)) (memLp_const 1)

/-- **The Nyman–Beurling statement:** the constant 1 lies in the closure of the span of the `rho θ`, `0 < θ ≤ 1`. -/
def NB : Prop :=
  constOne ∈ (Submodule.span ℝ (rho '' Ioc (0 : ℝ) 1)).topologicalClosure

/-- **The Báez-Duarte form:** the same with `θ = 1/n`, `n ≥ 1` (written `1/(n + 1)`, `n : ℕ`). -/
def BD : Prop :=
  constOne ∈ (Submodule.span ℝ (range fun n : ℕ => rho (1 / ((n : ℝ) + 1)))).topologicalClosure

/-- **THE NAMED PREMISE (T1-lit):** the classical equivalence of the Nyman–Beurling statement with Mathlib's `RiemannHypothesis`
-- Beurling, PNAS 41 (5), 312-314 (1955), DOI 10.1073/pnas.41.5.312; after Nyman's thesis (1950), carried by no record read; the
form `BD` after Báez-Duarte, arXiv math/0202141 (relay data/b629_citation.txt). A premise of this kernel, not a theorem of it. -/
structure NymanBeurlingPremise : Prop where
  equiv : NB ↔ RiemannHypothesis

/-- **THE FACE, AT INTERFACES ON THE PREMISE ALONE:** under the named premise, `RiemannHypothesis` holds exactly when `NB` does.
Its weight is the premise's and nothing else. -/
theorem rh_iff_nb (hP : NymanBeurlingPremise) : RiemannHypothesis ↔ NB :=
  hP.equiv.symm

/-- **The finite distances:** `distN N` is the distance in L²(0, 1) from the constant 1 to the span of the first `N` Báez-Duarte
dilations `rho (1/(n + 1))`, `n < N`; its square is the ruling's `d_N²`. -/
def distN (N : ℕ) : ℝ :=
  Metric.infDist constOne
    ((Submodule.span ℝ (range fun n : Fin N => rho (1 / (((n : ℕ) : ℝ) + 1))) : Submodule ℝ (Lp ℝ 2 unitMeasure)) :
      Set (Lp ℝ 2 unitMeasure))

/-- **d_N is monotone non-increasing:** the first `M` dilations are among the first `N` when `M ≤ N`, so the span grows and the
distance to it does not. -/
theorem distN_antitone : Antitone distN := by
  intro M N hMN
  unfold distN
  apply Metric.infDist_le_infDist_of_subset
  · refine SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_)
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n.1, lt_of_lt_of_le n.2 hMN⟩, rfl⟩
  · exact ⟨0, Submodule.zero_mem _⟩

end NymanBeurling
end SIDEExplicitFormula
