/-
SIDE-explicit-formula -- SIDEExplicitFormula/RegisterDepth.lean
THIS PROGRAMME'S WORK (act b538, ruling (R148)) -- NOT VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full:
`theorem`, never `lemma`.

W-ORD-REGISTER-DEPTH. The registers R1, R3, R5 of §27.3 and SIDE-lv-conservation's own h2, each read from its
compiled face and graded by what its Lean sentence says, relative to RH. The federation rule bars a Lake dependency
on SIDE-lv-conservation or SIDE-kernel, so every face is restated VERBATIM here, with its source path, line and pin
in its docstring (lv at tag v0.10.0 = 93c27ec, identical at HEAD 2f71068 for every file cited; SIDE-kernel at
v1.5 = 0e5233f). Where lv restates the kernel, the kernel's v1.5 text is used (relay data/b538_restatement_compare.txt).
Nothing here edits a deposited kernel; nothing here proves RH or h2_sign.
-/
import SIDEExplicitFormula.Seam
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.DiscreteSubset

open Complex HurwitzZeta MeasureTheory Set Filter Topology

noncomputable section

namespace SIDEExplicitFormula
namespace RegisterDepth

/-! ## R1 -- the universality hypothesis. SIDE-kernel v1.5 = 0e5233f, `Kernel/SilenceTheorem.lean`. -/

/-- `ConfigurationSpace` -- verbatim, `Kernel/SilenceTheorem.lean:26-28` (SIDE-kernel v1.5 = 0e5233f). -/
structure ConfigurationSpace where
  α : Type
  nonempty : Nonempty α

/-- `Interface` -- verbatim, `Kernel/SilenceTheorem.lean:33-37` (SIDE-kernel v1.5 = 0e5233f), field docstrings
dropped. -/
structure Interface (C : ConfigurationSpace) (R : Type) where
  action : C.α → R
  essential : Prop

/-- `Interface.is_universal` -- verbatim, `Kernel/SilenceTheorem.lean:42-44` (SIDE-kernel v1.5 = 0e5233f). -/
def Interface.is_universal {C : ConfigurationSpace} {R : Type}
    (I : Interface C R) : Prop :=
  ∀ c₁ c₂ : C.α, I.action c₁ = I.action c₂

/-- `factors_through` -- verbatim, `Kernel/SilenceTheorem.lean:49-51` (SIDE-kernel v1.5 = 0e5233f). -/
def factors_through {C : ConfigurationSpace} {R V : Type}
    (M : C.α → V) (I : Interface C R) : Prop :=
  ∃ f : R → V, ∀ c : C.α, M c = f (I.action c)

/-- `Interface.kappa_zero` -- verbatim, `Kernel/SilenceTheorem.lean:58-61` (SIDE-kernel v1.5 = 0e5233f). -/
def Interface.kappa_zero {C : ConfigurationSpace} {R : Type}
    (I : Interface C R) : Prop :=
  ∀ V : Type, ∀ M : C.α → V, factors_through M I →
    ∀ c₁ c₂ : C.α, M c₁ = M c₂

/-- **R1 face** -- verbatim, lv `SIDELvConservation/RegisterPentagon.lean:106-107` (v0.10.0). -/
def Register1_universalityHypothesis : Prop :=
  ∀ (C : ConfigurationSpace) (R : Type) (I : Interface C R), I.essential → I.is_universal

/-- **R1 is FALSE AS STATED.** The interface on `Bool` with the identity action and `essential := True` is essential
and not universal: `essential` is an uninterpreted `Prop` field, so the register quantifies over interfaces it cannot
distinguish ((R148)(3)(a)). -/
theorem not_register1 : ¬ Register1_universalityHypothesis := by
  intro h
  have h2 : (true : Bool) = false :=
    h ⟨Bool, ⟨true⟩⟩ Bool ⟨id, True⟩ trivial true false
  exact Bool.noConfusion h2

/-- The kernel's `silence_universal` (`Kernel/SilenceTheorem.lean:74-84`, SIDE-kernel v1.5), restated with its own
proof: it takes universality PER INTERFACE, so `not_register1` does not touch it. -/
theorem silence_universal_restated
    {C : ConfigurationSpace} {R : Type}
    (I : Interface C R)
    (h_univ : I.is_universal) :
    I.kappa_zero := by
  intro V M h_factors c₁ c₂
  obtain ⟨f, hf⟩ := h_factors
  rw [hf c₁, hf c₂]
  rw [h_univ c₁ c₂]

/-! ## lv's h2. `SIDELvConservation/T1_MellinFactorization.lean:26` (v0.10.0). -/

/-- `Phi` -- verbatim, lv `SIDELvConservation/T1_MellinFactorization.lean:26` (v0.10.0). -/
def Phi : ℝ → ℂ := fun t => ((evenKernel 0 t : ℂ) - 1) / 2

/-- The `n = 0` term of the even theta kernel: `1 ≤ evenKernel 0 x` for `x > 0` (`hasSum_int_evenKernel`). -/
theorem one_le_evenKernel_zero {x : ℝ} (hx : 0 < x) : 1 ≤ evenKernel 0 x := by
  have h := hasSum_int_evenKernel (0 : ℝ) hx
  rw [show ((0 : ℝ) : UnitAddCircle) = 0 from rfl] at h
  have h1 := le_hasSum h 0 (fun j _ => (Real.exp_pos _).le)
  simpa using h1

/-- The lower bound near 0 from the functional equation: `t ^ (-1/2) ≤ evenKernel 0 t` for `t > 0`. -/
theorem rpow_le_evenKernel_zero {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2 : ℝ)) ≤ evenKernel 0 t := by
  have hfe := evenKernel_functional_equation 0 t
  rw [← evenKernel_eq_cosKernel_of_zero] at hfe
  have h1 := one_le_evenKernel_zero (one_div_pos.mpr ht)
  rw [hfe, Real.rpow_neg ht.le, ← one_div]
  calc 1 / t ^ (1 / 2 : ℝ) = 1 / t ^ (1 / 2 : ℝ) * 1 := by ring
    _ ≤ 1 / t ^ (1 / 2 : ℝ) * evenKernel 0 (1 / t) := by gcongr

/-- **lv's h2 is FALSE for `re s ≤ 1`.** Mathlib's `mellin` is a Bochner integral, zero where the integrand is not
integrable; near 0, `‖t ^ (s/2 - 1) • Phi t‖ ≥ t ^ (-1) / 4`, and `t ^ (-1)` is not integrable on `(0, 1/4)`. -/
theorem mellin_Phi_eq_zero_of_re_le_one : ∀ s : ℂ, s.re ≤ 1 → mellin Phi (s / 2) = 0 := by
  intro s hs
  unfold mellin
  apply MeasureTheory.integral_undef
  intro hint
  have hsub : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • Phi t) (Ioo 0 (1 / 4)) :=
    IntegrableOn.mono_set hint Ioo_subset_Ioi_self
  have hg : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 (1 / 4)) := by
    refine Integrable.mono' (hsub.norm.const_mul 4) ((measurable_id.pow_const _).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have htle : t ≤ 1 := by linarith
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
    have hE : a ≤ evenKernel 0 t := ha ▸ rpow_le_evenKernel_zero ht0
    have ha2 : 2 ≤ a := by
      have h4 : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht0 ht1.le (by norm_num)
      have h4' : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have hpow : a ≤ t ^ ((s / 2 - 1).re) := by
      have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp
      rw [hre, ha]
      exact Real.rpow_le_rpow_of_exponent_ge ht0 htle (by linarith)
    have hPhi : (evenKernel 0 t - 1) / 2 ≤ ‖Phi t‖ := by
      have e : Phi t = (((evenKernel 0 t - 1) / 2 : ℝ) : ℂ) := by
        simp only [Phi]; push_cast; try ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    have hsq : t ^ (-1 : ℝ) = a * a := by
      rw [ha, ← Real.rpow_add ht0]; norm_num
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), hsq]
    have hN : a / 4 ≤ ‖Phi t‖ := by linarith
    have ha0 : 0 ≤ a := by linarith
    calc a * a = 4 * (a * (a / 4)) := by ring
      _ ≤ 4 * (t ^ ((s / 2 - 1).re) * ‖Phi t‖) := by gcongr
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1 / 4)).mp hg
  norm_num at this

/-- **lv's h2 on the critical strip** -- the hypothesis `mellin Phi (s / 2) ≠ 0` of lv's
`goalState_sevenClasses_of_h2` (`RegisterPentagon.lean:215`, v0.10.0) is false at every `s` with `0 < re s < 1`. -/
theorem lv_h2_false_on_strip : ∀ s : ℂ, 0 < s.re → s.re < 1 → ¬ (mellin Phi (s / 2) ≠ 0) := by
  intro s _ h1 h
  exact h (mellin_Phi_eq_zero_of_re_le_one s h1.le)

/-- **The corrected face.** With `completedRiemannZeta` in place of the Mellin factor, the strip statement is exactly
`rh_strip` (RH on the kernel's zero configuration). -/
theorem lvh2_corrected_iff :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 → completedRiemannZeta s ≠ 0) ↔ B321.rh_strip := by
  constructor
  · intro h ρ hρ
    rw [Zeta23.zetaZeroConfig_carrier] at hρ
    have hρ' : Zeta23.IsNontrivialZero ρ := hρ
    unfold Zeta23.IsNontrivialZero at hρ'
    obtain ⟨hz, h0, h1⟩ := hρ'
    by_contra hne
    apply h ρ h0 h1 hne
    have hρ0 : ρ ≠ 0 := by
      intro e; rw [e] at h0; simp at h0
    rw [riemannZeta_def_of_ne_zero hρ0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  · intro h s h0 h1 hne hΛ
    apply hne
    apply h s
    rw [Zeta23.zetaZeroConfig_carrier]
    show Zeta23.IsNontrivialZero s
    unfold Zeta23.IsNontrivialZero
    have hs0 : s ≠ 0 := by
      intro e; rw [e] at h0; simp at h0
    refine ⟨?_, h0, h1⟩
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]

/-! ## R3 -- totality through places. lv `T3_StepNineBridge.lean`, `CouplingsAtPhi.lean`, `RegisterPentagon.lean`
(v0.10.0). -/

namespace T3

/-- `Coupling` -- verbatim, lv `SIDELvConservation/T3_StepNineBridge.lean:44` (v0.10.0). -/
abbrev Coupling := (ℝ → ℂ) → Prop

/-- `PerClassExcludes` -- verbatim, lv `SIDELvConservation/T3_StepNineBridge.lean:52-53` (v0.10.0). -/
def PerClassExcludes (C : Coupling) (s : ℂ) : Prop :=
  ∃ Φ : ℝ → ℂ, C Φ ∧ mellin Φ (s / 2) ≠ 0

/-- `CombinationsExclude` -- verbatim, lv `SIDELvConservation/T3_StepNineBridge.lean:57-58` (v0.10.0). -/
def CombinationsExclude (𝒞 : Set Coupling) (s : ℂ) : Prop :=
  ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0

end T3

open T3

/-- `C1_realness` -- verbatim, lv `SIDELvConservation/CouplingsAtPhi.lean:67` (v0.10.0). -/
def C1_realness : Coupling := fun (Φ : ℝ → ℂ) => ∀ t : ℝ, (Φ t).im = 0

/-- `C2_halfplane_nonvanishing` -- verbatim, lv `CouplingsAtPhi.lean:72-73` (v0.10.0). -/
def C2_halfplane_nonvanishing : Coupling := fun (Φ : ℝ → ℂ) =>
  ∀ s : ℂ, 1 < s.re → mellin Φ (s / 2) ≠ 0

/-- `C3_theta_transformation` -- verbatim, lv `CouplingsAtPhi.lean:79-80` (v0.10.0). -/
def C3_theta_transformation : Coupling := fun (Φ : ℝ → ℂ) =>
  ∀ t : ℝ, 0 < t → Φ (1 / t) = Real.sqrt t * Φ t + (Real.sqrt t - 1) / 2

/-- `C4_modularity` -- verbatim, lv `CouplingsAtPhi.lean:108-113` (v0.10.0). -/
def C4_modularity : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ F : ℂ → ℂ,
    (∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ F τ) ∧
    (∀ t : ℝ, 0 < t → F (Complex.I * t) = 2 * Φ t + 1) ∧
    (∀ τ : ℂ, F (2 + τ) = F τ) ∧
    (∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)

/-- `C5_input` -- verbatim, lv `CouplingsAtPhi.lean:120-122` (v0.10.0). -/
def C5_input : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ μ : ℤ → ℝ, (∀ n : ℤ, 0 ≤ μ n) ∧
    ∀ t : ℝ, 0 < t → HasSum (fun n : ℤ => ((Real.exp (-Real.pi * μ n * t) : ℝ) : ℂ)) (2 * Φ t + 1)

/-- `C6_holomorphic_extension` -- verbatim, lv `CouplingsAtPhi.lean:144-146` (v0.10.0). -/
def C6_holomorphic_extension : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ F : ℂ → ℂ, (∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F z) ∧
    ∀ t : ℝ, 0 < t → F (t : ℂ) = Φ t

/-- `C7_order` -- verbatim, lv `CouplingsAtPhi.lean:182-185` (v0.10.0). -/
def C7_order : Coupling := fun (Φ : ℝ → ℂ) =>
  ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
    (∀ s : ℂ, 1 < s.re → G s = mellin Φ (s / 2) + 1 / s + 1 / (1 - s)) ∧
    ∃ A C : ℝ, ∀ s : ℂ, ‖G s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2)))

/-- `sevenClasses` -- verbatim, lv `CouplingsAtPhi.lean:188-190` (v0.10.0). -/
def sevenClasses : Set Coupling :=
  {C1_realness, C2_halfplane_nonvanishing, C3_theta_transformation, C4_modularity,
   C5_input, C6_holomorphic_extension, C7_order}

/-- **R3 face** -- verbatim, lv `SIDELvConservation/RegisterPentagon.lean:139-140` (v0.10.0). -/
def Register3_totalityThroughPlaces (s : ℂ) : Prop :=
  (∀ C ∈ sevenClasses, T3.PerClassExcludes C s) → T3.CombinationsExclude sevenClasses s

/-- **R3 on the convergence half-plane, on lv's h1.** For `1 < re s`, `Phi` itself witnesses the conclusion, given
`h1 : ∀ C ∈ sevenClasses, C Phi` -- compiled in lv as `h1_complete_at_Phi` (v0.10.0), carried here as a named premise
under the federation rule. -/
theorem register3_of_one_lt_re (h1 : ∀ C ∈ sevenClasses, C Phi) :
    ∀ s : ℂ, 1 < s.re → Register3_totalityThroughPlaces s := by
  intro s hs _
  refine ⟨Phi, h1, ?_⟩
  exact h1 C2_halfplane_nonvanishing (by simp [sevenClasses]) s hs

/-! ## R5 -- the Hilbert–Pólya output schema. -/

/-- `is_xi_zero` -- verbatim, `Kernel/XiDef.lean:34-38` (SIDE-kernel v1.5 = 0e5233f). -/
def is_xi_zero (sigma : Real) : Prop :=
  Exists (fun t : Real =>
    riemannZeta (⟨sigma, t⟩ : ℂ) = 0 /\
    (Not (Exists (fun n : Nat => (⟨sigma, t⟩ : ℂ) = -2 * (↑n + 1)))) /\
    (⟨sigma, t⟩ : ℂ) ≠ 1)

/-- **R5 output face** -- verbatim, lv `SIDELvConservation/RegisterPentagon.lean:189-195` (v0.10.0). -/
def Register5_output_HilbertPolya : Prop :=
  ∃ (spectrum : ℕ → ℝ) (pairing : ℕ → ℕ → ℝ) (T : ℕ → ℕ → ℝ),
    (∀ i j, pairing i j = pairing j i) ∧
    (∀ i, 0 < pairing i i) ∧
    (∀ i j, pairing i i * T i j = pairing j j * T j i) ∧
    (∀ n, T n n = spectrum n) ∧
    (∀ σ : ℝ, is_xi_zero σ → ∃ n : ℕ, spectrum n = σ)

/-- The zeros of zeta off the pole form a countable set: each is isolated (zeta is analytic on `{1}ᶜ`, connected, and
not identically zero there since `ζ 2 ≠ 0`), and a discrete subset of `ℂ` is countable. -/
theorem zeta_zeros_countable : {z : ℂ | z ≠ 1 ∧ riemannZeta z = 0}.Countable := by
  set Z : Set ℂ := {z : ℂ | z ≠ 1 ∧ riemannZeta z = 0} with hZ
  have hA : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two)
      (1 : ℂ)).isPreconnected
  have hdisc : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    rw [Filter.inf_principal_eq_bot]
    rcases (hA x hx.1).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have heq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hx.1 h
      have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by norm_num
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : (1 : ℝ) < (2 : ℂ).re) (heq h2)
    · filter_upwards [h] with w hw hwZ
      exact hw hwZ.2
  exact Set.countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- The real parts of the nontrivial zeros are countable. -/
theorem xi_zero_re_countable : {σ : ℝ | is_xi_zero σ}.Countable := by
  refine (zeta_zeros_countable.image Complex.re).mono ?_
  rintro σ ⟨t, hz, _, h1⟩
  exact ⟨⟨σ, t⟩, ⟨h1, hz⟩, rfl⟩

/-- **R5-output is TRUE AS STATED.** The constant pairing `1`, the diagonal operator and an enumeration of the
countably many real parts witness the schema: it carries no RH content, a SHELL; what it is missing is the ordinates,
and a self-adjoint operator on a Hilbert space whose spectrum they are. -/
theorem register5_output_holds : Register5_output_HilbertPolya := by
  obtain ⟨f, hf⟩ := (xi_zero_re_countable.union (Set.countable_singleton (0 : ℝ))).exists_eq_range
    ⟨0, Or.inr rfl⟩
  refine ⟨f, fun _ _ => 1, fun i j => if i = j then f i else 0, fun _ _ => rfl, fun _ => one_pos, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  · intro n; simp
  · intro σ hσ
    have : σ ∈ Set.range f := hf ▸ Or.inl hσ
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn⟩

end RegisterDepth
end SIDEExplicitFormula
