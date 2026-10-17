/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/Config.lean
THIS PROGRAMME'S WORK (act b679, ruling (R289)(4)-(6); the plan relay data/b679_strip_plan.txt == 1, == 3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE WIDENED CONFIGURATION CLASS. `WideConfig` carries `Zeta23.ZeroConfig`'s fields with one field widened: its points lie in the
OPEN strip `-1/2 < Re ρ < 3/2` (ZeroConfig's field is the closed strip `0 ≤ Re ρ ≤ 1`, Zeta23/Defs.lean :142, so a configuration
with a point off `[0, 1]` is no ZeroConfig). Beside it the named hypothesis `Wide.HExcl`: every real point of the carrier has
positive real part -- inside the strip, no point is a real number in `(-1/2, 0]`. Its half at `0` gives `ρ ≠ 0` where the v0.32
proofs took it from `0 < Re ρ`; its half on `(-1/2, 0)` excludes the point `1 / (1 - R)` at which the composition's direction
`w = (1 - x⁻¹) / R` would be `1` (Schema/LiConverseCfg.lean :231). The local count `Wide.HCount` is RestBound.lean :44's statement
over the widened class, and `Wide.zero_sum_inv_sq` is `WeilEF.zero_sum_inv_sq_gen`'s proof over it (that proof reads no strip).
Every v0.32 declaration stands as it is; nothing here replaces one. Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.LiWeil
import Zeta23.WeilEF.ZeroSummability

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open Zeta23

/-- **The widened configuration:** ZeroConfig's fields, the strip field the open strip `(-1/2, 3/2)`. -/
structure WideConfig where
  /-- the set of distinct points -/
  carrier : Set ℂ
  /-- multiplicity (value irrelevant off carrier) -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, -1 / 2 < ρ.re ∧ ρ.re < 3 / 2
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  /-- local finiteness in the ordinate -/
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace Wide

/-- `{ρ ∈ Z : T₁ < Im ρ ≤ T₂}`, ZeroConfig.window's definition over the widened class. -/
def window (Z : WideConfig) (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N(T₁, T₂)`, counted with multiplicity, ZeroConfig.N's definition over the widened class. -/
def N (Z : WideConfig) (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ window Z T₁ T₂, Z.mult ρ

/-- **H-COUNT over the widened class:** `N(t, t + 1) ≤ A₀ log(|t| + 3)` with `A₀ ≥ 1` (RestBound.lean :44's statement). -/
def HCount (Z : WideConfig) (A₀ : ℝ) : Prop :=
  1 ≤ A₀ ∧ ∀ t : ℝ, (N Z t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/-- **The exclusion:** every real point of the carrier has positive real part; inside the strip, no point is a real number in
`(-1/2, 0]` (by `reflect_mem`, equivalently none in `[1, 3/2)`). -/
def HExcl (Z : WideConfig) : Prop := ∀ ρ ∈ Z.carrier, ρ.im = 0 → 0 < ρ.re

/-- The exclusion's half at `0`: no point of the carrier is `0`. -/
theorem ne_zero_of_excl {Z : WideConfig} (hx : HExcl Z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) : ρ ≠ 0 := by
  intro e
  have h := hx ρ hρ (by rw [e, Complex.zero_im])
  rw [e, Complex.zero_re] at h
  exact lt_irrefl _ h

/-- From the two-sided local count to the finite-sub-family form `Tail.LocalCount` (Zeta23/Tail.lean :135's proof). -/
theorem localCount_ofWindowCount (Z : WideConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (N Z t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Tail.LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ where
  one_le := hA₀
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Wide.window Z t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h

/-- **`Σ_ρ m_ρ / (1 + |γ_ρ|²)` converges** over the widened class under the local count (WeilEF.zero_sum_inv_sq_gen's proof,
Zeta23/WeilEF/ZeroSummability.lean :121; it reads no strip). -/
theorem zero_sum_inv_sq (Z : WideConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (N Z t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  classical
  have hLC := localCount_ofWindowCount Z hA₀ hloc'
  have hW := WeilEF.summable_weight
  refine summable_of_sum_le (c := 4 * A₀ * WeilEF.totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])) fun s => ?_
  set κ : Z.carrier → ℤ := fun ρ => WeilEF.key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨WeilEF.key_lt _, WeilEF.le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact WeilEF.key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact WeilEF.le_key_add_one _
      have hge := WeilEF.one_add_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, WeilEF.gammaOf_re]; nlinarith [sq_nonneg ((gammaOf (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          = (Z.mult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
        _ ≤ (Z.mult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
    calc ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
      ≤ ∑ n ∈ s.image κ, 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * WeilEF.totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)

end Wide

end Schema
end SIDEExplicitFormula
