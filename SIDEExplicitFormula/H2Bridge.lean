/-
SIDE-explicit-formula -- SIDEExplicitFormula/H2Bridge.lean
THIS PROGRAMME'S WORK (act b532, ruling (R142)(4); W-ORD-H2-BRIDGE) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE BRIDGE, IN ITS TRIVIAL DIRECTION. The deposit's Route 3 premise, `ConservationBridge.ConservationHypothesis`
(SIDE-kernel v1.5 = 0e5233f, Bridge/ConservationBridge.lean), is restated here word for word in Mathlib's objects
(`conservationHypothesis`): every real part `sigma` of a nontrivial zero of `riemannZeta` (not a trivial zero, not the
pole) admits a prime `p` with `p ^ (-sigma) = p ^ (-(1 - sigma))`. SIDE-kernel's `is_xi_zero` and `prime_as_real` are
unfolded; the two kernels cannot import each other (Lean v4.29.0-rc8 / Mathlib e960b84 against v4.33.0-rc2 / 51e6992),
so the identity of this restatement with the deposited one is a statement-read, not a kernel fact.

`balance_lemma` is SIDE-kernel's `techne_kernel_voice1.balance_theorem`, ported: for a prime `p`,
`p ^ (-sigma) = p ^ (-(1 - sigma)) ↔ sigma = 1 / 2`. So `ch_iff_rh`: THE PREMISE IS RH RESTATED. `ch_imp_h2_sign`
composes with b513's `rh_imp_h2_sign`: both objects called h2 live in this kernel with the implication between them.
The converse `h2_sign_imp_ch` is a Prop, NOT PROVED, and `h2_sign_imp_ch_iff` shows it is b513's `h2_sign_imp_rh` --
Weil's converse, W-ORD-WEIL-CONVERSE, open at f4. `conservationHypothesisConfig` is the premise over the kernel's zero
configuration; it follows from the verbatim form (`ch_imp_config`), and the reverse would need the classical fact that
every nontrivial zero lies in the open strip, which Zeta23 records as not in the kernel. Nothing here is a statement
about the zeros of zeta or about RH beyond these implications.
-/
import SIDEExplicitFormula.RHChain

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace B321

/-- **The deposit's Route 3 premise, restated word for word:** every real part `sigma` of a nontrivial zero of
`riemannZeta` admits a prime `p` with `p ^ (-sigma) = p ^ (-(1 - sigma))`. -/
def conservationHypothesis : Prop :=
  ∀ σ : ℝ, (∃ t : ℝ, riemannZeta (⟨σ, t⟩ : ℂ) = 0 ∧ ¬ (∃ n : ℕ, (⟨σ, t⟩ : ℂ) = -2 * ((n : ℂ) + 1)) ∧ (⟨σ, t⟩ : ℂ) ≠ 1) →
    ∃ p : ℕ, ∃ _ : Nat.Prime p, (p : ℝ) ^ (-σ) = (p : ℝ) ^ (-(1 - σ))

/-- The same premise over the kernel's zero configuration. -/
def conservationHypothesisConfig : Prop :=
  ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ∃ p : ℕ, ∃ _ : Nat.Prime p, (p : ℝ) ^ (-ρ.re) = (p : ℝ) ^ (-(1 - ρ.re))

/-- **The balance lemma** (SIDE-kernel's `balance_theorem`, ported): at a prime, the Euler balance holds iff
`sigma = 1 / 2`. -/
theorem balance_lemma (p : ℕ) (hp : Nat.Prime p) (σ : ℝ) :
    (p : ℝ) ^ (-σ) = (p : ℝ) ^ (-(1 - σ)) ↔ σ = 1 / 2 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  constructor
  · intro h
    rcases lt_trichotomy (-σ) (-(1 - σ)) with hlt | heq | hgt
    · exact absurd h (ne_of_lt ((Real.rpow_lt_rpow_left_iff h1).mpr hlt))
    · linarith
    · exact absurd h (ne_of_gt ((Real.rpow_lt_rpow_left_iff h1).mpr hgt))
  · intro h
    rw [h]
    first
    | norm_num
    | (congr 1; ring)

/-- **The premise gives RH.** -/
theorem ch_imp_rh : conservationHypothesis → RiemannHypothesis := by
  intro h s hs hnt hne
  obtain ⟨p, hp, hbal⟩ := h s.re ⟨s.im, by rwa [Complex.eta], by rwa [Complex.eta], by rwa [Complex.eta]⟩
  exact (balance_lemma p hp s.re).mp hbal

/-- **RH gives the premise back**, at the prime 2. -/
theorem rh_imp_ch : RiemannHypothesis → conservationHypothesis := by
  intro hRH σ ⟨t, hz, hnt, hne⟩
  have hσ : σ = 1 / 2 := hRH ⟨σ, t⟩ hz hnt hne
  exact ⟨2, Nat.prime_two, (balance_lemma 2 Nat.prime_two σ).mpr hσ⟩

/-- **THE PREMISE IS RH RESTATED.** -/
theorem ch_iff_rh : conservationHypothesis ↔ RiemannHypothesis := ⟨ch_imp_rh, rh_imp_ch⟩

/-- The verbatim premise gives the premise over the kernel's zero configuration. -/
theorem ch_imp_config : conservationHypothesis → conservationHypothesisConfig := by
  intro h ρ hρ
  have hρ' : Zeta23.IsNontrivialZero ρ := by
    rw [Zeta23.zetaZeroConfig_carrier] at hρ
    exact hρ
  have hnt := Zeta23.IsNontrivialZero.not_trivial hρ'
  exact h ρ.re ⟨ρ.im, by rw [Complex.eta]; exact hρ'.1, by rw [Complex.eta]; exact hnt.1,
    by rw [Complex.eta]; exact hnt.2⟩

/-- **THE BRIDGE, compiled:** the deposit's Route 3 premise implies `h2_sign`, through RH. -/
theorem ch_imp_h2_sign : conservationHypothesis → h2_sign := fun h => rh_imp_h2_sign (ch_imp_rh h)

/-- **The converse, a Prop, NOT PROVED:** `h2_sign` implies the Route 3 premise. By `h2_sign_imp_ch_iff` it is
b513's `h2_sign_imp_rh` -- Weil's converse, W-ORD-WEIL-CONVERSE, compiled to f3 and open at f4. -/
def h2_sign_imp_ch : Prop := h2_sign → conservationHypothesis

/-- The converse is exactly f4's target. -/
theorem h2_sign_imp_ch_iff : h2_sign_imp_ch ↔ h2_sign_imp_rh := by
  unfold h2_sign_imp_ch h2_sign_imp_rh
  exact ⟨fun h hs => ch_imp_rh (h hs), fun h hs => rh_imp_ch (h hs)⟩

end B321
end SIDEExplicitFormula
