/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/EpsteinZQ.lean
THIS PROGRAMME'S WORK (act b703, ruling (R313)(4) and the author's words at its two prompts; the Epstein count's opening step M1 of relay
data/b701_epstein_plan.txt) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

Z_Q AS A LEAN OBJECT, ITS FACTS NAMED AS PREMISES. `Z_Q` is the Epstein zeta function of the form `Q0 = x² + xy + 6y²`,
discriminant `−23`, class number 3. DEFINED HERE: the form `Q0form`, its coefficients `rQ` (the representation count over the box
`|m| ≤ 2k, |n| ≤ k`, b326's normalisation `r_Q(1) = 2`), `ZQ` its lattice sum as Mathlib's `LSeries` (Z_Q itself where the series
converges), the gamma factor's base `qBase = 2π/√23`, and the three terms of its explicit formula -- the zero sum `zeroSideQ`, the
prime-power side `primeTermQ` (the coefficients `c` of −Z_Q′/Z_Q, a(1) = 2 so c(1) = 0), the archimedean term `archTermQ` with Z_Q's
bracket `2 Re ψ(1/2 + ir) − 2 log(2π/√23)` (relay tools/b326_windows.py :220-:228) -- beside b321's pole term `poleTerm`.
NAMED PREMISES, EACH STATED AND NOT PROVED: `ZQContinuation` (the continuation off s = 1, the functional equation of
Λ_Q(s) = (2π/√23)^{−s} Γ(s) Z_Q(s) on the critical strip, reality on the real line, the lattice sum's convergence on Re s > 1);
`ZQZeros` (a configuration of the widened class `WideConfig` whose carrier is the set of zeros of Λ_Q off its poles 0, 1 and its
trivial zeros −1, −2, ..., anywhere in ℂ, its multiplicities each zero's order); the logarithmic derivative's series; the explicit
formula `ZQExplicitFormula`; and the local count `Wide.HCount Z A0Q` on the same configuration, so the count and the sum range over one
set of zeros. THE CARRIER IS STRIP-FREE (the author's word at b703): an Epstein zeta of class number above 1 has infinitely many zeros with
Re s > 1 (Davenport-Heilbronn, cited at PLACE-papers OPEN_TRAILS-archive-2 :2089), so a closed-strip `Zeta23.ZeroConfig` cannot carry its
zeros; `WideConfig` (Schema/Wide/Config.lean :28-:38, the open strip (−1/2, 3/2)) can, Z_Q having no zero on Re s ≥ 3/2
(|Z_Q(s) − 2| ≤ Z_Q(3/2) − 2 < 2, relay data/b685_count_plan.txt :26-:27) and none on Re s ≤ −1/2 by the reflection.
A RESIDUE, NOT STATED: b590's `EpsteinPremises` (Schema/Epstein.lean :41-:44) sums its explicit formula over a closed-strip
configuration, which Davenport-Heilbronn makes false for Z_Q; no link to it is written here.
COMPILED: integer facts of the form; `rQ 0 = 0`; and the premises' consequences -- no point of the carrier is 0, the count and the
explicit formula read off the bundle, and the strip-free converse `Wide.li_nonneg_cfg_imp_online_ne_zero` read at the configuration.
Nothing here states a zero of Z_Q as proved; the certified zeros of relay data/b681_findings.json stay a premise. Nothing here proves
RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.EpsteinQ0
import SIDEExplicitFormula.Schema.Wide.StripFree
import Mathlib.NumberTheory.LSeries.Basic

open Complex MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

/-! ### The form and its lattice sum -/

/-- **The form** `Q0 = x² + xy + 6y²`, discriminant `−23`. -/
def Q0form (m n : ℤ) : ℤ := m ^ 2 + m * n + 6 * n ^ 2

/-- `4 Q0 = (2m + n)² + 23 n²`: the form is positive definite. -/
theorem four_mul_Q0form (m n : ℤ) : 4 * Q0form m n = (2 * m + n) ^ 2 + 23 * n ^ 2 := by
  unfold Q0form
  ring

/-- The form takes no negative value. -/
theorem Q0form_nonneg (m n : ℤ) : 0 ≤ Q0form m n := by
  nlinarith [sq_nonneg (2 * m + n), sq_nonneg n, four_mul_Q0form m n]

/-- **The coefficients** `r_Q(k)`: for `k ≥ 1` the number of `(m, n)` in the box `|m| ≤ 2k, |n| ≤ k` with `Q0(m, n) = k` (every solution
lies in the box by `four_mul_Q0form`, a fact no statement here depends on); `r_Q(0) := 0`, the origin excluded. b326's normalisation:
`r_Q(1) = 2`. -/
def rQ (k : ℕ) : ℕ :=
  if k = 0 then 0 else
    ((Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
      (fun p : ℤ × ℤ => Q0form p.1 p.2 = (k : ℤ))).card

theorem rQ_zero : rQ 0 = 0 := by
  simp [rQ]

/-- **Z_Q as its lattice sum**: the L-series `∑ r_Q(k) k^{−s}` -- Z_Q itself where the series converges (Re s > 1); Mathlib's `LSeries`
reads 0 where it does not. -/
def ZQ (s : ℂ) : ℂ := LSeries (fun k => (rQ k : ℂ)) s

/-- The gamma factor's base `2π/√23` (b685's (5.1) at `d_K = 23`, relay data/b685_count_plan.txt :45-:47). -/
def qBase : ℂ := ((2 * Real.pi / Real.sqrt 23 : ℝ) : ℂ)

/-! ### (Z1) the continuation and the functional equation, named premises -/

/-- **(Z1) THE CONTINUATION AND THE FUNCTIONAL EQUATION** -- stated, not proved; open in this kernel. `zq` agrees with the lattice sum on
Re s > 1, where the sum converges; it is holomorphic off `s = 1`; `Λ_Q(s) = (2π/√23)^{−s} Γ(s) Z_Q(s)` satisfies `Λ_Q(s) = Λ_Q(1 − s)` on
the critical strip; `zq` is real on the real line off `1`. The Poisson route (the theta of Q0 and its Mellin transform) is absent at
Mathlib de5ce8a9. -/
structure ZQContinuation (zq : ℂ → ℂ) : Prop where
  summable : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (rQ k : ℂ)) s
  agrees : ∀ s : ℂ, 1 < s.re → zq s = ZQ s
  holomorphic : DifferentiableOn ℂ zq {s : ℂ | s ≠ 1}
  functional_equation : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    qBase ^ (-s) * Complex.Gamma s * zq s = qBase ^ (-(1 - s)) * Complex.Gamma (1 - s) * zq (1 - s)
  real_on_real : ∀ x : ℝ, x ≠ 1 → (zq (x : ℂ)).im = 0

/-! ### (Z2) the zeros of Λ_Q, a named premise on the strip-free configuration -/

/-- The zeros of `Λ_Q`: the zeros of `zq` off the poles `0` and `1` of `Λ_Q` and off the trivial zeros `−1, −2, ...` (the poles of `Γ`),
anywhere in `ℂ`. -/
def LambdaQZeros (zq : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ≠ 0 ∧ ρ ≠ 1 ∧ (∀ n : ℕ, ρ ≠ -((n : ℂ) + 1)) ∧ zq ρ = 0}

/-- **(Z2) THE ZEROS OF Λ_Q AS A WIDENED CONFIGURATION** -- stated, not proved; open in this kernel. A configuration `Z` of the class
`WideConfig` (Schema/Wide/Config.lean :28-:38) whose carrier is the zeros of `Λ_Q` and whose multiplicity is each zero's order: `zq`
is `(z − ρ)^{m_ρ}` times a function analytic and nonzero at `ρ`, near `ρ`. Its fields (the open strip (−1/2, 3/2), the reflection
`ρ ↦ 1 − ρ̄`, local finiteness) are then facts about Λ_Q's zeros, carried by the premise and not proved. -/
structure ZQZeros (zq : ℂ → ℂ) (Z : WideConfig) : Prop where
  carrier_eq : Z.carrier = LambdaQZeros zq
  mult_order : ∀ ρ ∈ Z.carrier, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧ ∀ᶠ z in nhds ρ, zq z = (z - ρ) ^ Z.mult ρ * g z

/-! ### The three terms of the explicit formula -/

/-- **The zero sum** over the configuration, with multiplicity: `Σ_ρ m_ρ k̂(γ_ρ)` (b590's `ef`'s left side, Schema/Epstein.lean :43, over
the widened class). -/
def zeroSideQ (Z : WideConfig) (k : ℝ → ℂ) : ℂ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

/-- **The prime-power side**, in b321's even form, its coefficients `c` those of `−Z_Q′/Z_Q` in place of `Λ`:
`Σ_n c(n) n^{−1/2} · 2 k(log n)`. -/
def primeTermQ (c : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((c n / Real.sqrt n : ℝ) : ℂ) * (2 * k (Real.log n))

/-- Z_Q's bracket, b326's derived kernel `2 Re ψ(1/2 + i r) − 2 log(2π/√23)` (relay tools/b326_windows.py :220-:228), from the gamma
factor `(√23/2π)^s Γ(s)`. -/
def bracketQ (r : ℝ) : ℝ :=
  2 * (Complex.digamma (1 / 2 + Complex.I * (r : ℂ))).re - 2 * Real.log (2 * Real.pi / Real.sqrt 23)

/-- **The archimedean term**: `(1/2π) ∫ k̂(r) · bracketQ(r) dr`. -/
def archTermQ (k : ℝ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (bracketQ r : ℂ)

/-- **THE EXPLICIT FORMULA FOR Z_Q** -- stated, not proved; open in this kernel. T1-lit (Weil 1952; Bombieri-Lagarias 1999, as
Schema/Epstein.lean :10-:12 cites them) instantiated: for every even `C²` compactly supported `k`, the zero sum over Λ_Q's zeros equals
the pole term less the prime-power side plus the archimedean term. Its proof would re-run Zeta23/WeilEF's contour chain for Λ_Q, absent. -/
structure ZQExplicitFormula (Z : WideConfig) (c : ℕ → ℝ) : Prop where
  ef : ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k → (∀ x : ℝ, k (-x) = k x) →
    zeroSideQ Z k = poleTerm k - primeTermQ c k + archTermQ k

/-! ### The bundle and what compiles from it -/

/-- **THE Z_Q PREMISES**: (Z1) the continuation and functional equation; (Z2) the zeros of Λ_Q as the configuration `Z`; the
logarithmic derivative's series on Re s ≥ 3/2 with coefficients `c` (their recursion from `a = r_Q` not written: the series determines
them); the explicit formula; and the local count `Wide.HCount Z A0Q` (`A0Q = 10`, Schema/EpsteinQ0.lean :104; P3, derived at b685-b687
and not compiled) on the same configuration. Each stated, not proved; open. -/
structure ZQPremises (zq : ℂ → ℂ) (Z : WideConfig) (c : ℕ → ℝ) : Prop where
  continuation : ZQContinuation zq
  zeros : ZQZeros zq Z
  logDeriv : ∀ s : ℂ, 3 / 2 ≤ s.re → LSeries (fun n => (c n : ℂ)) s = -(deriv zq s / zq s)
  explicitFormula : ZQExplicitFormula Z c
  count : Wide.HCount Z A0Q

/-- No point of Λ_Q's zero configuration is `0`, from (Z2): the carrier excludes the pole. -/
theorem zqZeros_ne_zero {zq : ℂ → ℂ} {Z : WideConfig} (h : ZQZeros zq Z) : ∀ ρ ∈ Z.carrier, ρ ≠ 0 := by
  intro ρ hρ
  rw [h.carrier_eq] at hρ
  first
    | exact hρ.1
    | (simp only [LambdaQZeros, Set.mem_setOf_eq] at hρ; exact hρ.1)

/-- **The local count on Λ_Q's zeros**, read off the bundle. -/
theorem zq_count {zq : ℂ → ℂ} {Z : WideConfig} {c : ℕ → ℝ} (h : ZQPremises zq Z c) : Wide.HCount Z A0Q :=
  h.count

/-- **The explicit formula for Z_Q**, read off the bundle. -/
theorem zq_explicit_formula {zq : ℂ → ℂ} {Z : WideConfig} {c : ℕ → ℝ} (h : ZQPremises zq Z c) (k : ℝ → ℂ)
    (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) (he : ∀ x : ℝ, k (-x) = k x) :
    zeroSideQ Z k = poleTerm k - primeTermQ c k + archTermQ k :=
  h.explicitFormula.ef k hk hs he

/-- **The strip-free converse read at Z_Q** (Schema/Wide/StripFree.lean :157): under the Z_Q premises, Li positivity of the configuration
of Λ_Q's zeros would put every one on the line -- the kernel's theorem at this configuration, its count and `ρ ≠ 0` from the bundle. -/
theorem zq_li_nonneg_imp_online {zq : ℂ → ℂ} {Z : WideConfig} {c : ℕ → ℝ} (h : ZQPremises zq Z c) :
    (∀ n : ℕ, 0 ≤ Wide.liCoeff Z n) → ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  Wide.li_nonneg_cfg_imp_online_ne_zero Z h.count (zqZeros_ne_zero h.zeros)

end Schema
end SIDEExplicitFormula
