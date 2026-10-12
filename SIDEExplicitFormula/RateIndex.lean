/-
SIDE-explicit-formula -- SIDEExplicitFormula/RateIndex.lean
THIS PROGRAMME'S WORK (act b654, ruling (R264)(3); E1 of relay data/b559_constants.txt :149-:152) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

E1, THE CONFIGURATION-RELATIVE RATE. `zeroSide_eventually_neg` (PowerLimit.lean:1082) reads its index off a limit
(PowerLimit.lean:1092, over `rest_tendsto_zero`, :1025). Here the rest is bounded at each index `j ≥ D` by a rate in a
bound `θ` on `offScore g0 ρ / M` off the tie and kill sets (`rest_norm_le_rate`), and the zero side is negative at every
index where that rate falls below the tie terms' sum (`zeroSide_neg_at_rate`). Every hypothesis is fixed in the statements
(relay data/b654_e1_statement.txt). The second proof is `zeroSide_eventually_neg`'s own (PowerLimit.lean:1085-:1154)
at the index `j`, its limit step replaced by the rate.
-/
import SIDEExplicitFormula.PowerLimit

open Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace B321

variable {g0 : ℝ → ℝ} {L M : ℝ}

/-- **E1's rate for the rest.** Under the hypotheses of `zeroSide_neg_at_rate` that bear on the rest, at every `j ≥ D` the rest over
`M ^ (2 ^ (j + 1))` has norm at most `θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 A₀ Bf zeta3Sum)`. -/
theorem rest_norm_le_rate (H : PWSetup Zeta23.zetaZeroConfig g0 L M)
    (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hQb : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ ∉ tieSet Zeta23.zetaZeroConfig g0 M →
      ρ ∉ killSet Zeta23.zetaZeroConfig g0 M → offScore g0 ρ / M ≤ θ)
    (A₀ : ℝ) (hA : HCount Zeta23.zetaZeroConfig A₀)
    (j : ℕ) (hj : D ≤ j) :
    ‖∑' x, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) := by
  have hM := H.hM
  have hAw := Aw_nonneg H
  have hN : 2 ^ (D + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hθk : 0 ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) := pow_nonneg hθ0 _
  have hdom0 : ∀ x : Zeta23.zetaZeroConfig.carrier, 0 ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) := fun x =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
  have hterm : ∀ x : Zeta23.zetaZeroConfig.carrier,
      ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
        ((Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := by
    intro x
    by_cases hT : (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M
    · have h0 : fR H Q j x = 0 := by
        unfold fR
        rw [if_pos hT]
      rw [h0, zero_div, norm_zero]
      exact mul_nonneg hθk (hdom0 x)
    by_cases hK : (x : ℂ) ∈ killSet Zeta23.zetaZeroConfig g0 M
    · have h0 : fR H Q j x = 0 := by
        unfold fR
        rw [if_neg hT, kill_term_zero H (Q j) j hK, mul_zero]
      rw [h0, zero_div, norm_zero]
      exact mul_nonneg hθk (hdom0 x)
    have hr0 : 0 ≤ offScore g0 x / M := div_nonneg (norm_nonneg _) hM.le
    have hrθ : offScore g0 x / M ≤ θ := hθ x x.2 hT hK
    have hpow : (offScore g0 x / M) ^ (2 ^ (j + 1)) ≤
        (offScore g0 x / M) ^ (2 ^ (D + 1)) * θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) := by
      calc (offScore g0 x / M) ^ (2 ^ (j + 1))
          = (offScore g0 x / M) ^ (2 ^ (D + 1) + (2 ^ (j + 1) - 2 ^ (D + 1))) := by
            rw [Nat.add_sub_of_le hN]
        _ = (offScore g0 x / M) ^ (2 ^ (D + 1)) * (offScore g0 x / M) ^ (2 ^ (j + 1) - 2 ^ (D + 1)) := pow_add _ _ _
        _ ≤ (offScore g0 x / M) ^ (2 ^ (D + 1)) * θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrθ _) (pow_nonneg hr0 _)
    calc ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
        ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) :=
          fR_norm_le H Q B D hQb j x hT
      _ ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) *
            ((offScore g0 x / M) ^ (2 ^ (D + 1)) * θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (Nat.cast_nonneg _)
      _ = θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
            ((Zeta23.zetaZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := by
          ring
  have hbound : (∑' x : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) ≤
      3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum := by
    refine (dominant_summable H B D).tsum_le_of_sum_le (fun u => ?_)
    calc (∑ x ∈ u, (Zeta23.zetaZeroConfig.mult (x : ℂ) : ℝ) *
          (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))))
        = ∑ ρ ∈ u.map (Function.Embedding.subtype (· ∈ Zeta23.zetaZeroConfig.carrier)),
            (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
              (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1))) :=
          (Finset.sum_map u (Function.Embedding.subtype (· ∈ Zeta23.zetaZeroConfig.carrier))
            (fun ρ => (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
              (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1))))).symm
      _ ≤ 3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum :=
          weighted_finite_bound Zeta23.zetaZeroConfig hA
            (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
            (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
            (fun ρ hρ => zero_weight H B D ρ hρ) _ (fun ρ hρ => by
              obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hρ
              exact i.2)
  calc ‖∑' x, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
      ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * ∑' x : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.mult x : ℝ) *
          (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
        tsum_of_norm_bounded ((dominant_summable H B D).hasSum.mul_left _) hterm
    _ ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
          (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) :=
        mul_le_mul_of_nonneg_left hbound hθk

/-- **E1, the configuration-relative rate (b654, `(R264)`(3)).** For the configuration `zetaZeroConfig`, a base `g0` and the dominant
score `M` fixed by `H`; a coefficient family `Q` meeting the tie conditions with the bound `B (1 + ‖w‖) ^ D`; `θ` bounding `offScore g0 ρ / M`
at every zero outside the tie and kill sets; `A₀` the local count's constant: at every index `j ≥ D` at which
`θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 A₀ Bf zeta3Sum)`, `Bf = 128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))`, is below the tie terms'
sum `∑ x ∈ sT H, mult x * Nf H x`, the zero side of the window of index `j` has negative real part. -/
theorem zeroSide_neg_at_rate (H : PWSetup Zeta23.zetaZeroConfig g0 L M)
    (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hQtie : ∀ j, ∀ ρ ∈ tieSet Zeta23.zetaZeroConfig g0 M,
      (Polynomial.aeval (vOf ρ) (Q j)) ^ 2 * Xval H j ρ = -(‖Xval H j ρ‖ : ℂ))
    (hQb : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ ∉ tieSet Zeta23.zetaZeroConfig g0 M →
      ρ ∉ killSet Zeta23.zetaZeroConfig g0 M → offScore g0 ρ / M ≤ θ)
    (A₀ : ℝ) (hA : HCount Zeta23.zetaZeroConfig A₀)
    (j : ℕ) (hj : D ≤ j)
    (hrate : θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
        (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) <
      ∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x) :
    (zeroSide (kWindow (coeffList (Pof H (Q j))) g0 j)).re < 0 := by
  classical
  have hlt : ‖∑' x, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ <
      ∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x :=
    lt_of_le_of_lt (rest_norm_le_rate H Q B D hQb θ hθ0 hθ A₀ hA j hj) hrate
  have hM := H.hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMN : (M : ℂ) ^ (2 ^ (j + 1)) ≠ 0 := pow_ne_zero _ hM0
  have hsplit : ∀ x : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) =
        (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) +
          fR H Q j x := by
    intro x
    unfold fR
    split_ifs <;> simp
  have hzeroT : ∀ x ∉ sT H, (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) = 0 :=
    fun x hx => if_neg (fun h => hx ((mem_sT H x).mpr h))
  have hsumT : Summable (fun x : Zeta23.zetaZeroConfig.carrier =>
      if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) :=
    summable_of_ne_finset_zero hzeroT
  have hsumR : Summable (fR H Q j) := by
    refine Summable.of_norm_bounded ((dominant_summable H B D).mul_left (M ^ (2 ^ (j + 1)))) (fun x => ?_)
    have hb := fR_bound H Q B D hQb j hj x
    calc ‖fR H Q j x‖
        = ‖fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ * ‖(M : ℂ) ^ (2 ^ (j + 1))‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hMN]
      _ ≤ (Zeta23.zetaZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) * M ^ (2 ^ (j + 1)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact mul_le_mul_of_nonneg_right hb (pow_nonneg hM.le _)
      _ = M ^ (2 ^ (j + 1)) * ((Zeta23.zetaZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := mul_comm _ _
  have hT : ∀ x ∈ sT H, ((Zeta23.zetaZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x)).re =
        -((Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x * M ^ (2 ^ (j + 1))) := by
    intro x hx
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      tie_term_neg H (Q j) j (hQtie j) ((mem_sT H x).mp hx)]
    ring
  have hR : (∑' x, fR H Q j x).re <
      (∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (j + 1)) := by
    have h1 : (∑' x, fR H Q j x) =
        (∑' x, fR H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) * (M : ℂ) ^ (2 ^ (j + 1)) := by
      rw [tsum_div_const, div_mul_cancel₀ _ hMN]
    have h2 : ‖∑' x, fR H Q j x‖ <
        (∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (j + 1)) := by
      rw [h1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact mul_lt_mul_of_pos_right hlt (pow_pos hM _)
    exact lt_of_le_of_lt (Complex.re_le_norm _) h2
  have hTsum : (∑ x ∈ sT H, (if (x : ℂ) ∈ tieSet Zeta23.zetaZeroConfig g0 M then
      (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0)) =
      ∑ x ∈ sT H, (Zeta23.zetaZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) :=
    Finset.sum_congr rfl (fun x hx => if_pos ((mem_sT H x).mp hx))
  unfold zeroSide
  rw [tsum_congr hsplit, Summable.tsum_add hsumT hsumR, tsum_eq_sum hzeroT, hTsum, Complex.add_re, Complex.re_sum,
    Finset.sum_congr rfl hT, Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

end B321
end SIDEExplicitFormula
