/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/RateIndexCfg.lean
THIS PROGRAMME'S WORK (act b658, ruling (R268)(3)-(4); W-ORD-E1-CFG) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

E1 OVER A CONFIGURATION. RateIndex.lean's two statements (`rest_norm_le_rate`, `zeroSide_neg_at_rate`) carried from
`Zeta23.zetaZeroConfig` to any `WeilConfig`, reading its points and multiplicities (`C.toZeroConfig`) alone; the local
count enters as the hypothesis `hA` with its constant `A₀`, as in the ζ statements, and the summability of the dominant is
taken from it (`dominant_summable_hcount`), not from the structure's `count` field. The ζ-specific declarations the ζ proof
consumes are replaced by Converse.lean's twins (`fR_cfg`, `fR_norm_le_cfg`, `fR_bound_cfg`, `sT_cfg`, `mem_sT_cfg`) and
Config.lean's `zeroSide_cfg`; every hypothesis is the ζ statement's (relay data/b658_e1cfg_statement.txt). The ζ statements
are the instances at `zetaWeilConfig` (Instances.lean :25), by `rfl`. RateIndex.lean is not edited.
Nothing here proves RH or GRH or locates any zero.
-/
import SIDEExplicitFormula.Schema.Instances
import SIDEExplicitFormula.RateIndex

open Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

variable {C : WeilConfig} {g0 : ℝ → ℝ} {L M : ℝ}

/-- The dominant of E1's rest, summable over the configuration's points from a local count `hA` given as a hypothesis
(`dominant_summable_cfg`'s argument with `hA` in place of the structure's `count` field). -/
theorem dominant_summable_hcount (H : PWSetup C.toZeroConfig g0 L M) {A₀ : ℝ} (hA : HCount C.toZeroConfig A₀)
    (B : ℝ) (D : ℕ) :
    Summable (fun ρ : C.toZeroConfig.carrier => (C.toZeroConfig.mult ρ : ℝ) *
      (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))) := by
  have hM := H.hM
  have hAw := Aw_nonneg H
  exact weighted_summable C.toZeroConfig hA
    (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
    (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
    (fun ρ _ => mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
    (fun ρ hρ => zero_weight H B D ρ hρ)

/-- **E1's rate for the rest, over a configuration.** For `C` a `WeilConfig`, under the hypotheses of `rest_norm_le_rate`
with `C.toZeroConfig` in place of `Zeta23.zetaZeroConfig`, at every `j ≥ D` the rest over `M ^ (2 ^ (j + 1))` has norm at
most `θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 A₀ Bf zeta3Sum)`. -/
theorem rest_norm_le_rate_cfg (H : PWSetup C.toZeroConfig g0 L M)
    (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hQb : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ ρ ∈ C.toZeroConfig.carrier, ρ ∉ tieSet C.toZeroConfig g0 M →
      ρ ∉ killSet C.toZeroConfig g0 M → offScore g0 ρ / M ≤ θ)
    (A₀ : ℝ) (hA : HCount C.toZeroConfig A₀)
    (j : ℕ) (hj : D ≤ j) :
    ‖∑' x, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤
      θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) := by
  have hM := H.hM
  have hAw := Aw_nonneg H
  have hN : 2 ^ (D + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hθk : 0 ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) := pow_nonneg hθ0 _
  have hdom0 : ∀ x : C.toZeroConfig.carrier, 0 ≤ (C.toZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) := fun x =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg B) (by positivity))
      (pow_nonneg (div_nonneg (norm_nonneg _) hM.le) _))
  have hterm : ∀ x : C.toZeroConfig.carrier,
      ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
        ((C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := by
    intro x
    by_cases hT : (x : ℂ) ∈ tieSet C.toZeroConfig g0 M
    · have h0 : fR_cfg H Q j x = 0 := by
        unfold fR_cfg
        rw [if_pos hT]
      rw [h0, zero_div, norm_zero]
      exact mul_nonneg hθk (hdom0 x)
    by_cases hK : (x : ℂ) ∈ killSet C.toZeroConfig g0 M
    · have h0 : fR_cfg H Q j x = 0 := by
        unfold fR_cfg
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
    calc ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
        ≤ (C.toZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (j + 1))) :=
          fR_norm_le_cfg H Q B D hQb j x hT
      _ ≤ (C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) *
            ((offScore g0 x / M) ^ (2 ^ (D + 1)) * θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (Nat.cast_nonneg _)
      _ = θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
            ((C.toZeroConfig.mult x : ℝ) * (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := by
          ring
  have hbound : (∑' x : C.toZeroConfig.carrier, (C.toZeroConfig.mult x : ℝ) *
      (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) ≤
      3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum := by
    refine (dominant_summable_hcount H hA B D).tsum_le_of_sum_le (fun u => ?_)
    calc (∑ x ∈ u, (C.toZeroConfig.mult (x : ℂ) : ℝ) *
          (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))))
        = ∑ ρ ∈ u.map (Function.Embedding.subtype (· ∈ C.toZeroConfig.carrier)),
            (C.toZeroConfig.mult ρ : ℝ) *
              (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1))) :=
          (Finset.sum_map u (Function.Embedding.subtype (· ∈ C.toZeroConfig.carrier))
            (fun ρ => (C.toZeroConfig.mult ρ : ℝ) *
              (B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1))))).symm
      _ ≤ 3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum :=
          weighted_finite_bound C.toZeroConfig hA
            (fun ρ => B ^ 2 * (1 + ‖wOf ρ‖) ^ (2 * D) * (offScore g0 ρ / M) ^ (2 ^ (D + 1)))
            (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) (by positivity)
            (fun ρ hρ => zero_weight H B D ρ hρ) _ (fun ρ hρ => by
              obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hρ
              exact i.2)
  calc ‖∑' x, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖
      ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * ∑' x : C.toZeroConfig.carrier, (C.toZeroConfig.mult x : ℝ) *
          (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) :=
        tsum_of_norm_bounded ((dominant_summable_hcount H hA B D).hasSum.mul_left _) hterm
    _ ≤ θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
          (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) :=
        mul_le_mul_of_nonneg_left hbound hθk

/-- **E1 over a configuration.** For `C` a `WeilConfig`, a base `g0` and the dominant score `M` fixed by
`H : PWSetup C.toZeroConfig g0 L M`; a coefficient family `Q` meeting the tie conditions with the bound `B (1 + ‖w‖) ^ D`;
`θ` bounding `offScore g0 ρ / M` at every point of `C` outside the tie and kill sets; `A₀` a local count's constant for `C`
(`HCount C.toZeroConfig A₀`): at every index `j ≥ D` at which `θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) * (3 A₀ Bf zeta3Sum)`,
`Bf = 128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))`, is below the tie terms' sum `∑ x ∈ sT_cfg H, mult x * Nf H x`, the
zero side of `C` for the window of index `j` has negative real part. -/
theorem zeroSide_neg_at_rate_cfg (H : PWSetup C.toZeroConfig g0 L M)
    (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hQtie : ∀ j, ∀ ρ ∈ tieSet C.toZeroConfig g0 M,
      (Polynomial.aeval (vOf ρ) (Q j)) ^ 2 * Xval H j ρ = -(‖Xval H j ρ‖ : ℂ))
    (hQb : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ ρ ∈ C.toZeroConfig.carrier, ρ ∉ tieSet C.toZeroConfig g0 M →
      ρ ∉ killSet C.toZeroConfig g0 M → offScore g0 ρ / M ≤ θ)
    (A₀ : ℝ) (hA : HCount C.toZeroConfig A₀)
    (j : ℕ) (hj : D ≤ j)
    (hrate : θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
        (3 * A₀ * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) <
      ∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x) :
    (zeroSide_cfg C (kWindow (coeffList (Pof H (Q j))) g0 j)).re < 0 := by
  classical
  have hlt : ‖∑' x, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ <
      ∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x :=
    lt_of_le_of_lt (rest_norm_le_rate_cfg H Q B D hQb θ hθ0 hθ A₀ hA j hj) hrate
  have hM := H.hM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMN : (M : ℂ) ^ (2 ^ (j + 1)) ≠ 0 := pow_ne_zero _ hM0
  have hsplit : ∀ x : C.toZeroConfig.carrier,
      (C.toZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) =
        (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
          Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) +
          fR_cfg H Q j x := by
    intro x
    unfold fR_cfg
    split_ifs <;> simp
  have hzeroT : ∀ x ∉ sT_cfg H, (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) = 0 :=
    fun x hx => if_neg (fun h => hx ((mem_sT_cfg H x).mpr h))
  have hsumT : Summable (fun x : C.toZeroConfig.carrier =>
      if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0) :=
    summable_of_ne_finset_zero hzeroT
  have hsumR : Summable (fR_cfg H Q j) := by
    refine Summable.of_norm_bounded ((dominant_summable_hcount H hA B D).mul_left (M ^ (2 ^ (j + 1)))) (fun x => ?_)
    have hb := fR_bound_cfg H Q B D hQb j hj x
    calc ‖fR_cfg H Q j x‖
        = ‖fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))‖ * ‖(M : ℂ) ^ (2 ^ (j + 1))‖ := by
          rw [← norm_mul, div_mul_cancel₀ _ hMN]
      _ ≤ (C.toZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1))) * M ^ (2 ^ (j + 1)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
          exact mul_le_mul_of_nonneg_right hb (pow_nonneg hM.le _)
      _ = M ^ (2 ^ (j + 1)) * ((C.toZeroConfig.mult x : ℝ) *
            (B ^ 2 * (1 + ‖wOf x‖) ^ (2 * D) * (offScore g0 x / M) ^ (2 ^ (D + 1)))) := mul_comm _ _
  have hT : ∀ x ∈ sT_cfg H, ((C.toZeroConfig.mult x : ℂ) *
      Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x)).re =
        -((C.toZeroConfig.mult x : ℝ) * Nf H x * M ^ (2 ^ (j + 1))) := by
    intro x hx
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      tie_term_neg H (Q j) j (hQtie j) ((mem_sT_cfg H x).mp hx)]
    ring
  have hR : (∑' x, fR_cfg H Q j x).re <
      (∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (j + 1)) := by
    have h1 : (∑' x, fR_cfg H Q j x) =
        (∑' x, fR_cfg H Q j x / (M : ℂ) ^ (2 ^ (j + 1))) * (M : ℂ) ^ (2 ^ (j + 1)) := by
      rw [tsum_div_const, div_mul_cancel₀ _ hMN]
    have h2 : ‖∑' x, fR_cfg H Q j x‖ <
        (∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℝ) * Nf H x) * M ^ (2 ^ (j + 1)) := by
      rw [h1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact mul_lt_mul_of_pos_right hlt (pow_pos hM _)
    exact lt_of_le_of_lt (Complex.re_le_norm _) h2
  have hTsum : (∑ x ∈ sT_cfg H, (if (x : ℂ) ∈ tieSet C.toZeroConfig g0 M then
      (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) else 0)) =
      ∑ x ∈ sT_cfg H, (C.toZeroConfig.mult x : ℂ) *
        Zeta23.paperFT (kWindow (coeffList (Pof H (Q j))) g0 j) (Zeta23.gammaOf x) :=
    Finset.sum_congr rfl (fun x hx => if_pos ((mem_sT_cfg H x).mp hx))
  unfold zeroSide_cfg
  rw [tsum_congr hsplit, Summable.tsum_add hsumT hsumR, tsum_eq_sum hzeroT, hTsum, Complex.add_re, Complex.re_sum,
    Finset.sum_congr rfl hT, Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

/-- **The ζ instance of the rest's rate**: `rest_norm_le_rate_cfg` at `zetaWeilConfig` is `rest_norm_le_rate`, by definition. -/
theorem rest_norm_le_rate_cfg_zeta :
    @rest_norm_le_rate_cfg zetaWeilConfig = @B321.rest_norm_le_rate := rfl

/-- **The ζ instance of E1**: `zeroSide_neg_at_rate_cfg` at `zetaWeilConfig` is `zeroSide_neg_at_rate`, by definition. -/
theorem zeroSide_neg_at_rate_cfg_zeta :
    @zeroSide_neg_at_rate_cfg zetaWeilConfig = @B321.zeroSide_neg_at_rate := rfl

end Schema
end SIDEExplicitFormula
