import SIDEExplicitFormula.Window.FarJoin
import SIDEExplicitFormula.Window.FarLags

/-!
# L9c2: the far sum as a constant and a coefficient of each `log n`, `n ≤ 16369`

Each pair `k, m` of `farK` reads the convolution sums from the place `aKM k m`, where `lamT` is in closed form (`lamT_at`);
the shift is padded to `16369` places, the `log (1 + c)` part read at `n = c + 1` (`sum_log_succ`), and the pairs regrouped
inside each `log n` (`regroup3`). Each coefficient is then the place `n` of `farNumL` over `6 * farDEN` (`far_coef`, with
`farNumL_place`), the term `n = 0` being `0` since `log 0 = 0`, and the constant the sum of `farGL` over `6 * farDEN`.
-/

namespace SIDEExplicitFormula
namespace Window

theorem farNumL_place (n : ℕ) (hn : n < 16370) : farNumL.getD n 0 = farW n (autoD.drop (16360 + n)) := by
  have h := winOK_spec farW farNumL (autoD.drop 16360) 0 farNumL_all n (by rw [farNumL_len]; exact hn)
  rw [h, zero_add, drop_drop_add]

theorem farGL_place (c : ℕ) (hc : c < 16369) : farGL.getD c 0 = gW c (autoD.drop (16360 + c)) := by
  have h := winOK_spec gW farGL (autoD.drop 16360) 0 farGL_all c (by rw [farGL_len]; exact hc)
  rw [h, zero_add, drop_drop_add]

theorem autoD_getD_past (x : ℕ) (hx : 2 * 16365 ≤ x) : autoD.getD x 0 = 0 := by
  have hlen : autoD.length ≤ x := by rw [autoD_len, coeffList_len]; exact hx
  exact List.getD_eq_default autoD 0 hlen

/-- The coefficient of `log n` that the pair `k, m` gives. -/
noncomputable def farPhi (k m n : ℕ) : ℝ :=
  (autoD.getD (aKM k m + (n - 1)) 0 : ℝ) * lA k ((n - 1 : ℕ) : ℝ) + (autoD.getD (aKM k m + n) 0 : ℝ) * lB k (n : ℝ)

/-- The part with no logarithm that the pair `k, m` gives. -/
noncomputable def farGam (k m : ℕ) : ℝ :=
  ∑ c ∈ Finset.range 16369, (autoD.getD (aKM k m + c) 0 : ℝ) * lG k (c : ℝ)

theorem far_pair (k m : ℕ) (hk : k ≤ 3) (hm : m ≤ 4) :
    ∑ t ∈ Finset.range (2 * 16365), (autoD.getD t 0 : ℝ) * lamT k ((k : ℤ) + ((t : ℤ) - ((16365 : ℕ) - 1)) - m) =
      ∑ n ∈ Finset.range (16369 + 1), farPhi k m n * Real.log (n : ℝ) + farGam k m := by
  have ha1 : 16361 ≤ aKM k m := by unfold aKM; omega
  have ha2 : aKM k m ≤ 16368 := by unfold aKM; omega
  have hz : ∀ c, 2 * 16365 - aKM k m ≤ c → (autoD.getD (aKM k m + c) 0 : ℝ) = 0 := by
    intro c hc
    rw [autoD_getD_past (aKM k m + c) (by omega), Int.cast_zero]
  have h1 : ∀ t ∈ Finset.range (2 * 16365),
      (autoD.getD t 0 : ℝ) * lamT k ((k : ℤ) + ((t : ℤ) - ((16365 : ℕ) - 1)) - m) =
        if aKM k m ≤ t then (autoD.getD t 0 : ℝ) * (lA k ((t - aKM k m : ℕ) : ℝ) * Real.log (1 + ((t - aKM k m : ℕ) : ℝ)) +
          lB k ((t - aKM k m : ℕ) : ℝ) * Real.log ((t - aKM k m : ℕ) : ℝ) + lG k ((t - aKM k m : ℕ) : ℝ)) else 0 := by
    intro t _
    rw [lamT_at k m t hk, mul_ite, mul_zero]
  rw [Finset.sum_congr rfl h1, shift_ge_sum (2 * 16365) (aKM k m) (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [sum_range_pad (2 * 16365 - aKM k m) 16369 (by omega)]
  swap
  · intro c hc
    simp only [hz c hc, zero_mul]
  have e1 : ∀ c ∈ Finset.range 16369, (autoD.getD (aKM k m + c) 0 : ℝ) * (lA k (c : ℝ) * Real.log (1 + (c : ℝ)) +
      lB k (c : ℝ) * Real.log (c : ℝ) + lG k (c : ℝ)) =
      (autoD.getD (aKM k m + c) 0 : ℝ) * lA k (c : ℝ) * Real.log (1 + (c : ℝ)) +
        (autoD.getD (aKM k m + c) 0 : ℝ) * lB k (c : ℝ) * Real.log (c : ℝ) +
          (autoD.getD (aKM k m + c) 0 : ℝ) * lG k (c : ℝ) := by
    intro c _
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_succ]
  have e2 : ∑ c ∈ Finset.range 16369, (autoD.getD (aKM k m + c) 0 : ℝ) * lB k (c : ℝ) * Real.log (c : ℝ) =
      ∑ n ∈ Finset.range (16369 + 1), (autoD.getD (aKM k m + n) 0 : ℝ) * lB k (n : ℝ) * Real.log (n : ℝ) := by
    rw [Finset.sum_range_succ _ 16369, hz 16369 (by omega), zero_mul, zero_mul, add_zero]
  rw [e2, ← Finset.sum_add_distrib]
  unfold farPhi farGam
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem far_regroup :
    ∑ t ∈ Finset.range (2 * 16365), (autoD.getD t 0 : ℝ) * farK ((t : ℤ) - ((16365 : ℕ) - 1)) =
      ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 *
        (∑ n ∈ Finset.range (16369 + 1), farPhi k m n * Real.log (n : ℝ) + farGam k m) := by
  have h : ∀ t ∈ Finset.range (2 * 16365), (autoD.getD t 0 : ℝ) * farK ((t : ℤ) - ((16365 : ℕ) - 1)) =
      ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 *
        ((autoD.getD t 0 : ℝ) * lamT k ((k : ℤ) + ((t : ℤ) - ((16365 : ℕ) - 1)) - m)) := by
    intro t _
    unfold farK
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← Finset.mul_sum, far_pair k m (by simp at hk; omega) (by simp at hm; omega)]

theorem far_coef (n : ℕ) (hn1 : 1 ≤ n) :
    ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * farPhi k m n =
      (farW n (autoD.drop (16360 + n)) : ℝ) / (6 * (farDEN : ℝ)) := by
  rw [farW_eq]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hk' : k ≤ 3 := by simp at hk; omega
  have iA : aKM k m + (n - 1) = 16360 + n + (3 + m - k) := by unfold aKM; omega
  have iB : aKM k m + n = 16360 + n + (4 + m - k) := by unfold aKM; omega
  unfold farPhi
  rw [lA_poly k hk', lB_poly k hk', iA, iB, getD_drop_add, getD_drop_add]
  ring

theorem gam_coef (c : ℕ) :
    ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * ((autoD.getD (aKM k m + c) 0 : ℝ) * lG k (c : ℝ)) =
      (gW c (autoD.drop (16360 + c)) : ℝ) / (6 * (farDEN : ℝ)) := by
  rw [gW_eq]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hk' : k ≤ 3 := by simp at hk; omega
  have iC : aKM k m + c = 16360 + c + (4 + m - k) := by unfold aKM; omega
  rw [lG_poly k hk', iC, getD_drop_add]
  ring

theorem far_gam :
    ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * farGam k m =
      ∑ c ∈ Finset.range 16369, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) := by
  unfold farGam
  simp only [Finset.mul_sum]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [gam_coef c, farGL_place c (by simp at hc; omega)]

/-- The far sum collected by lag, as a constant and a coefficient of each `log n`, each over `6 * farDEN`. -/
theorem far_comb :
    ∑ t ∈ Finset.range (2 * 16365), (autoD.getD t 0 : ℝ) * farK ((t : ℤ) - ((16365 : ℕ) - 1)) =
      ∑ c ∈ Finset.range 16369, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) +
        ∑ n ∈ Finset.range (16369 + 1), (farNumL.getD n 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (n : ℝ) := by
  rw [far_regroup, regroup3, far_gam]
  congr 1
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0
    simp only [Nat.cast_zero, Real.log_zero, mul_zero]
  · rw [far_coef n h1, farNumL_place n (by simp at hn; omega)]

/-- **L9c2**: the far sum of `archJ_basis_local` as a constant and a coefficient of each `log n`, `n ≤ 16369`, read from the
data `farGL` and `farNumL` over `6 * farDEN`, times the square of the numerators' scale. -/
theorem far_final :
    ∑ j ∈ Finset.Icc 16 16380, coeff j * ∑ i ∈ Finset.Icc 16 16380, coeff i *
        ∑ k ∈ Finset.range 4, ∑ m ∈ Finset.range 5, (bw m : ℝ) / 6 * lamT k (k + ((i : ℤ) - j) - m) =
      (∑ c ∈ Finset.range 16369, (farGL.getD c 0 : ℝ) / (6 * (farDEN : ℝ)) +
        ∑ n ∈ Finset.range (16369 + 1), (farNumL.getD n 0 : ℝ) / (6 * (farDEN : ℝ)) * Real.log (n : ℝ)) *
        ((10 ^ coeffScale)⁻¹ * (10 ^ coeffScale)⁻¹) := by
  rw [far_lags, far_comb]

end Window
end SIDEExplicitFormula
