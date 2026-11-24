import SIDEExplicitFormula.Window.ArchComb
import SIDEExplicitFormula.Window.Arch
import SIDEExplicitFormula.Window.PoleComb
import SIDEExplicitFormula.Window.PrimeFinite
import SIDEExplicitFormula.Window.CQValues

/-!
# L11c: the arithmetic side at the window as the combination, in the integers' form

The pole term by `poleTerm_windowK_intH` and `poleSum_comb` (L11a), the prime-power side by `primeTermQ_cQ_eq_finite_sum` at
`N = 1024` with `windowK (log n)` through `Kt n` (`windowK_log_eq_Kt`), and the archimedean term by `archTermQ_windowK` with L9c
(`archJ_comb`) and `k(0)` as data (`windowK_zero`, so `windowKx 1 = k(0)`). The real part of the arithmetic side is then a rational
constant, the constants `log 23`, `log 2`, `log π` and Euler's constant times `k(0)`, a coefficient of each `log m`, `m < 16390`, and
the prime-power side's terms `2 cQ(n) Kt(n) / (80640 n^4 10^34)`, `2 ≤ n < 1024`. Nothing here is evaluated.
-/

namespace SIDEExplicitFormula
namespace Window

/-- `k(0)` as data. -/
noncomputable def kap0 : ℝ := (k0Num : ℝ) / (80640 * 10 ^ 34)

/-- The coefficient of `log m` in the arithmetic side: the pole term's and the archimedean sums'. -/
noncomputable def combCoef (m : ℕ) : ℝ :=
  2 * ((intHNum : ℝ) / (16 * 10 ^ coeffScale)) * poleCoef m + 2 * archCoef m

theorem windowK_zero_kap : windowK 0 = ((kap0 : ℝ) : ℂ) := windowK_zero

theorem windowKx_one_eq : windowKx 1 = kap0 := by
  have h1 := windowK_log (n := 1) (by norm_num)
  rw [Real.log_one, windowK_zero_kap] at h1
  have h3 := Complex.ofReal_inj.mp h1
  rw [Real.sqrt_one, one_mul] at h3
  show (∫ y in Set.Ioi 1, windowH (1 * y) * windowH y) = kap0
  exact h3.symm

theorem log_sqrt23 :
    Real.log (Real.sqrt 23 / (2 * Real.pi)) = Real.log 23 / 2 - Real.log 2 - Real.log Real.pi := by
  have h1 : Real.sqrt 23 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  rw [Real.log_div h1 h2, Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_sqrt (by norm_num)]
  ring

theorem poleCoef_high (m : ℕ) (hm : 16385 ≤ m) : poleCoef m = 0 := by
  unfold poleCoef
  rw [Finset.sum_eq_zero (fun k hk => by
    rw [coeff_eq_zero_of_not (m - k) (by have := Finset.mem_range.mp hk; omega), mul_zero]), mul_zero]

/-- The pole term at the window, gathered at each `log m`. -/
theorem poleTerm_comb :
    B321.poleTerm windowK =
      ((2 * ((intHNum : ℝ) / (16 * 10 ^ coeffScale)) * ∑ m ∈ Finset.range 16385, poleCoef m * Real.log m : ℝ) : ℂ) := by
  rw [poleTerm_windowK_intH, poleSum_comb]
  congr 1
  ring

/-- The prime-power side at the window: each `n < 1024`'s term through `Kt n`. -/
theorem primeTermQ_comb :
    Schema.primeTermQ Schema.ZQ.cQ windowK =
      ((∑ n ∈ Finset.Ico 2 1024, 2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) : ℝ) : ℂ) := by
  have hk := windowK_classK
  unfold B321.classK at hk
  obtain ⟨-, hcd, -, -⟩ := hk
  have hc : Continuous windowK := hcd.continuous
  have hs : ∀ u : ℝ, Real.log ((1024 : ℕ) : ℝ) < |u| → windowK u = 0 := fun u hu =>
    windowK_eq_zero u (by first | exact_mod_cast hu | (norm_num at hu; exact hu))
  rw [primeTermQ_cQ_eq_finite_sum windowK 1024 (by norm_num) hc hs, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
  have hpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hsq : Real.sqrt n ≠ 0 := hpos.ne'
  have e : ∀ a b : ℝ, (a : ℂ) * (2 * (b : ℂ)) = ((a * (2 * b) : ℝ) : ℂ) := fun a b => by
    push_cast <;> ring
  rw [windowK_log_eq_Kt n (by omega), e]
  congr 1
  calc _ = 2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) * (Real.sqrt n / Real.sqrt n) := by ring
    _ = _ := by rw [div_self hsq, mul_one]

/-- The archimedean term at the window by L9c, `k(0)` as data. -/
theorem archTermQ_comb :
    Schema.archTermQ windowK =
      ((2 * kap0 * (Real.log (Real.sqrt 23 / (2 * Real.pi)) - Real.eulerMascheroniConstant) +
        2 * (11 / 6 * kap0 + archC0 + ∑ m ∈ Finset.range 16390, archCoef m * Real.log (m : ℝ)) : ℝ) : ℂ) := by
  rw [archTermQ_windowK, archJ_comb, windowK_zero_kap, windowKx_one_eq]
  push_cast <;> ring

/-- The coefficients of the pole term and the archimedean sums, joined at each `m < 16390`. -/
theorem comb_sum :
    ∑ m ∈ Finset.range 16390, combCoef m * Real.log m =
      2 * ((intHNum : ℝ) / (16 * 10 ^ coeffScale)) * ∑ m ∈ Finset.range 16385, poleCoef m * Real.log m +
        2 * ∑ m ∈ Finset.range 16390, archCoef m * Real.log (m : ℝ) := by
  have hp : ∑ m ∈ Finset.range 16385, poleCoef m * Real.log m = ∑ m ∈ Finset.range 16390, poleCoef m * Real.log m :=
    sum_range_pad 16385 16390 (by norm_num) _ (fun m hm => by
      show poleCoef m * Real.log m = 0
      rw [poleCoef_high m hm, zero_mul])
  unfold combCoef
  rw [hp, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- **L11c**: the real part of the arithmetic side at the window as the combination in the integers' form: a rational constant,
`log 23`, `log 2`, `log π` and Euler's constant times `k(0)`, a coefficient of each `log m`, `m < 16390`, and the prime-power side's
terms through `cQ n` and `Kt n`, `2 ≤ n < 1024`. -/
theorem arith_eq_comb :
    (B321.poleTerm windowK - Schema.primeTermQ Schema.ZQ.cQ windowK + Schema.archTermQ windowK).re =
      11 / 3 * kap0 + 2 * archC0 + kap0 * Real.log 23 - 2 * kap0 * Real.log 2 - 2 * kap0 * Real.log Real.pi -
        2 * kap0 * Real.eulerMascheroniConstant + ∑ m ∈ Finset.range 16390, combCoef m * Real.log m -
        ∑ n ∈ Finset.Ico 2 1024, 2 * Schema.ZQ.cQ n * ((Kt n : ℝ) / (80640 * (n : ℝ) ^ 4 * 10 ^ 34)) := by
  rw [poleTerm_comb, primeTermQ_comb, archTermQ_comb, ← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.ofReal_re,
    log_sqrt23, comb_sum]
  ring

end Window
end SIDEExplicitFormula
