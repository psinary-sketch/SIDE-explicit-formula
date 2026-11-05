/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/GammaVal.lean
THIS PROGRAMME'S WORK (act b741, ruling (R351)(3)(b), relay data/b741_c7_plan.txt (5) G3) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G3, THE DISCS FOR EACH PIECE. Exact disc steps (`+`, `−`, `·`, a count, a power, a near point); `lam` between two rationals from `π` to
twenty digits and `√23` to twenty-four; the lower piece's disc at a rational `X` from the series; `Γ(w)/X^w` at `X ≥ 41` from the lower
piece and the upper piece's `e^(−X)/X`; `2^w` from its exponential series at `w log 2/16`, `log 2` to ten digits; each shell
`incGamma1 w ρ = (2^w)^j Γ(w)/(2^j ρ)^w − lowInt w ρ`; the move from `ρ` to `lam Q` by the Lipschitz bound. No value is certified here and
no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Series
import SIDEExplicitFormula.Schema.ZQ.OffZero.Sums
import SIDEExplicitFormula.Schema.ZQ.OffZero.Shells

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

theorem qc_one : qc (1, 0) = 1 := by
  apply Complex.ext <;> simp [qc_re, qc_im]

theorem inD_add' {z₁ z₂ : ℂ} {c₁ c₂ : ℚ × ℚ} {r₁ r₂ : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂) :
    inD (z₁ + z₂) (qadd c₁ c₂) (r₁ + r₂) :=
  inD_add h₁ h₂ (by simp [qsub, qn])

theorem inD_sub' {z₁ z₂ : ℂ} {c₁ c₂ : ℚ × ℚ} {r₁ r₂ : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂) :
    inD (z₁ - z₂) (qsub c₁ c₂) (r₁ + r₂) :=
  inD_sub h₁ h₂ (by simp [qsub, qn])

theorem inD_mul' {z₁ z₂ : ℂ} {c₁ c₂ : ℚ × ℚ} {r₁ r₂ : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂) :
    inD (z₁ * z₂) (qmul c₁ c₂) (qn c₁ * r₂ + qn c₂ * r₁ + r₁ * r₂) :=
  inD_mul h₁ h₂ (by simp [qsub, qn])

theorem inD_nat_mul' {z : ℂ} {c : ℚ × ℚ} {r : ℚ} (n : ℕ) (h : inD z c r) : inD ((n : ℂ) * z) (qscale n c) (n * r) :=
  inD_nat_mul n h (by simp [qsub, qn])

/-- A point near a disc's point is in the widened disc. -/
theorem inD_near {z z' : ℂ} {c : ℚ × ℚ} {r e : ℚ} (h : inD z c r) (h' : ‖z' - z‖ ≤ (e : ℝ)) : inD z' c (r + e) := by
  unfold inD at *
  push_cast
  have hz : z' - qc c = (z' - z) + (z - qc c) := by ring
  rw [hz]
  linarith [norm_add_le (z' - z) (z - qc c)]

/-- The disc's power: centre `c^n`, radius `(|c| + r)^n − |c|^n`. -/
theorem inD_pow {z : ℂ} {c : ℚ × ℚ} {r : ℚ} (h : inD z c r) (n : ℕ) :
    inD (z ^ n) (qpow c n) ((qn c + r) ^ n - qn c ^ n) := by
  unfold inD at *
  have hr : (0 : ℝ) ≤ r := (norm_nonneg _).trans h
  have hA := norm_qc_le c
  have hA0 := qn_nonneg c
  have hz : ‖z‖ ≤ (qn c : ℝ) + r := by
    have := norm_sub_norm_le z (qc c)
    linarith
  induction n with
  | zero => simp [qpow, qc_one]
  | succ n ih =>
    rw [qc_pow] at ih
    push_cast at ih ⊢
    rw [qpow, qc_mul, qc_pow]
    have hC : ‖qc c ^ n‖ ≤ (qn c : ℝ) ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hA n
    have hB : (0 : ℝ) ≤ ((qn c : ℝ) + r) ^ n - (qn c : ℝ) ^ n :=
      sub_nonneg.mpr (pow_le_pow_left₀ hA0 (by linarith) n)
    calc ‖z ^ (n + 1) - qc c ^ n * qc c‖ = ‖(z ^ n - qc c ^ n) * z + qc c ^ n * (z - qc c)‖ := by
          congr 1
          ring
      _ ≤ ‖z ^ n - qc c ^ n‖ * ‖z‖ + ‖qc c ^ n‖ * ‖z - qc c‖ := by
          rw [← norm_mul, ← norm_mul]
          exact norm_add_le _ _
      _ ≤ (((qn c : ℝ) + r) ^ n - (qn c : ℝ) ^ n) * ((qn c : ℝ) + r) + (qn c : ℝ) ^ n * r :=
          add_le_add (mul_le_mul ih hz (norm_nonneg _) hB) (mul_le_mul hC h (norm_nonneg _) (pow_nonneg hA0 n))
      _ = ((qn c : ℝ) + r) ^ (n + 1) - (qn c : ℝ) ^ (n + 1) := by ring

/-- `lam` from below: `π > 3.14159265358979323846`, `√23 < S_HI`. -/
def lamLo : ℚ := 6550673513692863886337 / 5000000000000000000000

/-- `lam` from above: `π < 3.14159265358979323847`, `√23 > S_LO`. -/
def lamHi : ℚ := 3275336756846431943179 / 2500000000000000000000

theorem lam_lo : (lamLo : ℝ) ≤ lam := by
  have hs : Real.sqrt 23 < 4795831523312719541597439 / 1000000000000000000000000 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hp := Real.pi_gt_d20
  have hpos := sqrt23_pos
  have h1 : (6550673513692863886337 / 5000000000000000000000 : ℝ) * Real.sqrt 23
      ≤ 6550673513692863886337 / 5000000000000000000000 * (4795831523312719541597439 / 1000000000000000000000000) :=
    mul_le_mul_of_nonneg_left hs.le (by norm_num)
  unfold lamLo lam
  push_cast
  rw [le_div_iff₀ hpos]
  linarith

theorem lam_hi : lam ≤ (lamHi : ℝ) := by
  have hs : (2397915761656359770798719 / 500000000000000000000000 : ℝ) < Real.sqrt 23 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hp := Real.pi_lt_d20
  have hpos := sqrt23_pos
  have h1 : (3275336756846431943179 / 2500000000000000000000 : ℝ) * (2397915761656359770798719 / 500000000000000000000000)
      ≤ 3275336756846431943179 / 2500000000000000000000 * Real.sqrt 23 :=
    mul_le_mul_of_nonneg_left hs.le (by norm_num)
  unfold lamHi lam
  push_cast
  rw [div_le_iff₀ hpos]
  linarith

/-- The lower piece's disc at rational `X`: the exact series and its remainder. -/
theorem lowInt_encl (w : ℚ × ℚ) (hw : 0 < w.1) {X : ℚ} (hX : 0 ≤ X) (n : ℕ) (hn : 2 * X ≤ n + 1) :
    inD (lowInt (qc w) X) (sRe X w.1 w.2 n, sIm X w.1 w.2 n) (2 * X ^ n / (n.factorial * (w.1 + n))) := by
  obtain ⟨wr, wi⟩ := w
  dsimp only at hw ⊢
  unfold inD
  rw [← sum_eq_qc X wr wi hw n]
  have h := lowInt_sub_sum_le (w := qc (wr, wi)) (by rw [qc_re]; exact_mod_cast hw) (a := (X : ℝ)) (by exact_mod_cast hX)
    (n := n) (by exact_mod_cast hn)
  refine h.trans (le_of_eq ?_)
  simp only [qc_re]
  push_cast <;> ring

theorem norm_incGamma1_X {w : ℂ} (hw : w.re ≤ 1) {X : ℝ} (hX : 41 ≤ X) : ‖incGamma1 w X‖ ≤ 1 / 10 ^ 19 := by
  have h41 : Real.exp (-41) ≤ 1 / (271828 / 100000) ^ 41 := by
    have h := exp_neg_nat_le 41
    push_cast at h
    exact h
  calc ‖incGamma1 w X‖ ≤ Real.exp (-X) / X := norm_incGamma1_le hw (by linarith)
    _ ≤ Real.exp (-41) / 41 := div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) (by norm_num) hX
    _ ≤ (1 / (271828 / 100000) ^ 41) / 41 := by gcongr
    _ ≤ 1 / 10 ^ 19 := by norm_num

/-- `Γ(w)/a^w`. -/
def Gfac (w : ℂ) (a : ℝ) : ℂ := (1 / (a : ℂ)) ^ w * Complex.Gamma w

/-- `Γ(w)/X^w` at rational `X ≥ 41`: the lower piece's series plus `1e-19` for the upper piece. -/
theorem GX_encl (w : ℚ × ℚ) (hw : 0 < w.1) (hw1 : w.1 ≤ 1) {X : ℚ} (hX : 41 ≤ X) (n : ℕ) (hn : 2 * X ≤ n + 1) {c : ℚ × ℚ}
    {r : ℚ} (hc : qn (qsub (sRe X w.1 w.2 n, sIm X w.1 w.2 n) c) + 2 * X ^ n / (n.factorial * (w.1 + n)) + 1 / 10 ^ 19 ≤ r) :
    inD (Gfac (qc w) X) c r := by
  have hX' : (41 : ℝ) ≤ X := by exact_mod_cast hX
  have hl := inD_recentre (lowInt_encl w hw (by linarith) n hn) (c := c) le_rfl
  have hI : ‖incGamma1 (qc w) X‖ ≤ ((1 / 10 ^ 19 : ℚ) : ℝ) := by
    have h := norm_incGamma1_X (w := qc w) (by rw [qc_re]; exact_mod_cast hw1) hX'
    exact_mod_cast h
  unfold Gfac
  have hX0 : (0 : ℝ) < X := by linarith
  rw [Gamma_split (w := qc w) (a := (X : ℝ)) (by rw [qc_re]; exact_mod_cast hw) hX0]
  unfold inD at *
  have e : lowInt (qc w) X + incGamma1 (qc w) X - qc c = (lowInt (qc w) X - qc c) + incGamma1 (qc w) X := by ring
  rw [e]
  have hc' : (((qn (qsub (sRe X w.1 w.2 n, sIm X w.1 w.2 n) c) + 2 * X ^ n / (n.factorial * (w.1 + n)) : ℚ)) : ℝ)
      + ((1 / 10 ^ 19 : ℚ) : ℝ) ≤ r := by
    rw [← Rat.cast_add]
    exact_mod_cast hc
  exact (norm_add_le _ _).trans ((add_le_add hl hI).trans hc')

/-- Each shell through `X = 2^j ρ`: `incGamma1 w ρ = (2^w)^j Γ(w)/X^w − lowInt w ρ`. -/
theorem incGamma1_split {w : ℂ} (hw : 0 < w.re) {ρ X : ℚ} (hρ : 0 < ρ) (j : ℕ) (hX : X = 2 ^ j * ρ) :
    incGamma1 w ρ = ((2 : ℂ) ^ w) ^ j * Gfac w X - lowInt w ρ := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hX' : (X : ℝ) = 2 ^ j * ρ := by exact_mod_cast hX
  have h1 := Gamma_split hw hρ'
  have h2 := one_div_cpow_two_pow hρ' w j
  have e1 : (1 / ((ρ : ℝ) : ℂ)) = (((1 / (ρ : ℝ)) : ℝ) : ℂ) := by
    push_cast <;> ring
  have e2 : (1 / ((X : ℝ) : ℂ)) = (((1 / (2 ^ j * (ρ : ℝ))) : ℝ) : ℂ) := by
    rw [hX']
    push_cast <;> ring
  unfold Gfac
  rw [e2, ← mul_assoc, ← h2, ← e1, h1]
  ring

/-- `exp` at a rational complex point of norm at most one: the partial sum and `exp_bound`'s remainder. -/
theorem exp_encl (p : ℚ × ℚ) (hp : qn p ≤ 1) (N : ℕ) (hN : 0 < N) :
    inD (Complex.exp (qc p)) (qexpS p N) (qn p ^ N * ((N + 1) / (N.factorial * N))) := by
  unfold inD
  rw [qc_expS]
  have hx : ‖qc p‖ ≤ 1 := (norm_qc_le p).trans (by exact_mod_cast hp)
  refine (Complex.exp_bound hx hN).trans ?_
  have h1 : ‖qc p‖ ^ N ≤ (qn p : ℝ) ^ N := pow_le_pow_left₀ (norm_nonneg _) (norm_qc_le p) N
  calc ‖qc p‖ ^ N * ((N.succ : ℝ) * (N.factorial * N : ℝ)⁻¹)
      ≤ (qn p : ℝ) ^ N * ((N.succ : ℝ) * (N.factorial * N : ℝ)⁻¹) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by push_cast <;> ring

/-- `log 2` to ten digits (`Real.log_two_near_10`). -/
def L2 : ℚ := 287209 / 414355

theorem two_cpow_eq (w : ℚ × ℚ) :
    (2 : ℂ) ^ qc w = Complex.exp (qc (qscale (L2 / 16) w)) ^ 16 * Complex.exp (((Real.log 2 - (L2 : ℝ) : ℝ) : ℂ) * qc w) := by
  have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] <;> norm_num
  rw [qc_scale, Complex.cpow_def_of_ne_zero two_ne_zero, hl, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The correction `exp((log 2 − L2) w)` within `2 · 1e-10 · |w|` of `1`. -/
theorem corr_encl (w : ℚ × ℚ) (hd : qn w ≤ 10 ^ 10) :
    inD (Complex.exp (((Real.log 2 - (L2 : ℝ) : ℝ) : ℂ) * qc w)) (1, 0) (2 * qn w / 10 ^ 10) := by
  unfold inD
  rw [qc_one]
  have hL : |Real.log 2 - (L2 : ℝ)| ≤ 1 / 10 ^ 10 := by
    have h := Real.log_two_near_10
    unfold L2
    exact_mod_cast h
  have hq := norm_qc_le w
  have hd' : (qn w : ℝ) ≤ 10 ^ 10 := by exact_mod_cast hd
  have hx : ‖(((Real.log 2 - (L2 : ℝ) : ℝ) : ℂ) * qc w)‖ ≤ 1 / 10 ^ 10 * qn w := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hL hq (norm_nonneg _) (by norm_num)
  have hx1 : ‖(((Real.log 2 - (L2 : ℝ) : ℝ) : ℂ) * qc w)‖ ≤ 1 := by
    refine hx.trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact hd'
  have hr : ((2 * qn w / 10 ^ 10 : ℚ) : ℝ) = 2 * (qn w : ℝ) / 10 ^ 10 := by
    push_cast <;> ring
  rw [hr]
  refine (Complex.norm_exp_sub_one_le hx1).trans ?_
  linarith

def tpP (w : ℚ × ℚ) : ℚ × ℚ := qscale (L2 / 16) w

def tpE (w : ℚ × ℚ) (N : ℕ) : ℚ × ℚ := qexpS (tpP w) N

def tpR (w : ℚ × ℚ) (N : ℕ) : ℚ := qn (tpP w) ^ N * ((N + 1) / (N.factorial * N))

def tpC (w : ℚ × ℚ) (N : ℕ) : ℚ × ℚ := qpow (tpE w N) 16

def tpR16 (w : ℚ × ℚ) (N : ℕ) : ℚ := (qn (tpE w N) + tpR w N) ^ 16 - qn (tpE w N) ^ 16

def tpD (w : ℚ × ℚ) : ℚ := 2 * qn w / 10 ^ 10

/-- `2^w` at rational `w`: `exp(L2 w/16)^16 · exp((log 2 − L2) w)`, the side condition one `ℚ` inequality. -/
theorem two_cpow_encl (w : ℚ × ℚ) (N : ℕ) (hN : 0 < N) (hp : qn (tpP w) ≤ 1) (hd : qn w ≤ 10 ^ 10) {c : ℚ × ℚ} {r : ℚ}
    (hc : qn (qsub (qmul (tpC w N) (1, 0)) c) + qn (tpC w N) * tpD w + qn (1, 0) * tpR16 w N + tpR16 w N * tpD w ≤ r) :
    inD ((2 : ℂ) ^ qc w) c r := by
  have h1 : inD (Complex.exp (qc (tpP w))) (tpE w N) (tpR w N) := exp_encl (tpP w) hp N hN
  have h2 := inD_pow h1 16
  have h3 : inD (Complex.exp (((Real.log 2 - (L2 : ℝ) : ℝ) : ℂ) * qc w)) (1, 0) (tpD w) := corr_encl w hd
  rw [two_cpow_eq]
  exact inD_mul h2 h3 hc

/-- The move from `ρ` to `lam Q`: `|lam Q − ρ| ≤ d` by `lamLo`, `lamHi`; the Lipschitz bound at `m = 13/10` costs `d · 10/3`. -/
theorem inD_transfer {w : ℂ} (hw : w.re ≤ 1) {q : ℝ} {Q ρ d : ℚ} (hq : q = Q) (hQ : 1 ≤ Q) (h13 : 13 / 10 ≤ ρ)
    (hlo : ρ - d ≤ Q * lamLo) (hhi : Q * lamHi ≤ ρ + d) {c : ℚ × ℚ} {r r' : ℚ} (h : inD (incGamma1 w ρ) c r)
    (hr : r + d * (10 / 3) ≤ r') : inD (incGamma1 w (lam * q)) c r' := by
  subst hq
  have hl1 := lam_lo
  have hl2 := lam_hi
  have hg := lam_gt
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlo' : (ρ : ℝ) - d ≤ Q * lamLo := by exact_mod_cast hlo
  have hhi' : (Q : ℝ) * lamHi ≤ ρ + d := by exact_mod_cast hhi
  have h13' : (13 / 10 : ℝ) ≤ ρ := by exact_mod_cast h13
  have hr' : (r : ℝ) + d * (10 / 3) ≤ r' := by exact_mod_cast hr
  have hab : |lam * Q - ρ| ≤ d := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl1 (by linarith : (0 : ℝ) ≤ Q),
      mul_le_mul_of_nonneg_left hl2 (by linarith : (0 : ℝ) ≤ Q)]
  have hm : (13 / 10 : ℝ) ≤ lam * Q := by nlinarith [mul_le_mul_of_nonneg_left hQ' lam_pos.le]
  have hL := incGamma1_sub_le hw (m := 13 / 10) (by norm_num) hm h13'
  rw [show (13 / 10 : ℝ) - 1 = 3 / 10 by norm_num] at hL
  have he : Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10)) ≤ 10 / 3 := by
    have a1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have a2 : Real.exp (-(3 / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    calc Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10)) ≤ 1 * (1 / (3 / 10)) :=
          mul_le_mul a1 (by gcongr) (by positivity) (by norm_num)
      _ = 10 / 3 := by norm_num
  have hd0 : (0 : ℝ) ≤ d := (abs_nonneg _).trans hab
  unfold inD at *
  have e : incGamma1 w (lam * Q) - qc c = (incGamma1 w (lam * Q) - incGamma1 w ρ) + (incGamma1 w ρ - qc c) := by ring
  rw [e]
  have hT : ‖incGamma1 w (lam * Q) - incGamma1 w ρ‖ ≤ d * (10 / 3) := by
    refine hL.trans ?_
    calc |lam * Q - ρ| * Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10))
        = |lam * Q - ρ| * (Real.exp (-1) * (Real.exp (-(3 / 10)) / (3 / 10))) := by ring
      _ ≤ d * (10 / 3) := mul_le_mul hab he (by positivity) hd0
  linarith [norm_add_le (incGamma1 w (lam * Q) - incGamma1 w ρ) (incGamma1 w ρ - qc c)]

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
