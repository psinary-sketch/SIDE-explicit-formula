/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/ZQ/OffZero/Sums.lean
THIS PROGRAMME'S WORK (act b741, ruling (R351)(3)(b), relay data/b741_c7_plan.txt (2) (R-S), (5) G2) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

G2, RATIONAL DISCS AND THE EXACT SUMS. A rational complex number `qc (x, y) = x + y i`; a disc `inD z c r : ‖z − qc c‖ ≤ r` with `c` and `r`
rational; the disc moved by `+`, `−`, `·` and a count, each step's side condition a `ℚ` inequality the kernel decides; the series
`Σ_{k<n} (−X)^k/(k! (w + k))` at rational `X` and `w` equal to `qc (sRe, sIm)`, computed in `ℚ`; the exponential's partial sum at a rational
complex point equal to `qc (qexpS ..)`. No value is certified here and no zero is located.
-/
import SIDEExplicitFormula.Schema.ZQ.OffZero.Elem

namespace SIDEExplicitFormula
namespace Schema
namespace ZQ
namespace OffZero

/-- A rational complex number. -/
noncomputable def qc (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩

def qadd (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 + q.1, p.2 + q.2)

def qsub (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 - q.1, p.2 - q.2)

def qmul (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

def qscale (q : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (q * p.1, q * p.2)

/-- A rational bound of the norm: `|x| + |y|`. -/
def qn (p : ℚ × ℚ) : ℚ := |p.1| + |p.2|

theorem qc_re (p : ℚ × ℚ) : (qc p).re = p.1 := rfl

theorem qc_im (p : ℚ × ℚ) : (qc p).im = p.2 := rfl

theorem qc_add (p q : ℚ × ℚ) : qc (qadd p q) = qc p + qc q := by
  apply Complex.ext <;> simp [qc_re, qc_im, Complex.add_re, Complex.add_im, qadd]

theorem qc_sub (p q : ℚ × ℚ) : qc (qsub p q) = qc p - qc q := by
  apply Complex.ext <;> simp [qc_re, qc_im, Complex.sub_re, Complex.sub_im, qsub]

theorem qc_mul (p q : ℚ × ℚ) : qc (qmul p q) = qc p * qc q := by
  apply Complex.ext <;> simp [qc_re, qc_im, Complex.mul_re, Complex.mul_im, qmul]

theorem qc_scale (q : ℚ) (p : ℚ × ℚ) : qc (qscale q p) = ((q : ℝ) : ℂ) * qc p := by
  apply Complex.ext <;> simp [qc_re, qc_im, Complex.mul_re, Complex.mul_im, qscale]

theorem norm_qc_le (p : ℚ × ℚ) : ‖qc p‖ ≤ (qn p : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
  rw [qc_re, qc_im, qn, Rat.cast_add, Rat.cast_abs, Rat.cast_abs]

theorem qn_nonneg (p : ℚ × ℚ) : (0 : ℝ) ≤ (qn p : ℝ) := (norm_nonneg _).trans (norm_qc_le p)

/-- The disc: `‖z − qc c‖ ≤ r`. -/
def inD (z : ℂ) (c : ℚ × ℚ) (r : ℚ) : Prop := ‖z - qc c‖ ≤ (r : ℝ)

theorem inD_recentre {z : ℂ} {c₀ c : ℚ × ℚ} {r₀ r : ℚ} (h : inD z c₀ r₀) (hc : qn (qsub c₀ c) + r₀ ≤ r) : inD z c r := by
  unfold inD at *
  have hc' : ((qn (qsub c₀ c) + r₀ : ℚ) : ℝ) ≤ r := by exact_mod_cast hc
  push_cast at hc'
  have n3 := norm_qc_le (qsub c₀ c)
  rw [qc_sub] at n3
  have e : z - qc c = (z - qc c₀) + (qc c₀ - qc c) := by ring
  rw [e]
  have a1 := norm_add_le (z - qc c₀) (qc c₀ - qc c)
  linarith

theorem inD_add {z₁ z₂ : ℂ} {c₁ c₂ c : ℚ × ℚ} {r₁ r₂ r : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂)
    (hc : qn (qsub (qadd c₁ c₂) c) + r₁ + r₂ ≤ r) : inD (z₁ + z₂) c r := by
  unfold inD at *
  have hc' : ((qn (qsub (qadd c₁ c₂) c) + r₁ + r₂ : ℚ) : ℝ) ≤ r := by exact_mod_cast hc
  push_cast at hc'
  have n3 := norm_qc_le (qsub (qadd c₁ c₂) c)
  rw [qc_sub, qc_add] at n3
  have e : z₁ + z₂ - qc c = ((z₁ - qc c₁) + (z₂ - qc c₂)) + (qc c₁ + qc c₂ - qc c) := by ring
  rw [e]
  have a1 := norm_add_le ((z₁ - qc c₁) + (z₂ - qc c₂)) (qc c₁ + qc c₂ - qc c)
  have a2 := norm_add_le (z₁ - qc c₁) (z₂ - qc c₂)
  linarith

theorem inD_sub {z₁ z₂ : ℂ} {c₁ c₂ c : ℚ × ℚ} {r₁ r₂ r : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂)
    (hc : qn (qsub (qsub c₁ c₂) c) + r₁ + r₂ ≤ r) : inD (z₁ - z₂) c r := by
  unfold inD at *
  have hc' : ((qn (qsub (qsub c₁ c₂) c) + r₁ + r₂ : ℚ) : ℝ) ≤ r := by exact_mod_cast hc
  push_cast at hc'
  have n3 := norm_qc_le (qsub (qsub c₁ c₂) c)
  rw [qc_sub, qc_sub] at n3
  have e : z₁ - z₂ - qc c = ((z₁ - qc c₁) - (z₂ - qc c₂)) + (qc c₁ - qc c₂ - qc c) := by ring
  rw [e]
  have a1 := norm_add_le ((z₁ - qc c₁) - (z₂ - qc c₂)) (qc c₁ - qc c₂ - qc c)
  have a2 := norm_sub_le (z₁ - qc c₁) (z₂ - qc c₂)
  linarith

theorem inD_mul {z₁ z₂ : ℂ} {c₁ c₂ c : ℚ × ℚ} {r₁ r₂ r : ℚ} (h₁ : inD z₁ c₁ r₁) (h₂ : inD z₂ c₂ r₂)
    (hc : qn (qsub (qmul c₁ c₂) c) + qn c₁ * r₂ + qn c₂ * r₁ + r₁ * r₂ ≤ r) : inD (z₁ * z₂) c r := by
  unfold inD at *
  have hr₁ : (0 : ℝ) ≤ r₁ := (norm_nonneg _).trans h₁
  have hc' : ((qn (qsub (qmul c₁ c₂) c) + qn c₁ * r₂ + qn c₂ * r₁ + r₁ * r₂ : ℚ) : ℝ) ≤ r := by exact_mod_cast hc
  push_cast at hc'
  have n1 := norm_qc_le c₁
  have n2 := norm_qc_le c₂
  have n3 := norm_qc_le (qsub (qmul c₁ c₂) c)
  rw [qc_sub, qc_mul] at n3
  have e : z₁ * z₂ - qc c = ((z₁ - qc c₁) * (z₂ - qc c₂) + (z₁ - qc c₁) * qc c₂ + qc c₁ * (z₂ - qc c₂))
      + (qc c₁ * qc c₂ - qc c) := by ring
  rw [e]
  have a1 := norm_add_le ((z₁ - qc c₁) * (z₂ - qc c₂) + (z₁ - qc c₁) * qc c₂ + qc c₁ * (z₂ - qc c₂)) (qc c₁ * qc c₂ - qc c)
  have a2 := norm_add_le ((z₁ - qc c₁) * (z₂ - qc c₂) + (z₁ - qc c₁) * qc c₂) (qc c₁ * (z₂ - qc c₂))
  have a3 := norm_add_le ((z₁ - qc c₁) * (z₂ - qc c₂)) ((z₁ - qc c₁) * qc c₂)
  have m1 : ‖(z₁ - qc c₁) * (z₂ - qc c₂)‖ ≤ (r₁ : ℝ) * r₂ := by
    rw [norm_mul]; exact mul_le_mul h₁ h₂ (norm_nonneg _) hr₁
  have m2 : ‖(z₁ - qc c₁) * qc c₂‖ ≤ (r₁ : ℝ) * qn c₂ := by
    rw [norm_mul]; exact mul_le_mul h₁ n2 (norm_nonneg _) hr₁
  have m3 : ‖qc c₁ * (z₂ - qc c₂)‖ ≤ (qn c₁ : ℝ) * r₂ := by
    rw [norm_mul]; exact mul_le_mul n1 h₂ (norm_nonneg _) (qn_nonneg c₁)
  linarith

theorem inD_nat_mul {z : ℂ} {c₁ c : ℚ × ℚ} {r₁ r : ℚ} (n : ℕ) (h₁ : inD z c₁ r₁)
    (hc : qn (qsub (qscale n c₁) c) + n * r₁ ≤ r) : inD ((n : ℂ) * z) c r := by
  unfold inD at *
  have hc' : ((qn (qsub (qscale n c₁) c) + n * r₁ : ℚ) : ℝ) ≤ r := by exact_mod_cast hc
  push_cast at hc'
  have n3 := norm_qc_le (qsub (qscale n c₁) c)
  rw [qc_sub, qc_scale] at n3
  push_cast at n3
  have e : (n : ℂ) * z - qc c = (n : ℂ) * (z - qc c₁) + ((n : ℂ) * qc c₁ - qc c) := by ring
  rw [e]
  have a1 := norm_add_le ((n : ℂ) * (z - qc c₁)) ((n : ℂ) * qc c₁ - qc c)
  have m1 : ‖(n : ℂ) * (z - qc c₁)‖ ≤ (n : ℝ) * r₁ := by
    rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n)
  linarith

/-- The real part of `Σ_{k<n} (−r)^k/(k! (w + k))` at `w = wr + wi i`, in `ℚ`: exact. -/
def sRe (r wr wi : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sRe r wr wi n + (-r) ^ n / (n.factorial : ℚ) * ((wr + n) / ((wr + n) ^ 2 + wi ^ 2))

/-- The imaginary part, the same sum. -/
def sIm (r wr wi : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sIm r wr wi n - (-r) ^ n / (n.factorial : ℚ) * (wi / ((wr + n) ^ 2 + wi ^ 2))

/-- **(c7)** The series at rational `X` and `w = qc (wr, wi)`, `wr > 0`, is `qc (sRe, sIm)`. -/
theorem sum_eq_qc (X wr wi : ℚ) (hw : 0 < wr) (n : ℕ) :
    ∑ k ∈ Finset.range n, (((-(X : ℝ)) ^ k / k.factorial : ℝ) : ℂ) / (qc (wr, wi) + k)
      = qc (sRe X wr wi n, sIm X wr wi n) := by
  induction n with
  | zero => apply Complex.ext <;> simp [qc_re, qc_im, sRe, sIm]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hw' : (0 : ℝ) < wr := by exact_mod_cast hw
    have hk : (0 : ℝ) < (wr : ℝ) + n := by positivity
    have hD : ((wr : ℝ) + n) * ((wr : ℝ) + n) + (wi : ℝ) * wi ≠ 0 := by positivity
    have hD2 : ((wr : ℝ) + n) ^ 2 + (wi : ℝ) ^ 2 ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    apply Complex.ext
    · simp only [Complex.add_re, Complex.div_re, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, Complex.add_im, qc_re, qc_im, sRe]
      push_cast
      field_simp
      ring
    · simp only [Complex.add_im, Complex.div_im, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, Complex.add_re, qc_re, qc_im, sIm]
      push_cast
      field_simp
      ring

/-- `p^n` in `ℚ × ℚ`. -/
def qpow (p : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => qmul (qpow p n) p

/-- `Σ_{m<N} p^m/m!` in `ℚ × ℚ`. -/
def qexpS (p : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | n + 1 => qadd (qexpS p n) (qscale (1 / (n.factorial : ℚ)) (qpow p n))

theorem qc_pow (p : ℚ × ℚ) (n : ℕ) : qc (qpow p n) = qc p ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [qc_re, qc_im, qpow]
  | succ n ih => rw [qpow, qc_mul, ih, pow_succ]

theorem qc_expS (p : ℚ × ℚ) (N : ℕ) :
    qc (qexpS p N) = ∑ m ∈ Finset.range N, qc p ^ m / (m.factorial : ℂ) := by
  induction N with
  | zero => apply Complex.ext <;> simp [qc_re, qc_im, qexpS]
  | succ n ih =>
    rw [qexpS, qc_add, qc_scale, qc_pow, ih, Finset.sum_range_succ]
    push_cast
    ring

end OffZero
end ZQ
end Schema
end SIDEExplicitFormula
