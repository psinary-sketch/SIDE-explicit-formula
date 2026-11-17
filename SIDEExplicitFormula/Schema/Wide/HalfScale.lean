/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/Wide/HalfScale.lean
THIS PROGRAMME'S WORK (act b757, ruling (R367)(7), the one direction over the wider strip) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE ONE DIRECTION OVER THE WIDER STRIP. For a configuration of points in the strip `-1/2 < Re s < 3/2` (`WideConfig`, Config.lean
:28), closed under `s ↦ 1 - conj s` with equal multiplicities and with the local count bound, a point off the line `Re s = 1/2` gives a
test function in classK at which the sum over the configuration of the multiplicity times the transform has negative real part
(`wide_detector`). THE ROUTE, the ruling's: the map `s ↦ 1/2 + (s - 1/2)/2` (`halfMap`) carries the configuration into the open strip
`0 < Re s < 1`, keeping the line, the reflection and the multiplicities (`halfConfig`), and the count passes with the constant `4 A₀`
over two unit windows (`half_count`); the detector theorem (Schema/Detector.lean :99), called at that configuration with its own zero
sum standing as the formula's other side (`halfWeil`), gives a window `k`, and the dilate `x ↦ 2 k(2x)` (`dil`) stays in classK
(`dil_classK`, the convolution dilated in `dil_weilTest`) and carries the half-scale sum to the wide one term by term (`halfConfig_sum`,
the sum reindexed over the carrier). Nothing here proves RH or GRH or locates any zero; every statement is over an arbitrary
configuration, with a point off the line as a hypothesis.
-/
import SIDEExplicitFormula.Schema.Detector
import SIDEExplicitFormula.Schema.Wide.Config

open MeasureTheory

noncomputable section

namespace SIDEExplicitFormula
namespace Schema
namespace Wide

/-! ### The half-scale map -/

/-- The half-scale map `s ↦ 1/2 + (s - 1/2)/2`. -/
def halfMap (s : ℂ) : ℂ := 1 / 2 + (s - 1 / 2) / 2

/-- Its inverse `w ↦ 1/2 + 2 (w - 1/2)`. -/
def halfInv (w : ℂ) : ℂ := 1 / 2 + 2 * (w - 1 / 2)

theorem halfInv_halfMap (s : ℂ) : halfInv (halfMap s) = s := by
  unfold halfInv halfMap
  ring

theorem halfMap_injective : Function.Injective halfMap := fun a b h => by
  rw [← halfInv_halfMap a, h, halfInv_halfMap]

theorem halfMap_eq (s : ℂ) :
    halfMap s = ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * (s - ((1 / 2 : ℝ) : ℂ)) := by
  unfold halfMap
  push_cast
  ring

theorem halfMap_re (s : ℂ) : (halfMap s).re = 1 / 2 + 1 / 2 * (s.re - 1 / 2) := by
  rw [halfMap_eq]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]

theorem halfMap_im (s : ℂ) : (halfMap s).im = 1 / 2 * s.im := by
  rw [halfMap_eq]
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im, zero_add, sub_zero]

/-- The map keeps the reflection `s ↦ 1 - conj s`. -/
theorem halfMap_reflect (s : ℂ) : halfMap (Zeta23.reflect s) = Zeta23.reflect (halfMap s) := by
  unfold halfMap Zeta23.reflect
  first
    | (simp only [map_add, map_sub, map_div₀, map_one, map_ofNat]; ring)
    | (apply Complex.ext <;> simp [Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring)

/-- The map halves the ordinate `γ_ρ = (ρ - 1/2)/i`. -/
theorem gammaOf_halfMap (s : ℂ) : Zeta23.gammaOf (halfMap s) = Zeta23.gammaOf s / 2 := by
  unfold Zeta23.gammaOf halfMap
  ring

/-- The map keeps the line and the points off it. -/
theorem halfMap_re_ne {s : ℂ} (h : s.re ≠ 1 / 2) : (halfMap s).re ≠ 1 / 2 := by
  rw [halfMap_re]
  intro h'
  apply h
  linarith

/-! ### The half-scale configuration and its count -/

/-- **The half-scale configuration**: the image of a wide configuration under `halfMap`, a configuration of the schema's closed
strip (`Zeta23.ZeroConfig`), its multiplicities carried by `halfInv`. -/
def halfConfig (Z : WideConfig) : Zeta23.ZeroConfig where
  carrier := halfMap '' Z.carrier
  mult := fun w => Z.mult (halfInv w)
  one_le_mult := by
    rintro _ ⟨s, hs, rfl⟩
    show 1 ≤ Z.mult (halfInv (halfMap s))
    rw [halfInv_halfMap]
    exact Z.one_le_mult s hs
  strip := by
    rintro _ ⟨s, hs, rfl⟩
    have h := Z.strip s hs
    rw [halfMap_re]
    constructor <;> linarith [h.1, h.2]
  reflect_mem := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨Zeta23.reflect s, Z.reflect_mem s hs, halfMap_reflect s⟩
  mult_reflect := by
    rintro _ ⟨s, hs, rfl⟩
    show Z.mult (halfInv (Zeta23.reflect (halfMap s))) = Z.mult (halfInv (halfMap s))
    rw [← halfMap_reflect, halfInv_halfMap, halfInv_halfMap]
    exact Z.mult_reflect s hs
  finite_window := by
    intro T₁ T₂
    refine ((Z.finite_window (2 * T₁) (2 * T₂)).image halfMap).subset ?_
    rintro _ ⟨⟨s, hs, rfl⟩, hw⟩
    obtain ⟨h1', h2'⟩ := hw
    have h1 : T₁ < (halfMap s).im := h1'
    have h2 : (halfMap s).im ≤ T₂ := h2'
    rw [halfMap_im] at h1 h2
    exact ⟨s, ⟨hs, by linarith, by linarith⟩, rfl⟩

theorem halfMap_mem {Z : WideConfig} {s : ℂ} (hs : s ∈ Z.carrier) : halfMap s ∈ (halfConfig Z).carrier :=
  ⟨s, hs, rfl⟩

/-- A window of the half-scale configuration is the image of the wide window at twice the heights. -/
theorem halfConfig_window (Z : WideConfig) (T₁ T₂ : ℝ) :
    (halfConfig Z).window T₁ T₂ = halfMap '' Wide.window Z (2 * T₁) (2 * T₂) := by
  ext w
  simp only [Zeta23.ZeroConfig.window, Wide.window, halfConfig, Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, h1, h2⟩
    rw [halfMap_im] at h1 h2
    exact ⟨s, ⟨hs, by linarith, by linarith⟩, rfl⟩
  · rintro ⟨s, ⟨hs, h1, h2⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_, ?_⟩ <;> rw [halfMap_im] <;> linarith

/-- The count of the half-scale configuration over `(T₁, T₂]` is the wide count over `(2 T₁, 2 T₂]`. -/
theorem halfConfig_N (Z : WideConfig) (T₁ T₂ : ℝ) :
    (halfConfig Z).N T₁ T₂ = Wide.N Z (2 * T₁) (2 * T₂) := by
  unfold Zeta23.ZeroConfig.N Wide.N
  rw [halfConfig_window, finsum_mem_image halfMap_injective.injOn]
  refine finsum_mem_congr rfl fun s _ => ?_
  show Z.mult (halfInv (halfMap s)) = Z.mult s
  rw [halfInv_halfMap]

/-- A window of height two is two windows of height one. -/
theorem wide_N_two (Z : WideConfig) (t : ℝ) :
    Wide.N Z t (t + 2) = Wide.N Z t (t + 1) + Wide.N Z (t + 1) (t + 1 + 1) := by
  unfold Wide.N
  have hU : Wide.window Z t (t + 2) = Wide.window Z t (t + 1) ∪ Wide.window Z (t + 1) (t + 1 + 1) := by
    ext ρ
    simp only [Wide.window, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, h1, h2⟩
      by_cases hc : ρ.im ≤ t + 1
      · exact Or.inl ⟨h, h1, hc⟩
      · push_neg at hc
        exact Or.inr ⟨h, hc, by linarith⟩
    · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
      · exact ⟨h, h1, by linarith⟩
      · exact ⟨h, by linarith, by linarith⟩
  have hD : Disjoint (Wide.window Z t (t + 1)) (Wide.window Z (t + 1) (t + 1 + 1)) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, _, h2⟩ ⟨_, h1, _⟩
    linarith
  rw [hU, finsum_mem_union hD (Z.finite_window t (t + 1)) (Z.finite_window (t + 1) (t + 1 + 1))]

theorem sq_bound (t : ℝ) : 2 * |t| + 4 ≤ (|t| + 3) ^ 2 := by
  nlinarith [abs_nonneg t]

theorem log_le_two_log {x t : ℝ} (hx : 0 < x) (h : x ≤ 2 * |t| + 4) : Real.log x ≤ 2 * Real.log (|t| + 3) := by
  calc Real.log x ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log hx (h.trans (sq_bound t))
    _ = 2 * Real.log (|t| + 3) := by
      rw [Real.log_pow]
      norm_num

/-- **The count passes with a constant**: a wide local count `A₀` gives the half-scale configuration the local count `4 A₀`. -/
theorem half_count (Z : WideConfig) {A₀ : ℝ} (hc : Wide.HCount Z A₀) : B321.HCount (halfConfig Z) (4 * A₀) := by
  obtain ⟨hA, hN⟩ := hc
  refine ⟨by linarith, fun t => ?_⟩
  rw [halfConfig_N, show 2 * (t + 1) = 2 * t + 2 by ring, wide_N_two]
  push_cast
  have h1 := hN (2 * t)
  have h2 := hN (2 * t + 1)
  have l1 : Real.log (|2 * t| + 3) ≤ 2 * Real.log (|t| + 3) :=
    log_le_two_log (by positivity) (by rw [abs_mul, abs_two]; linarith)
  have l2 : Real.log (|2 * t + 1| + 3) ≤ 2 * Real.log (|t| + 3) := by
    have ha := abs_add_le (2 * t) 1
    rw [abs_mul, abs_two, abs_one] at ha
    exact log_le_two_log (by positivity) (by linarith)
  have hA0 : 0 ≤ A₀ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left l1 hA0, mul_le_mul_of_nonneg_left l2 hA0]

/-- **The half-scale configuration as a configuration of the schema**, its own zero sum standing as the formula's other side, so the
field `ef` holds by definition; the count is `half_count`. -/
def halfWeil (Z : WideConfig) {A₀ : ℝ} (hc : Wide.HCount Z A₀) : WeilConfig where
  toZeroConfig := halfConfig Z
  rhs := fun k => ∑' ρ : (halfConfig Z).carrier, ((halfConfig Z).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)
  ef := fun _ _ _ _ => rfl
  count := ⟨4 * A₀, half_count Z hc⟩
  target := ∀ ρ ∈ (halfConfig Z).carrier, ρ.re = 1 / 2
  target_iff := Iff.rfl

/-! ### The dilate -/

/-- The dilate `x ↦ 2 k(2x)`. -/
def dil (k : ℝ → ℂ) : ℝ → ℂ := fun x => 2 * k (2 * x)

/-- The transform of the dilate is the transform at half the argument. -/
theorem paperFT_dil (k : ℝ → ℂ) (z : ℂ) : Zeta23.paperFT (dil k) z = Zeta23.paperFT k (z / 2) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun v : ℝ => k v * Complex.exp (Complex.I * (z / 2) * (v : ℂ))) 2
  have e : (fun u : ℝ => dil k u * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u : ℝ => (2 : ℂ) * (k (2 * u) * Complex.exp (Complex.I * (z / 2) * ((2 * u : ℝ) : ℂ))) := by
    funext u
    have e2 : Complex.I * (z / 2) * ((2 * u : ℝ) : ℂ) = Complex.I * z * (u : ℂ) := by
      push_cast
      ring
    rw [e2, dil]
    ring
  show (∫ u : ℝ, dil k u * Complex.exp (Complex.I * z * (u : ℂ))) =
    ∫ u : ℝ, k u * Complex.exp (Complex.I * (z / 2) * (u : ℂ))
  rw [e, MeasureTheory.integral_const_mul, h, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul]
  push_cast
  ring

theorem dil_even {k : ℝ → ℂ} (he : ∀ x : ℝ, k (-x) = k x) : ∀ x : ℝ, dil k (-x) = dil k x := by
  intro x
  simp only [dil, mul_neg, he]

theorem dil_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) : ContDiff ℝ 2 (dil k) := by
  unfold dil
  first
    | exact contDiff_const.mul (hk.comp (contDiff_const.mul contDiff_id))
    | fun_prop

theorem dil_hasCompactSupport {k : ℝ → ℂ} (hs : HasCompactSupport k) : HasCompactSupport (dil k) := by
  have h1 : HasCompactSupport fun x : ℝ => k ((2 : ℝ) • x) := hs.comp_smul two_ne_zero
  have h2 : HasCompactSupport ((fun _ : ℝ => (2 : ℂ)) * fun x : ℝ => k ((2 : ℝ) • x)) := h1.mul_left
  convert h2 using 1
  funext x
  simp only [dil, Pi.mul_apply, smul_eq_mul]

/-- **The dilate of a convolution `h ⋆ h~` is the convolution of the dilates**: `2 (h ⋆ h~)(2x) = (h₂ ⋆ h₂~)(x)` with
`h₂(x) = 2 h(2x)`, by the change of variables `t = 2s`. -/
theorem dil_weilTest (h : ℝ → ℂ) : dil (Zeta23.EF.weilTest h h) = Zeta23.EF.weilTest (dil h) (dil h) := by
  funext x
  have hG := MeasureTheory.Measure.integral_comp_mul_left
    (fun s : ℝ => h s * (starRingEnd ℂ) (h (-(2 * x - s)))) 2
  have e : (fun t : ℝ => (ContinuousLinearMap.mul ℝ ℂ) (dil h t) (Zeta23.EF.tilde (dil h) (x - t))) =
      fun t : ℝ => (4 : ℂ) * (h (2 * t) * (starRingEnd ℂ) (h (-(2 * x - 2 * t)))) := by
    funext t
    simp only [ContinuousLinearMap.mul_apply', dil, Zeta23.EF.tilde, map_mul, map_ofNat]
    have e3 : 2 * -(x - t) = -(2 * x - 2 * t) := by ring
    rw [e3]
    ring
  show (2 : ℂ) * (∫ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (h t) (Zeta23.EF.tilde h (2 * x - t))) =
    ∫ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (dil h t) (Zeta23.EF.tilde (dil h) (x - t))
  rw [e, MeasureTheory.integral_const_mul, hG]
  simp only [Zeta23.EF.tilde, ContinuousLinearMap.mul_apply']
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul]
  push_cast
  ring

/-- **The dilate stays in classK.** -/
theorem dil_classK {k : ℝ → ℂ} (hk : B321.classK k) : B321.classK (dil k) := by
  obtain ⟨he, hc, hs, h, hh, hhs, rfl⟩ := hk
  exact ⟨dil_even he, dil_contDiff hc, dil_hasCompactSupport hs, dil h, dil_contDiff hh, dil_hasCompactSupport hhs,
    dil_weilTest h⟩

/-! ### The sum reindexed, and the direction -/

/-- **The sum reindexed over the carrier**: the half-scale zero sum at `k` is the wide zero sum at the dilate of `k`. -/
theorem halfConfig_sum (Z : WideConfig) (k : ℝ → ℂ) :
    (∑' w : (halfConfig Z).carrier, ((halfConfig Z).mult w : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf w)) =
      ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * Zeta23.paperFT (dil k) (Zeta23.gammaOf ρ) := by
  have key := (Equiv.Set.image halfMap Z.carrier halfMap_injective).tsum_eq
    (fun w : ↥(halfMap '' Z.carrier) => (Z.mult (halfInv w) : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf w))
  refine Eq.trans ?_ (Eq.trans key.symm (tsum_congr fun ρ => ?_))
  · rfl
  · show (Z.mult (halfInv (halfMap ρ)) : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf (halfMap ρ)) =
      (Z.mult ρ : ℂ) * Zeta23.paperFT (dil k) (Zeta23.gammaOf ρ)
    rw [halfInv_halfMap, gammaOf_halfMap, paperFT_dil]

/-- **THE ONE DIRECTION OVER THE WIDER STRIP**: for a configuration in the strip `-1/2 < Re s < 3/2`, closed under `s ↦ 1 - conj s`
with equal multiplicities and with the local count bound, a point `ρ₀` off the line gives a test function in classK at which the sum
over the configuration of the multiplicity times the transform has negative real part. -/
theorem wide_detector (Z : WideConfig) {A₀ : ℝ} (hc : Wide.HCount Z A₀) (ρ₀ : ℂ) (h₀ : ρ₀ ∈ Z.carrier)
    (hoff : ρ₀.re ≠ 1 / 2) :
    ∃ k : ℝ → ℂ, B321.classK k ∧
      (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)).re < 0 := by
  obtain ⟨a, j, hk, -, hneg⟩ := detector (halfWeil Z hc) (halfMap ρ₀) (halfMap_mem h₀) (halfMap_re_ne hoff)
  refine ⟨dil _, dil_classK hk, ?_⟩
  rw [← halfConfig_sum]
  exact hneg

end Wide
end Schema
end SIDEExplicitFormula
