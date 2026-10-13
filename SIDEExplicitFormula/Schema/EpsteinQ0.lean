/-
SIDE-explicit-formula -- SIDEExplicitFormula/Schema/EpsteinQ0.lean
THIS PROGRAMME'S WORK (act b663, ruling (R273)(2)-(5) and the author's word on its plan; W-ORD-EPSTEIN-ZQ, the schema's negative
control) -- NOT VENDORED.
SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE EPSTEIN CONFIGURATION AT Q0 ON NAMED PREMISES, built on b590's Schema/Epstein.lean (not edited). `Z_Q` is the Epstein zeta
function of the form `x² + xy + 6y²` of discriminant `−23` (relay data/b523_registration_2026-09-25.txt :62). Mathlib holds no
Epstein zeta function, so `Z_Q`'s zero configuration enters as an abstract `Z` with named premises: the bench's zero list below
height 150 (relay data/b326_epstein_zeros.json, 146 ordinates on the line; data/b326_offline.json, 17 zeros off it) entered as data
-- BANKED BY TWO AGREEING ROUTES IN MPMATH AT 119 DIGITS, NOT BALL-CERTIFIED --, its completeness below 150, a local count with a
named constant, and b590's `EpsteinPremises` (the explicit formula, T1-lit, cited; the count). Every premise is a Prop, stated, not
proved; open. `qE0` (the list's off-line index 0) is the dominant of the seventeen at every base read (relay data/b663_dominance.txt);
b590's `rhoE` (index 1) is not the dominant at its own base. The schema's equivalence, the detector and the rate theorem are read at
the instance. Nothing here is a statement about the zeros of any Epstein zeta function beyond the compiled statements' own words,
and nothing here is about ζ.
-/
import SIDEExplicitFormula.Schema.Epstein
import SIDEExplicitFormula.Schema.RateIndexCfg

noncomputable section

namespace SIDEExplicitFormula
namespace Schema

open B321

/-- **The bench's ordinates on the line** below 150, in order: relay data/b326_epstein_zeros.json, key "zeros", index 0 to 145,
`gamma_a` (equal to `gamma_b`). Banked, not ball-certified. -/
def q0OnLine : List ℝ :=
  [1.3088963261727018, 4.942192602661986, 7.015387962039135, 8.604026776354834, 10.494498784571489, 11.804403648219864,
   12.971841167426028, 14.630459532385498, 18.82849120037208, 19.3037306182431, 20.347919365154475, 21.88496711243777,
   22.763691863626132, 23.86932538165451, 25.158944056221856, 26.14213997898418, 26.63666711532874, 28.43642203584401,
   31.196117023329187, 32.127353298840504, 34.88746345731914, 36.0357670821827, 37.240679172478515, 37.64019947045226,
   38.800437028576255, 39.738261798341185, 40.70906511628699, 41.35092944636506, 42.57504356723937, 44.685576622516585,
   47.08359442035064, 48.68241187449463, 49.57734915137088, 50.54961354583805, 51.153847302286316, 52.114807884777996,
   53.01272101926699, 53.593020297341475, 54.78521014767601, 55.49355239157788, 56.334946563552506, 57.22660299654013,
   57.867021422326076, 58.811871069721214, 59.46973430809086, 60.742754817433514, 62.39714535919029, 65.2077015441912,
   65.88161918577158, 67.12939964748354, 67.70527194780026, 68.5457418091777, 69.22992034457084, 70.20157239866475,
   71.04454676867475, 71.49293224940716, 72.32844113926275, 73.27592892501612, 74.28025173228808, 76.38180327666099,
   77.04305026187615, 78.00406658881624, 78.91932773648523, 81.01015017499257, 81.91656857365459, 82.66207838467604,
   83.07199487430825, 83.83884728012849, 84.89106412864085, 85.42988556561816, 86.36735400287947, 86.78175469255821,
   87.8225381513231, 88.67221311851672, 90.38831511455949, 94.60430339895885, 95.0904445795078, 96.0214680678525,
   96.68705490751545, 97.25100884374945, 97.9880661609588, 98.80957199892175, 99.42583919848293, 100.43180099236287,
   101.00775215917875, 101.56795300959075, 102.46728457611023, 103.14957624199216, 103.84515120574639, 104.42378252420065,
   105.28348774870744, 106.13961249810833, 107.06569010883605, 109.09063684434612, 110.55743292197253, 111.61508125326839,
   112.45753718602705, 113.30791462487926, 113.66376618115221, 114.53146227606129, 115.21844822352136, 115.9430469389007,
   116.74384005638979, 117.03429635535814, 118.02498533717672, 118.80099408248246, 119.41107333421324, 120.39903916833038,
   120.57263301421834, 121.32598454930938, 122.21420485325427, 122.78908020538589, 123.64223307585875, 125.2205013986734,
   126.13172616973814, 128.33851989838809, 128.83923125492512, 129.778520796246, 130.44753715926564, 131.24287952234002,
   131.72006790039447, 132.38744392724954, 133.2186403668608, 133.97307149032554, 134.67780475734642, 134.97681179011457,
   135.63045268866153, 136.48222099540945, 138.16103520156602, 139.24234760384005, 139.83283063612944, 140.62410263471764,
   141.44403042148485, 142.05186702504284, 142.5314986676226, 143.22337920445722, 143.74313154039882, 144.63731430516154,
   145.68112655602258, 145.69612980010947, 146.65415599702908, 147.28184433907404, 147.79596240779966, 148.75671942703156,
   149.3427459748624, 149.7180075858455]

/-- **The bench's dominant off-line zero of `Z_Q`** below 150: relay data/b326_offline.json, key "zeros", index 0, `rho_a`
(equal to `rho_b`), `0.9532604747946607 + 16.290215720390393 i`. Banked, not ball-certified. The largest score of the seventeen at
every base read (relay data/b663_dominance.txt). -/
def qE0 : ℂ := ⟨0.9532604747946607, 16.290215720390393⟩

theorem qE0_re_ne_half : qE0.re ≠ 1 / 2 := by
  show (0.9532604747946607 : ℝ) ≠ 1 / 2
  norm_num

/-- **The bench's zeros off the line** below 150, `σ` in `[0.52, 1.5]`: relay data/b326_offline.json, key "zeros", index 0 to 16,
`rho_a` (equal to `rho_b`); index 0 is `qE0`, index 1 is b590's `rhoE` (Schema/Epstein.lean :32). Banked, not ball-certified. -/
def q0OffLine : List ℂ :=
  [qE0, rhoE, ⟨0.6636516788595986, 33.65010058252734⟩, ⟨0.8099915314971334, 43.85866436500448⟩,
   ⟨0.7823785766777296, 46.96099366990747⟩, ⟨0.8086599714776392, 61.68790376879195⟩, ⟨0.8498790995198219, 64.43482894033404⟩,
   ⟨0.7136405423571629, 75.08120418273509⟩, ⟨0.7957690258412357, 79.59854966493671⟩, ⟨0.7304981576021291, 89.5181059788535⟩,
   ⟨0.8117833479328327, 92.15177371885736⟩, ⟨0.6054364221857381, 93.08126840179203⟩, ⟨0.9515046579731146, 107.39929110192057⟩,
   ⟨0.8230214293761758, 110.19743296884323⟩, ⟨0.8394283849959813, 124.77543810003729⟩, ⟨0.6665341524713113, 127.62283672383899⟩,
   ⟨0.8743056607269751, 137.88555701699448⟩]

/-- The point `1/2 + iγ` of the critical line. -/
def onLinePt (γ : ℝ) : ℂ := ⟨1 / 2, γ⟩

/-- **The 360 listed points**: `1/2 ± iγ` for the 146 ordinates, and the orbit `ρ, 1 − ρ̄, ρ̄, 1 − ρ` of each of the 17 off-line
zeros (`Zeta23.reflect ρ = 1 − ρ̄`, Zeta23/Defs.lean :124). -/
def q0Points : Set ℂ :=
  {ρ | (∃ γ ∈ q0OnLine, ρ = onLinePt γ ∨ ρ = onLinePt (-γ)) ∨
    ∃ r ∈ q0OffLine, ρ = r ∨ ρ = Zeta23.reflect r ∨ ρ = starRingEnd ℂ r ∨ ρ = Zeta23.reflect (starRingEnd ℂ r)}

theorem qE0_mem : qE0 ∈ q0Points := by
  rw [q0Points, Set.mem_setOf_eq]
  exact Or.inr ⟨qE0, by simp [q0OffLine], Or.inl rfl⟩

theorem rhoE_mem : rhoE ∈ q0Points := by
  rw [q0Points, Set.mem_setOf_eq]
  exact Or.inr ⟨rhoE, by simp [q0OffLine], Or.inl rfl⟩

/-- **(P1) THE BANKED LIST IS IN THE CONFIGURATION** -- stated, not proved; open. Every listed point is a point of `Z` with
multiplicity 1: T3, the bench's list (relay data/b326_epstein_zeros.json, data/b326_offline.json), banked, not ball-certified. -/
def Q0Listed (Z : Zeta23.ZeroConfig) : Prop := ∀ ρ ∈ q0Points, ρ ∈ Z.carrier ∧ Z.mult ρ = 1

/-- **(P2) THE LIST IS COMPLETE BELOW 150** -- stated, not proved; open. Every point of `Z` with `|Im ρ| < 150` is listed. This
includes the band `|Im ρ| < 0.5` and `Re ρ` in `(1/2, 0.52)`, which neither census of b326 reads (both start at `t = 0.5`; the
off-line census at `σ = 0.52`): T3, the bench's census, with those two regions unread. -/
def Q0Complete (Z : Zeta23.ZeroConfig) : Prop := ∀ ρ ∈ Z.carrier, |ρ.im| < 150 → ρ ∈ q0Points

/-- The local count's constant: 10, a round margin above the listed points' own value 1 (relay data/b663_a0_list.txt) for the
unlisted points above 150. No source line; its reason is that bank. -/
def A0Q : ℝ := 10

/-- **(P3) THE LOCAL COUNT WITH A NUMBER** -- stated, not proved; open. `HCount Z A0Q` (RestBound.lean :44-:45): T3 below 150,
T4 above it. -/
def Q0Count (Z : Zeta23.ZeroConfig) : Prop := HCount Z A0Q

/-- **THE Q0 PREMISES**: (P1)-(P3) and (P4) b590's `EpsteinPremises` (the explicit formula, T1-lit, cited; the count) -- each
stated, not proved; open. -/
structure Q0Premises (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) : Prop where
  listed : Q0Listed Z
  complete : Q0Complete Z
  count : Q0Count Z
  epstein : EpsteinPremises Z rhs

/-- **The Q0 configuration**: b590's `epsteinConfig` (Schema/Epstein.lean :47) under the Q0 premises; the target the strip form. -/
def q0Config (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) : WeilConfig :=
  epsteinConfig Z rhs hP.epstein

/-- **The target is false at Q0**: the listed off-line `qE0` is a point of the configuration (P1). -/
theorem q0_target_false (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    ¬ (q0Config Z rhs hP).target := by
  intro h
  have h' : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := h
  exact qE0_re_ne_half (h' qE0 (hP.listed qE0 qE0_mem).1)

/-- **The schema's equivalence at Q0**, one application of `h2_sign_cfg_iff_target` (Schema/Converse.lean :265). -/
theorem q0_h2_iff_target (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    h2_sign_cfg (q0Config Z rhs hP) ↔ (q0Config Z rhs hP).target :=
  h2_sign_cfg_iff_target (q0Config Z rhs hP)

/-- **Not Weil-positive at Q0**, through the detector at the dominant `qE0`. -/
theorem q0_not_h2_sign_cfg (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    ¬ h2_sign_cfg (q0Config Z rhs hP) :=
  not_h2_sign_cfg_of_offline (q0Config Z rhs hP) qE0 (hP.listed qE0 qE0_mem).1 qE0_re_ne_half

/-- **b590's negative control read at Q0**: `epstein_not_h2_sign_cfg` at `rhoE`, its membership from (P1). -/
theorem q0_not_h2_sign_cfg_rhoE (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    ¬ h2_sign_cfg (q0Config Z rhs hP) :=
  epstein_not_h2_sign_cfg Z rhs hP.epstein (hP.listed rhoE rhoE_mem).1

/-- **The detector read at Q0** (Schema/Detector.lean :99), at the dominant `qE0`: the named window, its base half-width
`baseWidth qE0`, its zero side negative. -/
theorem q0_detector (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    ∃ (a : List ℝ) (j : ℕ), classK (kWindow a (detectorBase qE0) j) ∧
      Function.support (pwWindow a (detectorBase qE0) j) ⊆ Set.Icc (-(2 ^ j * baseWidth qE0)) (2 ^ j * baseWidth qE0) ∧
      (zeroSide_cfg (q0Config Z rhs hP) (kWindow a (detectorBase qE0) j)).re < 0 :=
  detector (q0Config Z rhs hP) qE0 (hP.listed qE0 qE0_mem).1 qE0_re_ne_half

/-- **The local count binds at Q0**: `hA` of the rate theorem at `A₀ := A0Q`, from (P3). -/
theorem q0_hA (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) :
    HCount (q0Config Z rhs hP).toZeroConfig A0Q :=
  hP.count

/-- **The rate theorem read at Q0**: `zeroSide_neg_at_rate_cfg` (Schema/RateIndexCfg.lean :135-:148) at `C := q0Config`, its
`A₀ := A0Q` and `hA` from (P3); the other binders are the theorem's own, certified by arithmetic outside the kernel (relay
data/b663_epstein_control.txt), not compiled. -/
theorem q0_rate (Z : Zeta23.ZeroConfig) (rhs : (ℝ → ℂ) → ℂ) (hP : Q0Premises Z rhs) {g0 : ℝ → ℝ} {L M : ℝ}
    (H : PWSetup (q0Config Z rhs hP).toZeroConfig g0 L M)
    (Q : ℕ → Polynomial ℝ) (B : ℝ) (D : ℕ)
    (hQtie : ∀ j, ∀ ρ ∈ tieSet (q0Config Z rhs hP).toZeroConfig g0 M,
      (Polynomial.aeval (vOf ρ) (Q j)) ^ 2 * Xval H j ρ = -(‖Xval H j ρ‖ : ℂ))
    (hQb : ∀ j (w : ℂ), ‖Polynomial.aeval w (Pof H (Q j))‖ ≤ B * (1 + ‖w‖) ^ D)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ ρ ∈ (q0Config Z rhs hP).toZeroConfig.carrier, ρ ∉ tieSet (q0Config Z rhs hP).toZeroConfig g0 M →
      ρ ∉ killSet (q0Config Z rhs hP).toZeroConfig g0 M → offScore g0 ρ / M ≤ θ)
    (j : ℕ) (hj : D ≤ j)
    (hrate : θ ^ (2 ^ (j + 1) - 2 ^ (D + 1)) *
        (3 * A0Q * (128 * 8 ^ D * B ^ 2 * (Aw H / M) ^ (2 ^ (D + 1))) * zeta3Sum) <
      ∑ x ∈ sT_cfg H, ((q0Config Z rhs hP).toZeroConfig.mult x : ℝ) * Nf H x) :
    (zeroSide_cfg (q0Config Z rhs hP) (kWindow (coeffList (Pof H (Q j))) g0 j)).re < 0 :=
  zeroSide_neg_at_rate_cfg H Q B D hQtie hQb θ hθ0 hθ A0Q (q0_hA Z rhs hP) j hj hrate

end Schema
end SIDEExplicitFormula
