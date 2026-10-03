/-
SIDE-explicit-formula -- SIDEExplicitFormula/KeiperBounds.lean
THIS PROGRAMME'S WORK (act b601, ruling (R211)(4); W-ORD-KEIPER-FACE, OPEN_TRAILS :11704, re-priced at :12132) -- NOT
VENDORED. SPIRAL_MAP section 7 rule 9 applies here in full: `theorem`, never `lemma`.

THE WORK-ORDER'S LEMMA (2), COMPUTABLE TWO-SIDED BOUNDS FOR THE CONSTANTS THE KEIPER SUM CONSUMES, AS A PROP, CARRIED TO
NAMED PREMISES. The constants are the Stieltjes constants `Keiper.stieltjes n` for `n ≤ 11` and the zeta values
`riemannZeta j` for `2 ≤ j ≤ 12` (the polygamma values at 1/2, through `Keiper.GammaRZetaValues`). The table is rational,
read from the bench (mpmath at 60 digits, each value rounded outward at 10⁻³⁰); it is data, not a claim, until a premise or
a proof meets it. `KeiperBounds` is the Prop that every constant lies in its interval with zero imaginary part.

* CARRIED (`keiperBounds_of`, at INTERFACES on `BoundPremises`): Euler's γ to the table's width, every Stieltjes constant
  from the first to the eleventh, and the eleven zeta values are NAMED PREMISES -- Mathlib at the pin holds no Stieltjes
  constant beyond γ by name and no bound on any odd zeta value, and nothing here assumes one.
* CLOSED (`stieltjes_zero_coarse`): γ_0 = γ lies in (1/2, 2/3) with zero imaginary part, by Mathlib's
  `one_half_lt_eulerMascheroniConstant` and `eulerMascheroniConstant_lt_two_thirds`; the table's interval at 0 refines it
  (`table_refines_coarse`). Mathlib's interval is too wide to fix the sign of λ_1 = 1 + γ/2 − ½ log 4π.

Nothing here is a statement about the zeros of ζ, or proves any sign of any λ_n.
-/
import SIDEExplicitFormula.Keiper

open Complex

noncomputable section

namespace SIDEExplicitFormula
namespace KeiperBounds

open Keiper

/-- A complex number in a rational interval, on the real line. -/
def InInterval (lo hi : ℚ) (x : ℂ) : Prop := (lo : ℝ) ≤ x.re ∧ x.re ≤ (hi : ℝ) ∧ x.im = 0

/-- The table's lower bounds for γ_0, …, γ_11 (the bench, rounded down at 10⁻³⁰). -/
def stLo : ℕ → ℚ
  | 0 => (577215664901532860606512090081 : ℚ) / 10 ^ 30
  | 1 => (-72815845483676724860586375876 : ℚ) / 10 ^ 30
  | 2 => (-9690363192872318484530386037 : ℚ) / 10 ^ 30
  | 3 => (2053834420303345866160046541 : ℚ) / 10 ^ 30
  | 4 => (2325370065467300057468170176 : ℚ) / 10 ^ 30
  | 5 => (793323817301062701753334876 : ℚ) / 10 ^ 30
  | 6 => (-238769345430199609872421843 : ℚ) / 10 ^ 30
  | 7 => (-527289567057751046074097507 : ℚ) / 10 ^ 30
  | 8 => (-352123353803039509602052167 : ℚ) / 10 ^ 30
  | 9 => (-34394774418088048177914625 : ℚ) / 10 ^ 30
  | 10 => (205332814909064794683722288 : ℚ) / 10 ^ 30
  | 11 => (270184439543903526672902081 : ℚ) / 10 ^ 30
  | _ => 0

/-- The table's upper bounds for γ_0, …, γ_11 (the bench, rounded up at 10⁻³⁰). -/
def stHi : ℕ → ℚ
  | 0 => (577215664901532860606512090084 : ℚ) / 10 ^ 30
  | 1 => (-72815845483676724860586375873 : ℚ) / 10 ^ 30
  | 2 => (-9690363192872318484530386034 : ℚ) / 10 ^ 30
  | 3 => (2053834420303345866160046544 : ℚ) / 10 ^ 30
  | 4 => (2325370065467300057468170179 : ℚ) / 10 ^ 30
  | 5 => (793323817301062701753334879 : ℚ) / 10 ^ 30
  | 6 => (-238769345430199609872421840 : ℚ) / 10 ^ 30
  | 7 => (-527289567057751046074097504 : ℚ) / 10 ^ 30
  | 8 => (-352123353803039509602052164 : ℚ) / 10 ^ 30
  | 9 => (-34394774418088048177914622 : ℚ) / 10 ^ 30
  | 10 => (205332814909064794683722291 : ℚ) / 10 ^ 30
  | 11 => (270184439543903526672902084 : ℚ) / 10 ^ 30
  | _ => 0

/-- The table's lower bounds for ζ(2), …, ζ(12). -/
def zLo : ℕ → ℚ
  | 2 => (1644934066848226436472415166645 : ℚ) / 10 ^ 30
  | 3 => (1202056903159594285399738161510 : ℚ) / 10 ^ 30
  | 4 => (1082323233711138191516003696540 : ℚ) / 10 ^ 30
  | 5 => (1036927755143369926331365486456 : ℚ) / 10 ^ 30
  | 6 => (1017343061984449139714517929789 : ℚ) / 10 ^ 30
  | 7 => (1008349277381922826839797549848 : ℚ) / 10 ^ 30
  | 8 => (1004077356197944339378685238507 : ℚ) / 10 ^ 30
  | 9 => (1002008392826082214417852769231 : ℚ) / 10 ^ 30
  | 10 => (1000994575127818085337145958899 : ℚ) / 10 ^ 30
  | 11 => (1000494188604119464558702282525 : ℚ) / 10 ^ 30
  | 12 => (1000246086553308048298637998046 : ℚ) / 10 ^ 30
  | _ => 0

/-- The table's upper bounds for ζ(2), …, ζ(12). -/
def zHi : ℕ → ℚ
  | 2 => (1644934066848226436472415166648 : ℚ) / 10 ^ 30
  | 3 => (1202056903159594285399738161513 : ℚ) / 10 ^ 30
  | 4 => (1082323233711138191516003696543 : ℚ) / 10 ^ 30
  | 5 => (1036927755143369926331365486459 : ℚ) / 10 ^ 30
  | 6 => (1017343061984449139714517929792 : ℚ) / 10 ^ 30
  | 7 => (1008349277381922826839797549851 : ℚ) / 10 ^ 30
  | 8 => (1004077356197944339378685238510 : ℚ) / 10 ^ 30
  | 9 => (1002008392826082214417852769234 : ℚ) / 10 ^ 30
  | 10 => (1000994575127818085337145958902 : ℚ) / 10 ^ 30
  | 11 => (1000494188604119464558702282528 : ℚ) / 10 ^ 30
  | 12 => (1000246086553308048298637998049 : ℚ) / 10 ^ 30
  | _ => 0

/-- The `n`-th Stieltjes constant in the table's interval. -/
def StieltjesBoundsAt (n : ℕ) : Prop := InInterval (stLo n) (stHi n) (stieltjes n)

/-- The zeta value at `j` in the table's interval. -/
def ZetaValueBoundsAt (j : ℕ) : Prop := InInterval (zLo j) (zHi j) (riemannZeta (j : ℂ))

/-- **THE WORK-ORDER'S LEMMA (2), AS A PROP**: every constant the Keiper sum consumes up to `n = 12`, in its interval. -/
def KeiperBounds : Prop :=
  (∀ n : ℕ, n ≤ 11 → StieltjesBoundsAt n) ∧ (∀ j : ℕ, 2 ≤ j → j ≤ 12 → ZetaValueBoundsAt j)

/-- **THE NAMED PREMISES**: Euler's γ to the table's width; the Stieltjes constants from the first to the eleventh; the zeta
values from ζ(2) to ζ(12). -/
structure BoundPremises : Prop where
  gamma_tight : StieltjesBoundsAt 0
  higher_stieltjes : ∀ n : ℕ, 1 ≤ n → n ≤ 11 → StieltjesBoundsAt n
  zeta_values : ∀ j : ℕ, 2 ≤ j → j ≤ 12 → ZetaValueBoundsAt j

/-- **AT INTERFACES ON THE NAMED PREMISES**: the bounds. -/
theorem keiperBounds_of (hP : BoundPremises) : KeiperBounds := by
  unfold KeiperBounds
  refine ⟨fun n hn => ?_, hP.zeta_values⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    exact hP.gamma_tight
  · exact hP.higher_stieltjes n h hn

/-- **CLOSED: γ_0 in Mathlib's interval** (1/2, 2/3), on the real line. -/
theorem stieltjes_zero_coarse : InInterval (1 / 2) (2 / 3) (stieltjes 0) := by
  unfold InInterval
  rw [stieltjes_zero, Complex.ofReal_re, Complex.ofReal_im]
  have h1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have h2 : ((2 / 3 : ℚ) : ℝ) = 2 / 3 := by norm_num
  rw [h1, h2]
  exact ⟨Real.one_half_lt_eulerMascheroniConstant.le, Real.eulerMascheroniConstant_lt_two_thirds.le, rfl⟩

/-- **The table's interval at 0 lies inside Mathlib's**: the premise `gamma_tight` refines the closed bound. -/
theorem table_refines_coarse : (1 / 2 : ℚ) ≤ stLo 0 ∧ stHi 0 ≤ (2 / 3 : ℚ) := by
  constructor <;> norm_num [stLo, stHi]

end KeiperBounds
end SIDEExplicitFormula
