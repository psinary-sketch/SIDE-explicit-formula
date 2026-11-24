import SIDEExplicitFormula.Window.Packed

/-!
# Packed chunks of any lengths, reading no datum

A list cut into chunks of any lengths is packed as the join of its chunks: `chunkInfo b c` is a chunk`s packed value
with its length, `joinG b` joins such pairs (`packL_flatten_gen`), and `lenG` sums their lengths
(`length_flatten_gen`). `all_flatten` reads a property at each place of a flattened list from a check of each chunk.
Nothing here is evaluated.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The base of the far sum`s packings, a power of two above twice the bound on each convolution sum. -/
def packBase : ℤ := 2 ^ 133

/-- A round bound on the absolute value of each numerator of the window. -/
def numBound : ℤ := 4 * 10 ^ 17

theorem packBase_ge : 2 ≤ packBase := by decide +kernel

/-- A chunk`s packed value in the base `b`, with its length. -/
def chunkInfo (b : ℤ) (c : List ℤ) : ℤ × ℕ := (packL b c, c.length)

/-- The joined value of packed chunks, each given by its value and its length. -/
def joinG (b : ℤ) : List (ℤ × ℕ) → ℤ
  | [] => 0
  | p :: ps => p.1 + b ^ p.2 * joinG b ps

/-- The sum of the chunks` lengths. -/
def lenG : List (ℤ × ℕ) → ℕ
  | [] => 0
  | p :: ps => p.2 + lenG ps

theorem joinG_nil (b : ℤ) : joinG b [] = 0 := rfl

theorem joinG_cons (b : ℤ) (p : ℤ × ℕ) (ps : List (ℤ × ℕ)) : joinG b (p :: ps) = p.1 + b ^ p.2 * joinG b ps := rfl

theorem lenG_nil : lenG [] = 0 := rfl

theorem lenG_cons (p : ℤ × ℕ) (ps : List (ℤ × ℕ)) : lenG (p :: ps) = p.2 + lenG ps := rfl

theorem chunks_flatten_cons (c : List ℤ) (cs : List (List ℤ)) : (c :: cs).flatten = c ++ cs.flatten := by
  first | rfl | simp

theorem chunks_map_cons (b : ℤ) (c : List ℤ) (cs : List (List ℤ)) :
    (c :: cs).map (chunkInfo b) = chunkInfo b c :: cs.map (chunkInfo b) := by
  first | rfl | simp

/-- The packed value of a flattened list is the join of its chunks` values. -/
theorem packL_flatten_gen (b : ℤ) : ∀ cs : List (List ℤ), packL b cs.flatten = joinG b (cs.map (chunkInfo b))
  | [] => rfl
  | c :: cs => by
    rw [chunks_flatten_cons, chunks_map_cons, joinG_cons, packL_append, packL_flatten_gen b cs]
    rfl

/-- The length of a flattened list is the sum of its chunks` lengths. -/
theorem length_flatten_gen (b : ℤ) : ∀ cs : List (List ℤ), cs.flatten.length = lenG (cs.map (chunkInfo b))
  | [] => rfl
  | c :: cs => by
    rw [chunks_flatten_cons, chunks_map_cons, lenG_cons, List.length_append, length_flatten_gen b cs]
    rfl

theorem chunks_all_cons (f : List ℤ → Bool) (c : List ℤ) (cs : List (List ℤ)) :
    (c :: cs).all f = (f c && cs.all f) := by
  first | rfl | simp

/-- A property at each place of a flattened list, from a check of each chunk. -/
theorem all_flatten {P : ℤ → Prop} [DecidablePred P] :
    ∀ cs : List (List ℤ), (cs.all fun c => c.all fun x => decide (P x)) = true → ∀ x ∈ cs.flatten, P x
  | [], _, x, hx => by
    first
    | exact absurd hx (List.not_mem_nil _)
    | exact absurd hx List.not_mem_nil
    | simp at hx
  | c :: cs, h, x, hx => by
    rw [chunks_all_cons] at h
    have h1 : (c.all fun x => decide (P x)) = true := by
      first
      | exact (Bool.and_eq_true _ _ ▸ h).1
      | exact (Bool.and_eq_true_iff.mp h).1
      | (simp only [Bool.and_eq_true] at h
         exact h.1)
    have h2 : (cs.all fun c => c.all fun x => decide (P x)) = true := by
      first
      | exact (Bool.and_eq_true _ _ ▸ h).2
      | exact (Bool.and_eq_true_iff.mp h).2
      | (simp only [Bool.and_eq_true] at h
         exact h.2)
    rw [chunks_flatten_cons] at hx
    rcases List.mem_append.mp hx with hc | hcs
    · exact forall_of_all c h1 x hc
    · exact all_flatten cs h2 x hcs

end Window
end SIDEExplicitFormula
