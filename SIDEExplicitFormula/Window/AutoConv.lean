import SIDEExplicitFormula.Window.AutoP
import SIDEExplicitFormula.Window.AutoQ
import SIDEExplicitFormula.Window.AutoR0
import SIDEExplicitFormula.Window.AutoR1

/-!
# L9c1: the autocorrelation of the window`s numerators, by one product of packed integers

Written by relay tools/b768_packed_data.py from Coeffs.lean as its blob stands at the branch`s base (blob 167a41b457e70dd4);
edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

/-- The convolution sums of the numerators and their turn: the autocorrelation laid symmetrically about the place 16364,
the last place `0`. -/
def autoD : List ℤ := (autoRBlk0 ++ autoRBlk1 ++ autoRBlk2 ++ autoRBlk3 ++ autoRBlk4 ++ autoRBlk5 ++ autoRBlk6 ++ autoRBlk7 ++ autoRBlk8).flatten

theorem coeffList_blocks : coeffList = (autoPBlk0 ++ autoPBlk1 ++ autoPBlk2 ++ autoPBlk3).flatten := by
  simp only [coeffList, autoPBlk0, autoPBlk1, autoPBlk2, autoPBlk3, List.cons_append, List.nil_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem coeffList_rev_blocks : coeffList.reverse = (autoQBlk0 ++ autoQBlk1 ++ autoQBlk2 ++ autoQBlk3).flatten := by
  simp only [coeffList, autoQBlk0, autoQBlk1, autoQBlk2, autoQBlk3, List.reverse_append, List.cons_append, List.nil_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]

theorem auto_P : packL packBase coeffList = joinG packBase (autoPI0 ++ autoPI1 ++ autoPI2 ++ autoPI3) := by
  rw [coeffList_blocks, packL_flatten_gen, List.map_append, List.map_append, List.map_append, autoP_info0, autoP_info1, autoP_info2, autoP_info3]

theorem auto_Q : packL packBase coeffList.reverse = joinG packBase (autoQI0 ++ autoQI1 ++ autoQI2 ++ autoQI3) := by
  rw [coeffList_rev_blocks, packL_flatten_gen, List.map_append, List.map_append, List.map_append, autoQ_info0, autoQ_info1, autoQ_info2, autoQ_info3]

theorem auto_R : packL packBase autoD = joinG packBase (autoRI0 ++ autoRI1 ++ autoRI2 ++ autoRI3 ++ autoRI4 ++ autoRI5 ++ autoRI6 ++ autoRI7 ++ autoRI8) := by
  unfold autoD
  rw [packL_flatten_gen, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, autoR_info0, autoR_info1, autoR_info2, autoR_info3, autoR_info4, autoR_info5, autoR_info6, autoR_info7, autoR_info8]

set_option maxHeartbeats 0 in
theorem auto_join_ok : joinG packBase (autoPI0 ++ autoPI1 ++ autoPI2 ++ autoPI3) * joinG packBase (autoQI0 ++ autoQI1 ++ autoQI2 ++ autoQI3) =
    joinG packBase (autoRI0 ++ autoRI1 ++ autoRI2 ++ autoRI3 ++ autoRI4 ++ autoRI5 ++ autoRI6 ++ autoRI7 ++ autoRI8) := by decide +kernel

/-- The product of the packed numerators and the packed numerators turned is the packed convolution sums. -/
theorem auto_prod : packL packBase coeffList * packL packBase coeffList.reverse = packL packBase autoD := by
  rw [auto_P, auto_Q, auto_R]
  exact auto_join_ok

theorem coeffList_len : coeffList.length = 16365 := by
  rw [coeffList_blocks, length_flatten_gen packBase, List.map_append, List.map_append, List.map_append, autoP_info0, autoP_info1, autoP_info2, autoP_info3]
  decide +kernel

theorem coeffList_rev_len : coeffList.reverse.length = coeffList.length := by
  first
  | exact List.length_reverse _
  | exact List.length_reverse
  | simp

theorem autoD_len : autoD.length = 2 * coeffList.length := by
  rw [coeffList_len]
  unfold autoD
  rw [length_flatten_gen packBase, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, autoR_info0, autoR_info1, autoR_info2, autoR_info3, autoR_info4, autoR_info5, autoR_info6, autoR_info7, autoR_info8]
  decide +kernel

theorem coeffList_bd : ∀ x ∈ coeffList, -numBound ≤ x ∧ x ≤ numBound := by
  rw [coeffList_blocks]
  refine all_flatten (P := fun x => -numBound ≤ x ∧ x ≤ numBound) _ ?_
  simp only [List.all_append, autoP_bd0, autoP_bd1, autoP_bd2, autoP_bd3, Bool.and_self]

theorem coeffList_rev_bd : ∀ x ∈ coeffList.reverse, -numBound ≤ x ∧ x ≤ numBound := by
  rw [coeffList_rev_blocks]
  refine all_flatten (P := fun x => -numBound ≤ x ∧ x ≤ numBound) _ ?_
  simp only [List.all_append, autoQ_bd0, autoQ_bd1, autoQ_bd2, autoQ_bd3, Bool.and_self]

theorem autoD_bd : ∀ x ∈ autoD, -packBase < 2 * x ∧ 2 * x < packBase := by
  unfold autoD
  refine all_flatten (P := fun x => -packBase < 2 * x ∧ 2 * x < packBase) _ ?_
  simp only [List.all_append, autoR_bd0, autoR_bd1, autoR_bd2, autoR_bd3, autoR_bd4, autoR_bd5, autoR_bd6, autoR_bd7, autoR_bd8, Bool.and_self]

theorem auto_bM : 2 * ((coeffList.length : ℤ) * (numBound * numBound)) < packBase := by
  rw [coeffList_len]
  decide +kernel

/-- **L9c1**: each convolution sum of the numerators and their turn is the place of `autoD` at its index. -/
theorem auto_conv : ∀ k < 2 * coeffList.length,
    convR coeffList.length (fun i => coeffList.getD i 0) (fun j => coeffList.reverse.getD j 0) k = autoD.getD k 0 :=
  conv_of_packedL (M := numBound) packBase_ge coeffList coeffList.reverse autoD coeffList_rev_len autoD_len coeffList_bd
    coeffList_rev_bd auto_bM autoD_bd auto_prod

end Window
end SIDEExplicitFormula
