import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

namespace testing_aeneas
end testing_aeneas

namespace Spec/- {{{ -/
inductive BSTree(α : Type) where
| Nil 
| Node (value: α)(left right: BSTree α)

open testing_aeneas
def BSTree.contains[BEq α][LT α][DecidableLT α]: BSTree α -> α -> Bool
| .Nil, _=> false
| .Node curr left right, target => 
    if target == curr then
      True
    else if target < curr then 
      contains left target 
    else 
      contains right target 

def BSTree.insert[BEq α][LT α][DecidableLT α](value: α): BSTree α -> BSTree α
| .Nil => .Node value .Nil .Nil
| .Node curr left right =>
    if value < curr then
      .Node curr (insert value left) right
    else if value > curr then 
      .Node curr left (insert value right)
    else 
      .Node curr left right

@[simp] def BSTree.toSpec: BSTree α -> Set α
| .Nil => ∅
| .Node v left right => {v} ∪ (toSpec left) ∪ (toSpec right)
instance: Coe (Spec.BSTree α) (Set α) where coe := Spec.BSTree.toSpec

@[simp] def BSTree.well_formed[PartialOrder α][IsTotal α (·<=·)]: BSTree α -> Prop
| .Nil => True
| .Node curr left right =>
  well_formed left ∧ well_formed right ∧ 
    (∀ x ∈ (left: Set α),  x < curr) ∧
    (∀ x ∈ (right: Set α), curr < x)
end Spec/- }}} -/

section Translation/- {{{ -/
open testing_aeneas
@[simp] def testing_aeneas.BSTree.toSpec: BSTree α -> Spec.BSTree α
| .Nil => .Nil
| .Node v l r => .Node v l.toSpec r.toSpec
instance: Coe (BSTree α) (Spec.BSTree α) where coe := BSTree.toSpec
end Translation/- }}} -/

section Lemmas/- {{{ -/
attribute [-simp] Bool.exists_bool
attribute [local simp] Spec.BSTree.contains
attribute [local simp] Spec.BSTree.insert
open testing_aeneas.BSTree renaming toSpec -> toSet
open Spec.BSTree (toSpec)

namespace SetRefinement/- {{{ -/
open Spec
theorem left_right_disjoint_of_wf[PartialOrder α][IsTotal α (·<=·)]
  {curr: α}{left right: BSTree α}
: (BSTree.Node curr left right).well_formed -> Disjoint (toSpec left) (toSpec right)
:= by
  intro ⟨left_wf, right_wf, left_inv, right_inv⟩
  apply disjoint_iff.mpr; simp
  apply Set.subset_empty_iff.mp
  intro x ⟨xl, xr⟩
  have h1:=left_inv x xl 
  have h2:=right_inv x xr
  have := Trans.trans h1 h2
  have := lt_irrefl x
  contradiction

theorem contains_spec{tree: BSTree Isize}(target: Isize)
: tree.well_formed
-> (tree.contains target ↔ target ∈ (tree : Set Isize))
:= by 
  intro well_formed
  cases tree <;> simp at *
  case Node curr left right =>
    have left_disjoint_right := left_right_disjoint_of_wf well_formed
    obtain ⟨left_wf, right_wf, left_inv, right_inv⟩ := well_formed
    split_ifs <;> try simp [*]
    case pos target_lt_curr =>
      have := contains_spec target left_wf
      /- progress as ⟨left_contains_target, left_contains_target_spec⟩ -/
      if left.contains target then
        simp_all
      else
        simp_all
        intro target_in_right
        have := right_inv _ target_in_right
        omega
    case neg target_ge_curr =>
      have target_ge_curr := (le_of_not_gt target_ge_curr)
      have := contains_spec target right_wf
      if right.contains target then
        simp_all
      else
        simp_all
        intro target_in_left
        have := left_inv _ target_in_left
        omega

theorem insert_spec(tree: BSTree Isize)(value: Isize)
: tree.well_formed
-> let tree' := tree.insert value
   insert value (toSpec tree) = ↑tree' ∧ tree'.well_formed
:= by
  cases tree <;> simp
  case Node curr left right =>
    intro left_wf right_wf left_inv right_inv
    have ⟨left'_spec, left'_wf⟩:= insert_spec left value left_wf
    have ⟨right'_spec, right'_wf⟩:= insert_spec right value right_wf
    split_ifs <;> simp [*] at *
    case pos value_lt_curr =>
      split_conjs <;> try assumption
      · rw [<-left'_spec]
        simp [Set.insert_union, Set.insert_comm]
      · rw [<-left'_spec]
        simp [value_lt_curr]
        assumption
    case pos curr_lt_value _ =>
      split_conjs <;> try assumption
      · rw [<-right'_spec]
        simp [Set.insert_union]
      · rw [<-right'_spec]
        simp [curr_lt_value]
        assumption
    case neg not_value_lt_curr not_value_gt_curr =>
      have: curr = value := by scalar_tac
      subst this
      simp; split_conjs <;> assumption

end SetRefinement/- }}} -/

namespace TreeRefinement/- {{{ -/
open testing_aeneas

@[pspec]
theorem tree_contains_spec(tree: BSTree Isize)(target: Isize)
: ∃ b, 
    BSTreeIsize.contains tree target = Result.ok b ∧
    Spec.BSTree.contains ↑tree target = b
:= by
  cases tree <;> rw [BSTreeIsize.contains] <;> simp
  case Node curr left right =>
    split_ifs <;> (try progress with tree_contains_spec as ⟨in_left, in_left_spec⟩) <;> simp [*]

@[pspec]
theorem tree_insert_spec(tree: BSTree Isize)(value: Isize)
: ∃ tree',
    BSTreeIsize.insert tree value = Result.ok tree' ∧
    Spec.BSTree.insert value ↑tree = ↑tree'
:= by
  cases tree <;> rw [BSTreeIsize.insert] <;> simp
  case Node curr left right =>
    split_ifs <;> (try progress with tree_insert_spec as ⟨tree', tree'_spec⟩) <;> simp [*]

end TreeRefinement/- }}} -/

end Lemmas/- }}} -/
