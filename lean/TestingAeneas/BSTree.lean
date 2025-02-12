import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

attribute [-simp] Bool.exists_bool

section SetImpl/- {{{ -/

namespace Spec/- {{{ -/
open testing_aeneas
def contains[BEq α][LT α][DecidableLT α]: BSTree α -> α -> Bool
| .Nil, _=> false
| .Node curr left right, target => 
    if target == curr then
      True
    else if target < curr then 
      contains left target 
    else 
      contains right target 

def insert[BEq α][LT α][DecidableLT α](value: α): BSTree α -> BSTree α
| .Nil => .Node value .Nil .Nil
| .Node curr left right =>
    if value < curr then
      .Node curr (insert value left) right
    else if value > curr then 
      .Node curr left (insert value right)
    else 
      .Node curr left right
end Spec/- }}} -/

open testing_aeneas
section Translation/- {{{ -/
@[simp] def testing_aeneas.BSTree.toSpec: BSTree α -> Set α
| .Nil => ∅
| .Node v left right => {v} ∪ (toSpec left) ∪ (toSpec right)

instance: Coe (BSTree α) (Set α) where
  coe := BSTree.toSpec
end Translation/- }}} -/

namespace Lemmas/- {{{ -/
@[simp] def well_formed[PartialOrder α][IsTotal α (·<=·)]: BSTree α -> Prop
| .Nil => True
| .Node curr left right =>
  well_formed left ∧ well_formed right ∧ 
    (∀ x ∈ (left: Set α),  x < curr) ∧
    (∀ x ∈ (right: Set α), curr < x)

theorem left_disjoint_right_of_wf[PartialOrder α][IsTotal α (·<=·)]
  {curr: α}{left right: BSTree α}
: well_formed (.Node curr left right) -> Disjoint (toSpec left) (toSpec right)
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

@[pspec]
theorem contains_spec(tree: BSTree Isize)(target: Isize)
: well_formed tree 
-> ∃ b,
    BSTreeIsize.contains tree target = Result.ok b ∧
    (b = true ↔ target ∈ (tree : Set Isize))
:= by 
  intro well_formed
  rw [BSTreeIsize.contains]
  cases tree <;> simp at *
  case Node curr left right =>
    have left_disjoint_right := left_disjoint_right_of_wf well_formed
    obtain ⟨left_wf, right_wf, left_inv, right_inv⟩ := well_formed
    split_ifs <;> simp [*]
    case pos curr_neq_target target_lt_curr =>
      progress as ⟨left_contains_target, left_contains_target_spec⟩
      if left_contains_target then
        simp_all
      else
        simp_all
        intro target_in_right
        have := right_inv _ target_in_right
        omega
    case neg curr_neq_target target_ge_curr =>
      have target_ge_curr := (le_of_not_gt target_ge_curr)
      progress as ⟨right_contains_target, right_contains_target_spec⟩
      if right_contains_target then
        simp_all
      else
        simp_all
        intro target_in_left
        have := left_inv _ target_in_left
        omega

@[pspec]
theorem insert_spec(tree: BSTree Isize)(value: Isize)
: well_formed tree
-> ∃ tree',
    BSTreeIsize.insert tree value = Result.ok tree' ∧
    insert value (toSpec tree) = ↑tree' ∧
    well_formed tree'
:= by
  rw [BSTreeIsize.insert]
  cases tree <;> simp
  case Node curr left right =>
    intro left_wf right_wf left_inv right_inv
    split_ifs
    case pos value_lt_curr =>
      progress as ⟨left', left'_spec, left'_wf⟩; simp
      split_conjs <;> try assumption
      · rw [<-left'_spec]
        simp [Set.insert_union, Set.insert_comm]
      · rw [<-left'_spec]
        simp [value_lt_curr]
        assumption
    case pos not_value_lt_curr value_gt_curr =>
      progress as ⟨right', right'_spec, right'_wf⟩
      simp; split_conjs <;> try assumption
      · rw [<-right'_spec]
        simp [Set.insert_union]
      · rw [<-right'_spec]
        simp [value_gt_curr]
        assumption
    case neg not_value_lt_curr not_value_gt_curr =>
      have: curr = value := by scalar_tac
      subst this
      simp; split_conjs <;> assumption


end Lemmas/- }}} -/
end SetImpl/- }}} -/
