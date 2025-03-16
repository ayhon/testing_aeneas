import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

namespace testing_aeneas
end testing_aeneas

section Operations/- {{{ -/
namespace Spec
inductive BSTree(α : Type) where
| Nil 
| Node (value: α)(left right: BSTree α)
deriving Inhabited

open testing_aeneas
@[simp] def BSTree.contains[BEq α][LT α][DecidableLT α]: BSTree α -> α -> Bool
| .Nil, _=> false
| .Node curr left right, target => 
    if target == curr then
      True
    else if target < curr then 
      contains left target 
    else 
      contains right target 

@[simp] def BSTree.insert[BEq α][LT α][DecidableLT α](value: α): BSTree α -> BSTree α
| .Nil => .Node value .Nil .Nil
| .Node curr left right =>
    if value < curr then
      .Node curr (insert value left) right
    else if value > curr then 
      .Node curr left (insert value right)
    else 
      .Node curr left right
end Spec
end Operations/- }}} -/

section Refinements/- {{{ -/
open testing_aeneas
@[simp] def testing_aeneas.BSTree.toSpec: BSTree α -> Spec.BSTree α
| .Nil => .Nil
| .Node v l r => .Node v l.toSpec r.toSpec
instance: Coe (BSTree α) (Spec.BSTree α) where coe := BSTree.toSpec

@[simp] def Spec.BSTree.toSet: BSTree α -> Set α
| .Nil => ∅
| .Node v left right => {v} ∪ left.toSet ∪ right.toSet
instance: Coe (Spec.BSTree α) (Set α) where coe := Spec.BSTree.toSet
end Refinements/- }}} -/

section Propositions/- {{{ -/
@[simp] def Spec.BSTree.well_formed[LinearOrder α]: BSTree α -> Prop
| .Nil => True
| .Node curr left right =>
  well_formed left ∧ well_formed right ∧ 
    (∀ x ∈ (left: Set α),  x < curr) ∧
    (∀ x ∈ (right: Set α), curr < x)
end Propositions/- }}} -/

section Lemmas/- {{{ -/
attribute [-simp] Bool.exists_bool
attribute [local simp] Spec.BSTree.contains
attribute [local simp] Spec.BSTree.insert
open testing_aeneas.BSTree renaming toSpec -> toSet

section SetRefinement/- {{{ -/
namespace Spec
theorem BSTree.left_right_disjoint_of_wf[LinearOrder α]
  {curr: α}{left right: BSTree α}
: (BSTree.Node curr left right).well_formed -> Disjoint left.toSet right.toSet
:= by/- {{{ -/
  intro ⟨left_wf, right_wf, left_inv, right_inv⟩
  apply disjoint_iff.mpr; simp
  apply Set.subset_empty_iff.mp
  intro x ⟨xl, xr⟩
  have h1:=left_inv x xl 
  have h2:=right_inv x xr
  have := Trans.trans h1 h2
  have := lt_irrefl x
  contradiction/- }}} -/

theorem BSTree.not_mem_value_of_wf[LinearOrder α]
  {curr: α}{left right: BSTree α}
: (BSTree.Node curr left right).well_formed 
→ curr ∉ (left.toSet ∪ right.toSet)
:= by/- {{{ -/
  intro ⟨_, _, left_bs, right_bs⟩
  intro hyp; obtain hyp | hyp := hyp
  · exact (lt_self_iff_false curr).mp (left_bs curr hyp)
  · exact (lt_self_iff_false curr).mp (right_bs curr hyp)/- }}} -/

theorem BSTree.contains.spec[LinearOrder α]{tree: BSTree α}(target: α)
: tree.well_formed
-> (tree.contains target ↔ target ∈ (tree : Set α))
:= by /- {{{ -/
  intro well_formed
  cases tree <;> simp at *
  case Node curr left right =>
    have left_disjoint_right := left_right_disjoint_of_wf well_formed
    obtain ⟨left_wf, right_wf, left_inv, right_inv⟩ := well_formed
    split_ifs <;> try simp [*]
    case pos target_lt_curr =>
      have := contains.spec target left_wf
      /- progress as ⟨left_contains_target, left_contains_target_spec⟩ -/
      if left.contains target then
        simp_all
      else
        simp_all
        intro target_in_right
        have := right_inv _ target_in_right
        have := ne_of_lt (Trans.trans this target_lt_curr)
        contradiction
    case neg target_ge_curr =>
      have target_ge_curr := (le_of_not_gt target_ge_curr)
      have := contains.spec target right_wf
      if right.contains target then
        simp_all
      else
        simp_all
        intro target_in_left
        have := left_inv _ target_in_left
        have := ne_of_lt (Trans.trans this target_ge_curr)
        contradiction/- }}} -/

theorem BSTree.insert.spec[LinearOrder α]{tree: BSTree α}
: tree.well_formed
-> ∀ value, 
   let tree' := tree.insert value
   tree'.toSet = Insert.insert value tree.toSet ∧ 
   tree'.well_formed
:= by/- {{{ -/
  cases tree  <;> simp
  case Node curr left right =>
    intro left_wf right_wf left_inv right_inv value
    have left_rec := insert.spec left_wf value
    have right_rec := insert.spec right_wf value
    split_ifs <;> simp [*] at *
    case pos value_lt_curr =>
      split_conjs <;> try assumption
      · simp [Set.insert_union, Set.insert_comm]
    case pos curr_lt_value _ =>
      split_conjs <;> try assumption
    case neg not_value_lt_curr not_value_gt_curr =>
      have: curr = value := eq_of_le_of_le (not_value_lt_curr) (not_value_gt_curr)
      subst this
      simp; split_conjs <;> assumption/- }}} -/

end Spec
end SetRefinement/- }}} -/

section TreeRefinement/- {{{ -/
namespace testing_aeneas

@[progress]
theorem BSTreeIsize.contains.spec(tree: BSTree Isize)(target: Isize)
: ∃ b, 
    BSTreeIsize.contains tree target = Result.ok b ∧
    Spec.BSTree.contains ↑tree target = b
:= by/- {{{ -/
  rw [BSTreeIsize.contains]
  progress* <;> simp [*]/- }}} -/

@[progress]
theorem BSTreeIsize.insert.spec(tree: BSTree Isize)(value: Isize)
: ∃ tree',
    BSTreeIsize.insert tree value = Result.ok tree' ∧
    Spec.BSTree.insert value ↑tree = ↑tree'
:= by/- {{{ -/
  rw [BSTreeIsize.insert]
  progress* <;> simp [*]/- }}} -/

end testing_aeneas
end TreeRefinement/- }}} -/

end Lemmas/- }}} -/
