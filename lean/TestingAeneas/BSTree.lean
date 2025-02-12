import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

attribute [-simp] Bool.exists_bool


namespace SetImpl/- {{{ -/
namespace Spec/- {{{ -/
/-
In this case, the spec is simply Mathlib's `Set`.
Then `insert x` is just `∪ {x}` and `contains`
is the ∈ operator.

EDIT: Actually, I'll just use a list, with a couple
 of restrictions if needed
-/
/- structure Set(α: Type)where -/
/-   toList: List α -/

/- def Set.all(condition: α -> Bool)(set : Set α): Bool := set.toList.all condition -/

/- def Set.contains[BEq α](set: Set α)(target: α): Bool := set.toList.contains target -/
/- instance[BEq α]: Membership (α) (Set α) where mem set target := set.contains target = true -/
/- instance[BEq α](set: Set α): Decidable (x ∈ set) -/

/- def Set.inclusion[BEq α](set set': Set α): Bool := set.all set'.contains -/
/- instance[BEq α]: HasSubset (Set α) where Subset set set' := set'.inclusion set = true -/

/- def Set.beq[BEq α](set set': Set α): Bool := set.inclusion set' && set'.inclusion set -/
/- instance[BEq α]: BEq (Set α) where beq := Set.beq -/

/- def Set.insert[BEq α](set: Set α)(target: α) := -/ 
/-   if set.all (· != target) -/ 
/-   then {set with toList := target :: set.toList} -/
/-   else set`Finset` -/

/- theorem all_contains[BEq α](set: Set α)(condition: α -> Bool) -/
/- : set.all condition ↔ (∀ x, set.contains x -> condition x) -/ 
/- := sorry -/
/- 
EDIT2: I'm going to try with Mathlib's `Set` again
-/


end Spec/- }}} -/

namespace Lemmas/- {{{ -/

open testing_aeneas
section Translation/- {{{ -/

@[simp] def toSpec: BSTree α -> Set α
| .Nil => ∅
| .Node v left right => {v} ∪ (toSpec left) ∪ (toSpec right)

instance: Coe (BSTree α) (Set α) where
  coe := toSpec

/- theorem toSpec_equiv{tree tree': BSTree α} -/
/- : (tree : Set α) = tree' ↔ tree = tree' -/
/- := sorry -/
-- NOTE: This refinement is not injective!
end Translation/- }}} -/

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
