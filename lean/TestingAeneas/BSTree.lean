import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

attribute [-simp] Bool.exists_bool

namespace TreeImpl/- {{{ -/
namespace Spec/- {{{ -/

inductive BSTree(α: Type) where
| Nil : BSTree α
| Node(v: α)(left right: BSTree α): BSTree α

def BSTree.contains[BEq α]: BSTree α -> α -> Bool
| Nil, _=> false
| Node curr left right, target => 
    curr == target || left.contains target || right.contains target

def BSTree.insert[BEq α][LE α][DecidableLE α](value: α): BSTree α -> BSTree α
| Nil => Node value Nil Nil
| Node curr left right =>
  if value == curr then 
    Node curr left right
  else if value <= curr then -- This is actually value < curr, but we define everything in terms of LE
    Node curr (left.insert value) right
  else 
    Node curr left (right.insert value)

@[simp]
abbrev between[LE α][DecidableLE α](lo hi value: α) := decide (lo <= value ∧ value <= hi)

def BSTree.for_all(condition: α -> Bool): BSTree α -> Bool
| Nil => True
| Node curr left right =>
  condition curr && left.for_all condition && right.for_all condition

inductive BSTree.WellFormed[LE α][DecidableLE α][BoundedOrder α]: BSTree α -> α -> α -> Prop where
  | isEmpty : ∀ a b : α, BSTree.Nil.WellFormed a b
  -- The problem with this (↑) approach is that we no longer have
  -- the invariant that a <= b, which may be useful for proofs.
  -- Solution: Add it to compound. In general, the empty tree 
  --  should satisfy any possible bounds, so the definition makes sense
  | isCompound(v: α)
    (left right: BSTree α)
    (left_inv:  left.for_all <| between l v)
    (right_inv: right.for_all <| between v r)
    (non_empty: between l r v)
    : (left_wf: left.WellFormed l v) -> (right_wf: right.WellFormed v r) -> (Node v left right).WellFormed l r

end Spec/- }}} -/
namespace Lemmas/- {{{ -/
open testing_aeneas

section Translation/- {{{ -/

@[simp]
def toSpec: BSTree α -> Spec.BSTree α
| .Nil => .Nil 
| .Node v left right => .Node v (toSpec left) (toSpec right)

instance: Coe (BSTree α) (Spec.BSTree α) where
  coe := toSpec

theorem toSpec_equiv{tree tree': BSTree α}
: (tree: Spec.BSTree α) = tree' ↔ tree = tree'
:= match tree, tree' with
   | .Nil, .Nil
   | .Node .., .Nil
   | .Nil , .Node .. => by simp [toSpec]
   | .Node v left right, .Node v' left' right' => by 
      simp [toSpec]; intro
      apply Iff.intro
      case mp =>
        intro; split_conj <;> apply toSpec_equiv.mp <;> simp [*]
      case mpr =>
        intro ⟨h1, h2⟩; subst h1 h2; simp
end Translation/- }}} -/

instance: BoundedOrder (Scalar ty) where
  top := ⟨Scalar.max ty, by scalar_tac, by scalar_tac⟩
  bot := ⟨Scalar.min ty, by scalar_tac, by scalar_tac⟩
  le_top := by scalar_tac
  bot_le := by scalar_tac

theorem for_all_iff_contains[BEq α][LawfulBEq α]{tree: Spec.BSTree α}{p: α -> Bool}
: tree.for_all p ↔ (∀ x : α, tree.contains x -> p x)
:= match tree with
   | .Nil => by simp [Spec.BSTree.for_all, Spec.BSTree.contains]
   | .Node curr left right => by
      simp [Spec.BSTree.for_all, Spec.BSTree.contains]
      apply Iff.intro
      case mp => 
        intro ⟨p_x, left_forall, right_forall⟩ x
        intro this
        match this with
        | .inl (.inl curr_x) => subst curr_x; assumption
        | .inl (.inr x_in_left) =>  
          apply for_all_iff_contains.mp left_forall; assumption
        | .inr _ =>  
          apply for_all_iff_contains.mp right_forall; assumption
      case mpr => 
        intro forall_contained
        split_conjs
        · exact forall_contained curr (by simp)
        · apply for_all_iff_contains.mpr
          intro x x_in_sub
          exact forall_contained x (by simp [x_in_sub])
        · apply for_all_iff_contains.mpr
          intro x x_in_sub
          exact forall_contained x (by simp [x_in_sub])



theorem contains_spec(tree: BSTree Isize)(target: Isize)
: (toSpec tree).WellFormed l r
-> ∃ b,
    BSTreeIsize.contains tree target = Result.ok b ∧
    Spec.BSTree.contains ↑tree target = b
:= by
  intro well_formed
  rw [BSTreeIsize.contains]
  match tree with 
  | .Nil => simp [Spec.BSTree.contains]
  | .Node curr left right => 
      simp 
      obtain _|⟨_, _, _, left_inv, right_inv, non_empty, left_wf, right_wf⟩ := well_formed 
      --        ^↑ Why do I need to add these holes? TODO
      split_ifs
      case pos found =>
        subst found; simp [Spec.BSTree.contains]
      case pos not_curr curr_lt =>
        have ⟨b, h1, h2⟩:= contains_spec left target left_wf
        simp [h1, h2, Spec.BSTree.contains, not_curr]
        -- Now I need to prove that curr is not on `right`
        have not_in_right: (toSpec right).contains target = false := by
          clear b h1 h2
          apply for_all_iff_contains.mp at right_inv
          if h: (toSpec right).contains target then
            have x_right_bnd := right_inv target h
            simp [Spec.between] at x_right_bnd
            have ⟨x_lb, x_hb⟩ := x_right_bnd
            -- I now need the hypothesis that curr ≤ target ∧ target < curr -> False
            /- exfalso -/
            /- exact not_le_of_gt (curr_lt) x_lb -/
            -- NOTE: You shouldn't have to thing too much about arithmetic operations
            scalar_tac
          else
            simp [h]
        simp [not_in_right]
      case neg not_curr curr_ge =>
        have ⟨b, h1, h2⟩:= contains_spec right target right_wf
        simp [h1, h2, Spec.BSTree.contains, not_curr]
        have not_in_left: (toSpec left).contains target = false := by
          clear b h1 h2
          apply for_all_iff_contains.mp at left_inv
          if h: (toSpec left).contains target then
            have x_left_bnd := left_inv target h
            simp [Spec.between] at x_left_bnd
            have ⟨x_lb, x_hb⟩ := x_left_bnd
            scalar_tac
          else
            simp [h]
        simp [not_in_left]


theorem nil_of_wellformed_of_gt[BEq α][LawfulBEq α][LE α][DecidableLE α][IsTrans α (·≤·)][BoundedOrder α](tree: Spec.BSTree α)
: ¬ (l <= r) -> tree.WellFormed l r -> tree = .Nil
:= by
  intro l_gt_r
  intro tree_wf
  match tree with
  | .Nil => rfl
  | .Node .. =>
    obtain _|⟨_, _, _, left_inv, right_inv, non_empty, left_wf, right_wf⟩ := tree_wf
    simp at non_empty
    have ⟨lb, ub⟩ := non_empty
    have: l <= r := Trans.trans lb ub
    simp at *; contradiction
    

theorem insert_spec(tree: BSTree Isize)(value: Isize)
: (toSpec tree).WellFormed l r 
-> ∃ tree',
    BSTreeIsize.insert tree value = Result.ok tree' ∧
    Spec.BSTree.insert value ↑tree = ↑tree' ∧
    (toSpec tree).WellFormed (minOfLe.min l value) (maxOfLe.max r value)
:= by
  intro well_formed
  rw [BSTreeIsize.insert]
  cases tree
  case Nil => 
    simp [toSpec, Spec.BSTree.insert]
    apply Spec.BSTree.WellFormed.isEmpty
  case Node curr left right =>
    simp [toSpec, Spec.BSTree.insert]
    simp [toSpec] at well_formed
    obtain _|⟨_, _, _, left_inv, right_inv, nonempty, left_wf, right_wf⟩ := well_formed 
    simp at nonempty

    simp [for_all_iff_contains] at right_inv left_inv
    split_ifs <;> try (first | scalar_tac | contradiction) 
    case pos value_neq_curr curr_ge => 
      /- have curr_gt: ↑value < ↑curr := by scalar_tac -/
      progress as ⟨tree', tree'_spec, tree'_wf⟩
      simp [tree'_spec]
      simp [maxOfLe, curr_ge] at tree'_wf
      have: (value: Int) <= ↑r := by scalar_tac
      simp [maxOfLe, this]
      apply Spec.BSTree.WellFormed.isCompound
      case left_inv => 
        apply for_all_iff_contains.mpr
        intro x x_in_left
        have := left_inv x x_in_left
        simp [Spec.between, this]
      case right_inv => 
        apply for_all_iff_contains.mpr
        intro x x_in_right
        have := right_inv x x_in_right
        simp [Spec.between, this]
      case left_wf => 
        assumption
      case right_wf => 
        assumption
      case non_empty =>
        simp [Spec.between, maxOfLe]
        scalar_tac
    case pos _ curr_eq_value => 
      subst curr_eq_value
      simp [maxOfLe, minOfLe, nonempty]
      apply Spec.BSTree.WellFormed.isCompound <;>
        (try apply for_all_iff_contains.mpr) <;> 
        (try simp [Spec.between]) <;> 
        assumption
    case neg _ curr_gt => 
      progress as ⟨tree', tree'_spec, tree'_wf⟩
      simp [tree'_spec]
      have: curr <= (value: Int) := by apply Int.le_of_lt; assumption
      simp [minOfLe, this] at tree'_wf
      have: l <= (value: Int) := _root_.trans nonempty.left this
      simp [minOfLe, this]
      apply Spec.BSTree.WellFormed.isCompound
      case left_inv => 
        apply for_all_iff_contains.mpr
        intro x x_in_left
        have := left_inv x x_in_left
        simp [Spec.between, this]
      case right_inv => 
        apply for_all_iff_contains.mpr
        intro x x_in_right
        have := right_inv x x_in_right
        simp [Spec.between, this]
      case right_wf => assumption
      case left_wf => assumption
      case non_empty => simp [Spec.between, minOfLe]; scalar_tac
end Lemmas/- }}} -/
end TreeImpl/- }}} -/

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
