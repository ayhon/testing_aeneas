import TestingAeneas.Definitions

import Aeneas
open Aeneas.Std

namespace Spec

inductive BSTree(α: Type) where
| Nil : BSTree α
| Node(v: α)(left right: BSTree α): BSTree α

def BSTree.contains[BEq α]: BSTree α -> α -> Bool
| Nil, _=> false
| Node curr left right, target => 
    curr == target || left.contains target || right.contains target

def BSTree.insert[Ord α](value: α): BSTree α -> BSTree α
| Nil => Node value Nil Nil
| Node curr left right =>
  match compare value curr with
  | .lt => Node curr (left.insert value) right
  | _   => Node curr left (right.insert value)

abbrev between[LE α][DecidableLE α](lo hi value: α) := decide (lo <= value ∧ value <= hi)

def BSTree.for_all(condition: α -> Bool): BSTree α -> Bool
| Nil => True
| Node curr left right =>
  condition curr && left.for_all condition && right.for_all condition

inductive BSTree.WellFormed[LE α][DecidableLE α][BoundedOrder α]: BSTree α -> α -> α -> Prop where
  | isEmpty : BSTree.Nil.WellFormed ⊥ ⊤
  | isCompound(v: α)
    (left right: BSTree α)
    (left_inv:  left.for_all <| between l v)
    (right_inv: right.for_all <| between v r)
    : left.WellFormed l v -> right.WellFormed v r -> (Node v left right).WellFormed l r

end Spec

namespace Lemmas
open testing_aeneas

section Translation

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
end Translation

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
      obtain _|⟨_, _, _, left_inv, right_inv, left_wf, right_wf⟩ := well_formed 
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


theorem insert_spec(tree: BSTree Isize)(a: Isize)
: (toSpec tree).WellFormed l r 
-> ∃ tree',
    BSTreeIsize.insert tree a = Result.ok tree' ∧
    Spec.BSTree.insert a ↑tree = ↑tree' ∧
    (toSpec tree).WellFormed (min l a) (max r a)
:= sorry

end Lemmas
