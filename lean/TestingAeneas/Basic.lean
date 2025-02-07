import Aeneas
import TestingAeneas.Definitions

open Aeneas.Std

namespace Lemmas
  open testing_aeneas

  def toLeafList_aux: testing_aeneas.Tree A -> List A -> List A
  | .Leaf a, aux => a :: aux
  | .Branch lhs rhs, aux => 
      let rhs_list := toLeafList_aux rhs aux
      toLeafList_aux lhs rhs_list

  abbrev toLeafList'(tree: testing_aeneas.Tree A): List A := toLeafList_aux tree []
  -- NOTE: While this implementation is more efficient, it makes proving things harder.

  def toLeafList: testing_aeneas.Tree A -> List A
  | .Leaf a => [a]
  | .Branch lhs rhs => toLeafList lhs ++ toLeafList rhs

  /- @[pspec] -/
  theorem rev_spec'{A: Type}(tree: testing_aeneas.Tree A)
  : ∃ tree',
      tree.rev = .ok tree' ∧
      List.reverse (toLeafList tree) = toLeafList tree'
  := by
    rw [testing_aeneas.Tree.rev]
    match tree with
    | .Leaf a => 
      simp [toLeafList]
    | .Branch lhs rhs =>
      simp
      progress as ⟨rhs_rev, rhs_rev_spec⟩
      progress as ⟨lhs_rev, lhs_rev_spec⟩
      simp [testing_aeneas.Tree.branch]
      simp [toLeafList]
      simp [lhs_rev_spec, rhs_rev_spec]
  

  theorem rev_involution'{A: Type}(tree: testing_aeneas.Tree A)
  : do {(<-tree.rev).rev} = Result.ok tree := by
    progress with rev_spec' as ⟨tree_rev, tree_rev_spec⟩
    progress with rev_spec' as ⟨tree_rev_rev, tree_rev_rev_spec⟩
    sorry

  -- The previous invariant is not enough, since `rev` also guarantees that the shape of
  -- the tree stays the same. 

  -- IDEA: I could define a tree in Lean and simply have the `spec` state that I have a
  --       translation from one version to the other. However, using this approach more
  --       generally would require that I implement the same functions twice, which is
  --       not ideal. 
  --       However, this is much less of an issue if the definitions I translate them to
  --       are simpler and easier to reason about (without worrying about them being
  --       inefficient).
  --       In fact, mathlib already has a simple `Tree` definition which fits my needs
  abbrev MathLibTree := _root_.Tree

  def toTree: testing_aeneas.Tree A -> MathLibTree (Option A)
  | .Leaf a => .node (some a) .nil .nil
  | .Branch lhs rhs => .node (none) (toTree lhs) (toTree rhs)

  def rev: MathLibTree α -> MathLibTree α
  | .node v lhs rhs => .node v (rev rhs) (rev lhs)
  | .nil => .nil

  @[pspec]
  theorem rev_spec{A: Type}(tree: testing_aeneas.Tree A)
  : ∃ tree',
      tree.rev = .ok tree' ∧
      rev (toTree tree) = toTree tree'
  := by
    rw [testing_aeneas.Tree.rev]
    match tree with
    | .Leaf a => 
      simp [toTree, rev]
    | .Branch lhs rhs =>
      simp [testing_aeneas.Tree.branch]
      progress with rev_spec as ⟨rhs_rev, rhs_rev_spec⟩
      progress with rev_spec as ⟨lhs_rev, lhs_rev_spec⟩
      simp [toTree, rev]
      simp [rhs_rev_spec, lhs_rev_spec]

  theorem toTree_equiv{A: Type}(tree tree': testing_aeneas.Tree A)
  : toTree tree = toTree tree' ↔ tree = tree'
  := by
    apply Iff.intro
    case mpr => intro; congr
    intro toTree_eq
    match tree, tree' with
    | .Leaf a, .Leaf a' =>
        simp [toTree] at *; assumption
    | .Leaf _, .Branch _ _ 
    | .Branch _ _, .Leaf _ =>
        simp [toTree] at *
    | .Branch lhs rhs, .Branch lhs' rhs' =>
        simp [toTree] at *
        split_conjs
        · exact toTree_equiv _ _ |>.mp toTree_eq.left
        · exact toTree_equiv _ _ |>.mp toTree_eq.right


  theorem Mathlib_rev_involution{A: Type}(tree: MathLibTree A)
  : rev (rev tree) = tree := match tree with
  | .nil => by simp [rev]
  | .node v lhs rhs => by
      simp [rev]; split_conj <;> apply Mathlib_rev_involution

  theorem rev_involution{A: Type}(tree: testing_aeneas.Tree A)
  : do {(<-tree.rev).rev} = Result.ok tree := by
    progress with rev_spec as ⟨tree_rev, tree_rev_spec⟩
    progress with rev_spec as ⟨tree_rev_rev, tree_rev_rev_spec⟩
    apply toTree_equiv _ _ |>.mp
    rw [<-tree_rev_rev_spec, <-tree_rev_spec]
    apply Mathlib_rev_involution

  -- The proof of rev_involution is trivial once the Mathlib_rev_involution
  -- definition is obtained.

end Lemmas
