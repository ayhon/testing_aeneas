import Aeneas
import TestingAeneas.BSTree

open Aeneas.Std

namespace Spec/- {{{ -/
@[simp] def BSTree.height: BSTree α -> Nat
| Node _ left right => 1 + left.height.max right.height
| Nil => 0


@[simp] abbrev BSTree.balancingFactor: BSTree α -> Int
| Node _ left right => (left.height: Int) - right.height
| Nil => 0

/-
          Rotate right

         v₁             v₂ 
      v₂    C   -->   A    v₁ 
    A   B                 B  C
 
-/
def BSTree.rotateRight: BSTree α -> BSTree α
| Node v₁ (Node v₂ A B) C => Node v₂ A (Node v₁ B C)
| otherwise => otherwise

/-
          Rotate left

      v₁                  v₂  
    A    v₂    -->     v₁    C
        B  C         A   B    
 
-/
def BSTree.rotateLeft: BSTree α -> BSTree α
| Node v₁ A (Node v₂ B C) => Node v₂ (Node v₁ A B) C
| otherwise => otherwise

@[simp] def BSTree.balanced: BSTree α -> Prop
| Nil => true
| Node _ left right =>
    |(left.height: Int) - right.height| ≤ 1 ∧
    left.balanced ∧ right.balanced

@[simp] abbrev BSTree.is_avl[PartialOrder α][IsTotal α (·≤·)](tree: BSTree α): Prop :=
  tree.balanced ∧ tree.well_formed

def BSTree.rebalance(tree: BSTree α): BSTree α :=
  match tree, tree.balancingFactor with
  | Node value left right,  2 =>
    if left.balancingFactor = -1 then
      /-
            A           ⟨A⟩            
         ⟨C⟩  ᵈ  >>    B  ᵈ   >>     B
         ᵃ  B        C  ᶜ          C   A
           ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
      -/
      
      Node value left.rotateLeft right |>.rotateRight
    else if left.balancingFactor = 1 then
      /-
             ⟨A⟩
            B  ᵈ  >>     B
          C  ᶜ         C   A
         ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
      -/
      tree.rotateRight
    else tree
  | Node value left right, -2 => 
    if right.balancingFactor = 1 then
      /-
           A         ⟨A⟩           
         ᵃ  ⟨C⟩  >>  ᵃ  B    >>     B
           B  ᵈ       ᵇ  C        C   A
          ᵇ ᶜ           ᶜ ᵈ      ᵃ ᵇ ᶜ ᵈ
      -/
      Node value left right.rotateRight |>.rotateLeft
    else if right.balancingFactor = -1 then
      /-
         ⟨A⟩           
         ᵃ  B    >>     B
          ᵇ  C        C   A
            ᶜ ᵈ      ᵃ ᵇ ᶜ ᵈ
      -/
      tree.rotateLeft
    else tree
  | _, _ => tree

end Spec/- }}} -/

section Translation/- {{{ -/
open testing_aeneas
def testing_aeneas.AVLTree.toBS: AVLTree α -> Spec.BSTree α
| .Nil => .Nil
| .Node v left right .. => .Node v left.toBS right.toBS

instance: Coe (AVLTree α) (Spec.BSTree α) where coe := AVLTree.toBS
end Translation/- }}} -/

@[simp] def testing_aeneas.AVLTree.invariant: AVLTree α -> Prop
| .Nil => true
| .Node _ left right bf => 
    bf = (left.toBS.height - right.toBS.height : Int) ∧
    left.invariant ∧ right.invariant


section Lemmas/- {{{ -/
namespace AVLRefinement
open testing_aeneas hiding max min BSTree
open Spec

/- theorem valid_right_left_eq(curr: α)(left right: BSTree α) -/
/- : let tree := BSTree.Node curr left right -/
/-   left ≠ .Nil -> -/
/-   tree.rotateRight.rotateLeft = tree := by -/
/-   intro tree left_not_nil -/
/-   simp [BSTree.rotateLeft, tree] -/
/-   cases left <;> try contradiction -/
/-   simp [BSTree.rotateRight] -/

/- theorem valid_left_right_eq(curr: α)(left right: BSTree α) -/
/- : let tree := BSTree.Node curr left right -/
/-   right ≠ .Nil -> -/
/-   tree.rotateLeft.rotateRight = tree -/
/- := by -/
/-   intro tree right_not_nil -/
/-   simp [BSTree.rotateRight, tree] -/
/-   cases right <;> try contradiction -/
/-   simp [BSTree.rotateLeft] -/

/- theorem rotateLeft_preserves_wf[PartialOrder α][IsTotal α (·<=·)](tree: BSTree α) -/
/- : tree.well_formed -> tree.rotateLeft.well_formed -/
/- := by -/
/-   simp [BSTree.rotateLeft] -/
/-   split <;> simp -/
/-   case _ v₂ A v₁ B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E -/
/-     intro A_wf B_wf E_wf B_inv E_inv A_inv inner_inv -/
/-     have v_rel: v₂ < v₁ := by apply inner_inv; simp -/
/-     split_conjs <;> try assumption -/
/-     · intros; simp [*] -/
/-     · intros x pred -/
/-       obtain (h | h) | h := pred <;> try simp [*] -/
/-       exact Trans.trans (A_inv _ h) v_rel -/

/- theorem rotateRight_preserves_wf[PartialOrder α][IsTotal α (·<=·)](tree: BSTree α) -/
/- : tree.well_formed -> tree.rotateRight.well_formed -/
/- := by -- NOTE: symmetrical to rotateLeft_preserves_wf -/
/-   simp [BSTree.rotateRight] -/
/-   split <;> simp -/
/-   case _ v₁ v₂ A B E => -- Node v₁ (Node v₂ A B) E => Node v₂ A (Node v₁ B E) -/
/-     intro A_wf B_wf A_inv B_inv E_wf inner_inv E_inv -/
/-     have v_rel: v₂ < v₁ := by apply inner_inv; simp -/
/-     split_conjs <;> try assumption -/
/-     · intros; simp [*] -/
/-     · intros x pred -/
/-       obtain (h | h) | h := pred <;> try simp [*] -/
/-       exact Trans.trans v_rel (E_inv _ h) -/

/- theorem height_node(tree: BSTree α) -/
/- : tree.height > 0 ↔ tree ≠ .Nil -/
/- := by cases tree <;> simp -/

@[pspec]
theorem max_spec(a b: I8)
: ∃ c,
  testing_aeneas.max a b = Result.ok c ∧
  c.val = max a.val b.val
:= by
  simp [testing_aeneas.max]
  if a > b then
    exists a; simp; scalar_tac
  else
    exists b; simp; scalar_tac

@[pspec]
theorem min_spec(a b: I8)
: ∃ c,
  testing_aeneas.min a b = Result.ok c ∧
  c.val = min a.val b.val
:= by -- NOTE: symmetrical to max_spec
  simp [testing_aeneas.min]
  if a < b then
    exists a; simp; scalar_tac
  else
    exists b; simp; scalar_tac

theorem balancing_factor_update_rotateLeft(l m r: Int)
: let bf_out := l - max m r - 1
  let bf_in  := m - r
  let bf_4 := l - m
  let bf_3 := 1 + max l m - r
  bf_4 = bf_out - bf_in ⊓ 0 + 1 
  ∧ bf_3 = 1 + bf_in + bf_4 ⊔ 0
:= by scalar_tac

theorem balancing_factor_update_rotateRight(l m r: Int)
: let bf_out := 1 + max l m - r
  let bf_in  := l - m
  let bf_4 := m - r
  let bf_3 := l - max m r - 1
  bf_4 = bf_out - bf_in ⊔ 0 - 1 
  ∧ bf_3 = bf_in + bf_4 ⊓ 0 - 1
:= by scalar_tac

@[pspec]
theorem rotateLeft_spec(tree: AVLTree Isize)
: ∃ tree',
    AVLTreeIsize.rotateLeft tree = .ok tree' ∧
    (tree: BSTree Isize).rotateLeft = tree'
:= sorry

@[pspec]
theorem rotateRight_spec(tree: AVLTree Isize)
: ∃ tree',
    AVLTreeIsize.rotateRight tree = .ok tree' ∧
    (tree: BSTree Isize).rotateRight = tree'
:= sorry

@[pspec]
theorem rebalance_spec(tree: AVLTree Isize)
: ∃ tree',
    AVLTreeIsize.rebalance tree = .ok tree' ∧
    tree.toBS.rebalance = tree'.toBS
:= sorry

theorem rebalance_correct[PartialOrder α][IsTotal α (·≤·)](value: α)(left right: BSTree α)
: left.is_avl
-> right.is_avl
-> (BSTree.Node v left right).well_formed
-> |(left.height - right.height: Int)| = 2
-> (BSTree.Node v left right).rebalance.is_avl
:= sorry

@[pspec]
theorem insert_spec(tree: AVLTree Isize)(value: Isize)
: tree.toBS.is_avl
-> ∃ tree' tree'',
    AVLTreeIsize.insert tree value = .ok tree' ∧
    tree.toBS.insert value = tree'' ∧
    tree''.is_avl ∧
    tree'.toBS = tree''.rebalance -- The condition |tree.balancingFactor| <= 1 implies tree''.rebalance = tree''
:= sorry

theorem insert_height[BEq α][LE α][LT α][DecidableLT α](value: α)(tree: BSTree α)
: (tree.insert a |>.height) <= tree.height + 1
:= sorry

theorem contains_spec(tree: AVLTree Isize)(target: Isize)
: ∃ b,
    AVLTreeIsize.contains tree target = .ok b ∧
    b = tree.toBS.contains target
:= sorry

end AVLRefinement
end Lemmas/- }}} -/
