import Aeneas
import TestingAeneas.BSTree
import TestingAeneas.AVLTree
import TestingAeneas.Definitions

set_option maxHeartbeats 1000000
/- set_option maxRecDepth 1000000 -/

open Aeneas Std

section Operations/- {{{ -/
namespace Spec

def BSTree.rebalance'(tree: BSTree α): BSTree α :=
  match tree with
  | Nil => tree
  | Node value left right =>
      let bf1 := tree.balancingFactor
      if bf1 = 2 then
        match left with
        | Nil => tree 
        | Node .. =>
          let bf2 := left.balancingFactor
          if bf2 = -1 then
            /-
                  X           ⟨X⟩      linux      
               ⟨Z⟩  ᵈ  >>    Y  ᵈ   >>     Y
               ᵃ  Y        Z  ᶜ          Z   X
                 ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
            -/
            
            Node value left.rotateLeft right |>.rotateRight
          else 
            /-
                   ⟨X⟩
                  Y  ᵈ  >>     Y
                Z  ᶜ         Z   X
               ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
            -/
            tree.rotateRight
      else if bf1 = -2 then
        match right with
        | Nil => tree
        | Node .. =>
          let bf2 := right.balancingFactor
          if bf2 = 1 then
            /-
                 X         ⟨X⟩           
               ᵃ  ⟨Z⟩  >>  ᵃ  Y    >>     Y
                 Y  ᵈ       ᵇ  Z        Z   X
                ᵇ ᶜ           ᶜ ᵈ      ᵃ ᵇ ᶜ ᵈ
            -/
            Node value left right.rotateRight |>.rotateLeft
          else
            /-
               ⟨X⟩           
               ᵃ  Y    >>     Y
                ᵇ  Z        Z   X
                  ᶜ ᵈ      ᵃ ᵇ ᶜ ᵈ
            -/
            tree.rotateLeft
      else tree

def BSTree.popLeftmost{α: Type}[LT α][DecidableLT α][Inhabited α]: BSTree α -> BSTree α × α
| Nil => @panic _ (instInhabitedProd) "Unreachable"
| Node value Nil right => (right, value)
| Node value left right => 
  let (left', popped) := left.popLeftmost
  let res := Node value left' right
  (res.rebalance', popped)

def BSTree.delete_rebalance[LT α][DecidableLT α][Inhabited α](value: α): BSTree α -> BSTree α
| Nil => Nil
| Node curr left right =>
  if value < curr then
    Node curr (left.delete_rebalance value) right |>.rebalance'
  else if curr < value then
    Node curr left (right.delete_rebalance value) |>.rebalance'
  else -- value == curr
    match left, right with
    | Nil, right => right
    | left, Nil => left
    | left, right => 
      let (right', leftmost) := right.popLeftmost
      let res := Node leftmost left right'
      res.rebalance'

end Spec
end Operations/- }}} -/

section Lemmas /- {{{ -/
open testing_aeneas hiding max min BSTree
attribute [-simp] Bool.exists_bool

namespace Spec

section Rebalance'/- {{{ -/

@[simp] theorem BSTree.rebalance'_toSet[LinearOrder α][IsTotal α (·≤·)](tree: BSTree α)
: tree.toSet = tree.rebalance'.toSet
:= by/- {{{ -/
  cases tree <;> simp [BSTree.rebalance']
  case Node value left right =>
    split -- Here there are actually 3 cases
    case' isTrue => split_ifs <;> cases left -- First case, destructure left
    case' isFalse => split
    case' isTrue => split_ifs <;> cases right -- second case, destructure right
    -- Third case, can be solved through `simp`
    all_goals simp [BSTree.rotateLeft_toSet, BSTree.rotateRight_toSet]/- }}} -/


theorem BSTree.rebalance'.preserves_inv_left{value: Isize}{left right: AVLTree Isize}{bf: I8}
: let tree := AVLTree.Node value left right bf
  tree.invariant
-> tree.toBS.balancingFactor = 2 
-> left.toBS.balanced -- left.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1)
-> right.toBS.balanced -- right.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1)
-> ∃ tree' height_decrease,
    AVLTreeIsize.rebalance_with_height_decrease tree = .ok (tree', height_decrease) ∧
    tree.toBS.rebalance' = tree'.toBS ∧
    tree'.invariant ∧ -- TODO: These don't actually depend on AVLTreeIsize, but just on BSTree. Rework them.
    tree'.toBS.balanced ∧ -- tree'.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1) ∧
    (if height_decrease then tree'.toBS.height = tree.toBS.height - 1
                        else tree'.toBS.height = tree.toBS.height)
:= by /- {{{ -/
  sorry
  /-
  intro tree tree_inv bf_2 left_bnd right_bnd
  have ⟨bf_def, left_inv, right_inv⟩ := tree_inv
  unfold tree at *
  simp [AVLTreeIsize.rebalance_with_height_decrease.eq_def]

  have: bf = 2#i8 := by -- NOTE: Spiritually this should be just `scalar_tac`.
    simp only [<-bf_2, bf_def]
    scalar_tac
  simp only [AVLTree.toBS] at bf_def
  simp only [BSTree.rebalance', bf_def]
  simp [this]


  -- The core of the proof relies on the fact that, since we have restricted the values
  -- that tree.balancingFactor and left.balancingFactor can take, we can actually 
  -- determine the values of the heights of the relevant subtrees. In particular, we
  -- can write them as a function of a shared value H.
  generalize right_H: right.toBS.height = H at *
  -- We write subtree_H to refer to the proposition that relates subtree's height with H
  have left_H : left.toBS.height = H + (2: Int) := by 
    simp [Spec.balancingFactor_Node, this] at tree_inv
    omega -- scalar_tac doesn't seem to work

  cases left
  case Nil => 
    -- Left cannot be nil, because then its balancingFactor would be 0, which we disallow!
    simp [AVLTreeIsize.balance_factor, Spec.balancingFactor_Node] at bf_2
    scalar_tac
  case Node v1 left1 right1 bf1 =>
    simp at left_inv
    have ⟨bf1_def, left1_inv, right1_inv⟩ := left_inv
    simp [bf1_def] at left_bnd
    simp [AVLTreeIsize.balance_factor, bf1_def]

    -- Depending on the balancing factor of left, we encounter ourselves in the LEFT-LEFT
    -- or LEFT-RIGHT case. We handle these separately
    if bf1_is_n1: bf1 = (-1)#i8 then/- {{{ -/
      simp [bf1_is_n1] at *
      -- This is the LEFT-RIGHT case, which corresponds to the following shape
      /-
               ┌────tree────┐
               │     H+3    │
               ▼            ▼
        ┌────left───┐     right
        │     H+2   │       H
        ▼           ▼
      left1    ┌──right1──┐
        H      │   H+1    │
               ▼          ▼
             left2      right2
              ≤H          ≤H
      -/
      have left1_H: left1.toBS.height = H:= by omega
      have right1_H: right1.toBS.height = H + 1 := by omega
      obtain ⟨left1_bnd, right1_bnd⟩ := left_bnd

      -- We can apply the spec of rotateLeft to get to the following
      -- intermediary step, which is similar to the LEFT-LEFT case.
      cases right1
      case Nil =>
        -- This can't be nil, because otherwise left.balancingFactor could never be negative!
        simp [bf1_is_n1] at bf1_def
      case Node v2 left2 right2 bf2 =>
        simp [BSTree.rotateLeft] at left_H right1_bnd ⊢
        have: left2.toBS.height ⊔ right2.toBS.height = H := by omega
        obtain ⟨bf2_bal, left2_bnd, right2_bnd⟩ := right1_bnd

        progress with rotateLeft.spec as ⟨left', left'_spec, left'_inv⟩
        · simp [*, boundedBalancingFactor_expand (by decide: 1 < 2)]
        -- After this operation, this is the current state of our tree
        /-
                      ┌────tree────┐
                      │     H+3    │
                      ▼            ▼
               ┌───right1──┐     right
               │   (left') │       H
               ▼     H+2   ▼
          ┌───left───┐   right2
          │ (left1') │  (right1')
          ▼   H+1    ▼     ≤H
        left1      left2
        (left2')   (right2')
          H          ≤H
        -/
        simp only [BSTree.rotateLeft] at left'_spec
        -- Now we can simply apply the rotateRight spec and solve the goal through simplification
        progress as ⟨tree', tree'_spec, tree'_inv⟩
        · simp [*, BSTree.rotateLeft]; omega
        · simp [*, boundedBalancingFactor_expand (by decide: 1 < 2)]; omega
        simp [*, BSTree.rotateRight, Nat.max]
        scalar_tac/- }}} -/
    else if bf1_is_1: bf1 = 1#i8 then/- {{{ -/
      simp [bf1_is_1] at *
      -- We're in the LEFT-LEFT case. This is the general shape of this case
      /-
               ┌──tree──┐
               ▼        ▼
           ┌─left─┐    right                ┌─────left─────┐
           ▼      ▼      H                  ▼              ▼
        ┌left1┐ right1        =======>  ┌─left1─┐      ┌─tree─┐
        │     │   H                     ▼       ▼      ▼      ▼
        ▼     ▼                        left2  right2 right1  right
      left2 right2                      ≤H      ≤H     H       H
       ≤H     ≤H
      -/
      have right1_H: right1.toBS.height = H     := by omega
      have  left1_H: left1.toBS.height  = H + 1 := by omega

      -- This case can be solved directly by using the rotateRight spec
      -- However, to do so we need to provide some specific preconditions
      -- which require manipulating the hypothesis a bit.
      obtain ⟨left1_bnd, right1_bnd⟩ := left_bnd
      progress as ⟨tree', tree'_spec,tree'_inv⟩
      · simp [*]; omega
      · simp [*, boundedBalancingFactor_expand (by simp : 1 < 2)]
        omega
      simp only [BSTree.rotateRight] at tree'_spec
      simp [*, BSTree.rotateRight, balancingFactor_Node, BSTree.rebalance, Nat.max]
      split_conj <;> scalar_tac/- }}} -/
    else/- {{{ -/
      have bf1_is_0: bf1 = 0#i8 := by scalar_tac
      simp [bf1_is_0]
      have right1_H: right1.toBS.height = left1.toBS.height := by simp [bf1_is_0] at bf1_def; omega
      have  left1_H: left1.toBS.height  = H + 1 := by simp [right1_H] at left_H; omega

      obtain ⟨left1_bnd, right1_bnd⟩ := left_bnd
      progress as ⟨tree', tree'_spec,tree'_inv⟩
      · simp [*]; omega
      · simp [*, boundedBalancingFactor_expand (by simp : 1 < 2)]
        omega
      simp [BSTree.rotateRight] at tree'_spec
      simp [*, BSTree.rotateRight, balancingFactor_Node, BSTree.rebalance, Nat.max]
      scalar_tac/- }}} -//- }}} -/
-/

theorem BSTree.rebalance'.preserves_inv_right{value: Isize}{left right: AVLTree Isize}{bf: I8}
: let tree := AVLTree.Node value left right bf
  tree.invariant
-> tree.toBS.balancingFactor = -2
-> left.toBS.balanced
-> right.toBS.balanced
-> ∃ tree' height_decrease,
    AVLTreeIsize.rebalance_with_height_decrease tree = .ok (tree',height_decrease) ∧
    tree.toBS.rebalance' = tree'.toBS ∧
    tree'.invariant ∧
    tree'.toBS.balanced ∧
    (if height_decrease then tree'.toBS.height = tree.toBS.height - 1
                        else tree'.toBS.height = tree.toBS.height)
:= by /- {{{ -/
  sorry/-
  intro tree tree_inv bf_2 left_bnd right_bnd
  have ⟨bf_def, left_inv, right_inv⟩ := tree_inv
  unfold tree at *
  simp [AVLTreeIsize.rebalance_with_height_decrease.eq_def]

  have: bf = (-2)#i8 := by -- NOTE: Spiritually this should be just `scalar_tac`.
    simp only [<-bf_2, bf_def]
    scalar_tac
  simp only [AVLTree.toBS] at bf_def
  simp only [BSTree.rebalance', bf_def]
  simp [this]


  -- The core of the proof relies on the fact that, since we have restricted the values
  -- that tree.balancingFactor and left.balancingFactor can take, we can actually 
  -- determine the values of the heights of the relevant subtrees. In particular, we
  -- can write them as a function of a shared value H.
  generalize left_H: left.toBS.height = H at *
  -- We write subtree_H to refer to the proposition that relates subtree's height with H
  have right_H : right.toBS.height = H + (2: Int) := by 
    simp [Spec.balancingFactor_Node, this] at tree_inv
    omega -- scalar_tac doesn't seem to work

  cases right
  case Nil => 
    -- Left cannot be nil, because then its balancingFactor would be 0, which we disallow!
    simp [AVLTreeIsize.balance_factor, Spec.balancingFactor_Node] at bf_2
  case Node v1 left1 right1 bf1 =>
    simp at right_inv
    have ⟨bf1_def, left1_inv, right1_inv⟩ := right_inv
    simp [bf1_def] at right_bnd
    simp [AVLTreeIsize.balance_factor, bf1_def]

    cases bf1_is_1: decide (bf1 = 1#i8)
    case true =>/- {{{ -/
      simp at bf1_is_1; simp [bf1_is_1] at *

      have right1_H: right1.toBS.height = H:= by omega
      have left1_H: left1.toBS.height = H + 1 := by omega
      obtain ⟨left1_bnd, right1_bnd⟩ := right_bnd

      -- We can apply the spec of rotateLeft to get to the following
      -- intermediary step, which is similar to the LEFT-LEFT case.
      cases left1
      case Nil =>
        -- This can't be nil, because otherwise left.balancingFactor could never be negative!
        simp [bf1_is_1] at bf1_def
        scalar_tac
      case Node v2 left2 right2 bf2 =>
        simp [BSTree.rotateRight] at right_H left1_bnd ⊢
        have: left2.toBS.height ⊔ right2.toBS.height = H := by omega
        obtain ⟨bf2_bal, left2_bnd, right2_bnd⟩ := left1_bnd

        progress with rotateRight.spec as ⟨right', right'_spec, right'_inv⟩
        · simp [*, boundedBalancingFactor_expand (by decide: 1 < 2)]

        simp only [BSTree.rotateRight] at right'_spec
        -- Now we can simply apply the rotateRight spec and solve the goal through simplification
        progress as ⟨tree', tree'_spec, tree'_inv⟩
        · simp [*, BSTree.rotateRight]; omega
        · simp [*, boundedBalancingFactor_expand (by decide: 1 < 2)]; omega
        simp [*, BSTree.rotateLeft, Nat.max]
        scalar_tac/- }}} -/
    cases bf1_is_n1: decide $ bf1 = (-1)#i8
    case true => /- {{{ -/
      simp at bf1_is_n1; simp [bf1_is_n1] at *
      -- We're in the LEFT-LEFT case. This is the general shape of this case
      /-
               ┌──tree──┐
               ▼        ▼
           ┌─left─┐    right                ┌─────left─────┐
           ▼      ▼      H                  ▼              ▼
        ┌left1┐ right1        =======>  ┌─left1─┐      ┌─tree─┐
        │     │   H                     ▼       ▼      ▼      ▼
        ▼     ▼                        left2  right2 right1  right
      left2 right2                      ≤H      ≤H     H       H
       ≤H     ≤H
      -/
      have  left1_H: left1.toBS.height  = H     := by omega
      have right1_H: right1.toBS.height = H + 1 := by omega

      -- This case can be solved directly by using the rotateRight spec
      -- However, to do so we need to provide some specific preconditions
      -- which require manipulating the hypothesis a bit.
      obtain ⟨left1_bnd, right1_bnd⟩ := right_bnd
      progress as ⟨tree', tree'_spec,tree'_inv⟩
      · simp [*]; omega
      · simp [*, boundedBalancingFactor_expand (by simp : 1 < 2)]
        omega
      simp only [BSTree.rotateLeft] at tree'_spec
      simp [*, BSTree.rotateLeft, balancingFactor_Node, BSTree.rebalance, Nat.max]
      split_conj <;> scalar_tac/- }}} -/
    case false =>/- {{{ -/
      have bf1_is_0: bf1 = 0#i8 := by 
        simp only [decide_eq_false_iff_not, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq,
          Int.reduceNeg] at bf1_is_1 bf1_is_n1
        scalar_tac
      simp [bf1_is_0]
      have right1_H: right1.toBS.height = left1.toBS.height := by simp [bf1_is_0] at bf1_def; omega
      have  left1_H: left1.toBS.height  = H + 1 := by simp [right1_H] at right_H; omega

      obtain ⟨left1_bnd, right1_bnd⟩ := right_bnd
      progress as ⟨tree', tree'_spec,tree'_inv⟩
      · simp [*]; omega
      · simp [*, boundedBalancingFactor_expand (by simp : 1 < 2)]
        omega
      simp [BSTree.rotateRight] at tree'_spec
      simp [*, BSTree.rotateLeft, balancingFactor_Node, BSTree.rebalance, Nat.max]
      checkpoint scalar_tac/- }}} -//- }}} -/
-/

theorem BSTree.rebalance'.preserves_wf[LinearOrder α][IsTotal α (·≤·)]{tree: BSTree α}
: tree.well_formed
-> tree.rebalance'.well_formed
:= by/- {{{ -/
  cases tree 
  case Nil => simp [BSTree.rebalance']
  case Node value left right =>
    simp only [BSTree.rebalance']
    simp
    intro left_wf right_wf left_bs right_bs
    if bf_2: left.height - right.height = (2 : Int) then
      simp [bf_2]
      -- In this case, we look at the left
      cases left
      case Nil => simp_all
      case Node v1 left1 right1 =>
        simp at left_bs ⊢
        have ⟨left1_wf, right1_wf, left1_bs, right1_bs⟩ := left_wf
        have v1_value: v1 < value := by apply left_bs; simp

        if bf1_n1: (left1.height - right1.height : Int) = -1 then
          -- LEFT-RIGHT case
          simp [bf1_n1]

          cases right1
          case Nil => 
            simp [BSTree.rotateRight, BSTree.rotateLeft]
            split_conjs <;> try assumption

            -- NOTE: Closing dependent arrows{{{
            intro x x_right
            trans value <;> try assumption
            apply right_bs; assumption/- }}} -/
          case Node v2 left2 right2 =>
            have ⟨left2_wf, righ2_wf, left2_bs, right2_bs⟩ := right1_wf
            have v1_v2 : v1 < v2 := by exact right1_bs v2 (by simp)
            have v2_value : v2 < value := by exact left_bs v2 (by simp)

            simp [BSTree.rotateRight, BSTree.rotateLeft, *]

            -- NOTE: Closing dependent arrows{{{
            split_conjs <;> try assumption
            · intro x x_left2; apply right1_bs; simp [*]
            · intro x x_right2; apply left_bs; simp [*]
            · intro x h
              obtain (h | h) | h := h
              · rw [h]; assumption
              · trans v1 <;> try assumption
                apply left1_bs; assumption
              · apply left2_bs; assumption
            · intro x h
              obtain (h | h) | h := h
              · rw [h]; assumption
              · apply right2_bs; assumption
              · trans value <;> try assumption
                apply right_bs; assumption/- }}} -/
        else -- if bf1_1: (left1.height - right1.height : Int) = 1 then
          -- LEFT-LEFT case
          simp [bf1_n1, BSTree.rotateRight]
          split_conjs <;> simp_all -- The problem with this simp_all is that it deletes v1_value

          have v1_value: v1 < value := left_bs _ (by simp)

          -- NOTE: Closing dependent arrows{{{
          intro x hyp 
          obtain (h | h) | h := hyp
          · rw [h]; assumption
          · apply right1_bs; assumption
          · trans value <;> try assumption
            apply right_bs; assumption/- }}} -/

    else if bf_n2: (left.height - right.height : Int) = -2 then
      simp [bf_n2]
      -- In this case we look at the right.
      -- It's symmetrical to the previous branch
      cases right
      case Nil => simp; split_conjs <;> assumption
      case Node v1 left1 right1 =>
        simp at right_bs ⊢
        have ⟨left1_wf, right1_wf, left1_bs, right1_bs⟩ := right_wf
        have value_v1: value < v1 := by apply right_bs; simp

        if bf1_n1: (left1.height - right1.height : Int) = 1 then
          -- RIGHT-LEFT case
          simp [bf1_n1]

          cases left1
          case Nil => 
            simp [BSTree.rotateRight, BSTree.rotateLeft]
            split_conjs <;> try assumption

            -- NOTE: Closing dependent arrows{{{
            intro x x_right
            trans value <;> try assumption
            apply left_bs; assumption/- }}} -/
          case Node v2 left2 right2 =>
            have ⟨left2_wf, righ2_wf, left2_bs, right2_bs⟩ := left1_wf
            have v1_v2 : v2 <v1  := by exact left1_bs v2 (by simp)
            have v2_value : value < v2 := by exact right_bs v2 (by simp)

            simp [BSTree.rotateRight, BSTree.rotateLeft, *]
            -- NOTE: Closing dependent arrows{{{
            split_conjs <;> try assumption
            · intro x x_left2; apply right_bs; simp [*]
            · intro x x_right2; apply left1_bs; simp [*]
            · intro x h
              obtain (h | h) | h := h
              · rw [h]; assumption
              · trans value <;> try assumption
                apply left_bs; assumption
              · apply left2_bs; assumption
            · intro x h
              obtain (h | h) | h := h
              · rw [h]; assumption
              · apply right2_bs; assumption
              · trans v1 <;> try assumption
                apply right1_bs; assumption/- }}} -/
        else -- if bf1_1: (left1.height - right1.height : Int) = -1 then
          -- RIGHT-RIGHT case
          simp [bf1_n1, BSTree.rotateLeft]
          split_conjs <;> simp_all

          have v1_value: value < v1 := right_bs _ (by simp)

          -- NOTE: Closing dependent arrows{{{
          intro x hyp
          obtain (h | h) | h := hyp
          · rw [h]; assumption
          · trans value <;> try assumption
            apply left_bs; assumption
          · apply left1_bs; assumption/- }}} -/
    else
      simp [bf_n2, bf_2]
      split_conjs <;> assumption/- }}} -/

theorem BSTree.rebalance'.id_if_balanced{value: Isize}{left right: AVLTree Isize}{bf: I8}
: let tree := AVLTree.Node value left right bf
  tree.invariant
→ tree.toBS.balanced
→ ∃ tree' _hd,
  AVLTreeIsize.rebalance_with_height_decrease tree = .ok (tree', _hd) ∧
  tree.toBS.rebalance = tree' ∧
  tree'.invariant
:= by/- {{{ -/
  intro tree ⟨bf_def, left_inv, right_inv⟩ ⟨bf_ne_2, _⟩
  simp at bf_def
  rw [AVLTreeIsize.rebalance_with_height_decrease]
  simp [tree, balancingFactor_Node, bf_def] at bf_ne_2
  have: ¬ bf.val = 2 := by scalar_tac
  have: ¬ bf.val = -2 := by scalar_tac
  simp [BSTree.rebalance, tree, bf_def, *]/- }}} -/

end Rebalance'/- }}} -/

section Delete/- {{{ -/

theorem BSTree.popLeftmost_contains[LinearOrder α][DecidableLT α][Inhabited α]
{value: α}{tree left right: BSTree α}
: tree = .Node value left right
→ let popped := tree.popLeftmost.2
  popped ∈ tree.toSet
:= by /- {{{ -/
  intro popped
  simp [popped, BSTree.popLeftmost]
  cases left_def:left
  case Nil => 
    simp [popped, BSTree.popLeftmost]
  case Node value1 left1 right1 =>
    simp only [BSTree.popLeftmost, ←left_def]
    left; right
    apply popLeftmost_contains left_def/- }}} -/

theorem BSTree.delete_of_popLeftmost_of_wf[LinearOrder α][DecidableLT α][Inhabited α]
{tree: BSTree α}
: tree.well_formed
/- → tree.popLeftmost = (tree', popped) -/ 
→ tree.popLeftmost.1 = tree.delete_rebalance tree.popLeftmost.2
:= by/- {{{ -/
  cases tree
  case Nil => 
    simp [BSTree.popLeftmost, BSTree.delete_rebalance, panic, panicCore, default]
  case Node value left right =>
    cases left_def: left
    case Nil =>
      simp [BSTree.popLeftmost, BSTree.delete_rebalance]
    case Node value1 left1 right1 =>
      simp only [←left_def]
      simp [BSTree.popLeftmost, BSTree.delete_rebalance]
      intro left_wf right_wf left_bs right_bs
      generalize popped_def: (Spec.BSTree.Node value left right).popLeftmost.2 = popped

      have: popped < value := by
        apply left_bs popped
        simp only [left_def, BSTree.popLeftmost] at popped_def
        simp [←left_def] at popped_def
        subst popped_def
        exact popLeftmost_contains left_def
      simp [this]
      simp only [left_def, BSTree.popLeftmost] at popped_def ⊢
      /- obtain ⟨left'_spec, popped_value⟩ := tree'_spec -/
      simp [←left_def] at popped_def ⊢
      congr
      simp [←popped_def]
      exact delete_of_popLeftmost left_wf/- }}} -/

/- example(s: Set α)(x: α): x ∉ s → s \ {x} = s := by exact? -/

theorem BSTree.delete_rebalance.spec[LinearOrder α][DecidableLT α][Inhabited α]
{tree: BSTree α}(target: α)
: tree.is_avl
→ let tree' := tree.delete_rebalance target
  tree'.toSet = tree.toSet \ {target} ∧
  tree'.is_avl
:= by 
  intro ⟨tree_bal, tree_wf⟩ tree'
  cases tree
  case Nil => simp [tree', BSTree.delete_rebalance]
  case Node val left right =>
    obtain ⟨bf_bal,left_bal,right_bal⟩ := tree_bal
    have ⟨left_wf,right_wf,left_bs,right_bs⟩ := tree_wf

    simp [tree', BSTree.delete_rebalance]
    cases target_val: compare target val <;> simp [compare_iff] at target_val
    case eq => 
      -- We have found the element we want to delete
      subst target_val; simp
      cases left_def: left <;> cases right_def: right
      case Nil.Nil => simp
      -- We deal with the cases in which we shortcircuit the computation.
      case Nil.Node val1 left1 right1 |
           Node.Nil val1 left1 right1 =>
        simp_all
        ext x
        simp_all
        intro hyp
        apply ne_of_gt
        case Nil.Node => exact right_bs x hyp
        case Node.Nil => exact left_bs x hyp
      -- Otherwise, we deal with `left` and `right`, ignoring their decomposition.
      simp only [←left_def, ←right_def]
      simp [delete_of_popLeftmost_of_wf right_wf]
      split_conjs
      · -- NOTE: Reasoning over sets!
        have ⟨this,_⟩:= delete_rebalance.spec right.popLeftmost.2 ⟨right_bal, right_wf⟩
        simp [Set.insert_union, this, Set.insert_diff_singleton]
        rw [Set.union_comm]
        simp [←Set.insert_union]
        simp [Set.insert_union]
        have := BSTree.not_mem_value_of_wf (tree_wf)
        simp [Set.diff_singleton_eq_self this]
        simp [←Set.insert_union]
        simp [Set.insert_eq_self.mpr (popLeftmost_contains right_def)]
        simp [Set.union_comm]
      · 
        sorry
      · sorry
    case lt => 
      simp [target_val]
      sorry
    case gt => 
      simp [target_val]
      sorry

    obtain target_lt | target_val | target_gt := lt_trichotomy target val
    · simp [target_lt]
      
      sorry
    · substs target_val
      simp
      sorry

    · simp [target_gt, not_lt_of_lt target_gt]
      sorry

theorem testing_aeneas.AVLTreeIsize.deleteAndWarn.spec
{tree tree': AVLTree Isize}{target: Isize}
: tree.invariant
→ tree.toBS.is_avl
→ ∃ tree' height_decrease,
  AVLTreeIsize.deleteAndWarn tree target = Result.ok (tree', height_decrease) ∧
  tree'.toBS = tree.toBS.delete_rebalance target ∧
  tree'.invariant ∧
  if height_decrease then tree'.toBS.height = tree.toBS.height - 1
                     else tree'.toBS.height = tree.toBS.height

:= by sorry

end Delete/- }}} -/

end Spec
end Lemmas/- }}} -/
