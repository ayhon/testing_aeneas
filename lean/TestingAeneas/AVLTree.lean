import Aeneas
import TestingAeneas.BSTree

set_option maxHeartbeats 1000000

open Aeneas.Std

namespace Spec/- {{{ -/
section Operations/- {{{ -/
@[simp] def BSTree.height: BSTree α -> Nat
| Node _ left right => 1 + left.height.max right.height
| Nil => 0

def BSTree.balancingFactor: BSTree α -> Int
| Node _ left right => (left.height: Int) - right.height
| Nil => 0

theorem balancingFactor_Nil{α : Type}: (@BSTree.Nil α).balancingFactor = 0 := by rfl
@[simp] theorem balancingFactor_Node{value: α}{left right: BSTree α}: 
    (BSTree.Node value left right).balancingFactor = left.height - right.height := by rfl


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

-- NOTE: I don't make this definition [simp] because it's a bit finicky and not really
-- equational. I'd rather handle the unfoldings manually.
def BSTree.rebalance(tree: BSTree α): BSTree α :=
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
                  X           ⟨X⟩            
               ⟨Z⟩  ᵈ  >>    Y  ᵈ   >>     Y
               ᵃ  Y        Z  ᶜ          Z   X
                 ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
            -/
            
            Node value left.rotateLeft right |>.rotateRight
          else if bf2 = 1 then
            /-
                   ⟨X⟩
                  Y  ᵈ  >>     Y
                Z  ᶜ         Z   X
               ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
            -/
            tree.rotateRight
          else tree
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
          else if bf2 = -1 then
            /-
               ⟨X⟩           
               ᵃ  Y    >>     Y
                ᵇ  Z        Z   X
                  ᶜ ᵈ      ᵃ ᵇ ᶜ ᵈ
            -/
            tree.rotateLeft
          else tree
      else tree

def BSTree.insert_rebalance[LT α][DecidableLT α](value: α): BSTree α -> BSTree α
| Nil => Node value Nil Nil
| Node curr left right =>
  let res := 
    if value < curr then
      Node curr (left.insert_rebalance value) right
    else if curr < value then
      Node curr left (right.insert_rebalance value)
    else
      Node value left right -- since value = curr
  if res.balancingFactor.natAbs = 2 then
    res.rebalance
  else
    res
end Operations/- }}} -/

section Propositions/- {{{ -/
@[simp] def BSTree.all_subtrees(cond: BSTree α -> Prop): BSTree α -> Prop
| Nil => true
| tree@(Node _ left right) => cond tree ∧ left.all_subtrees cond ∧ right.all_subtrees cond

@[simp] abbrev BSTree.boundedBalancingFactor(bnd: Nat)(tree: BSTree α) :=
  tree.all_subtrees (·.balancingFactor.natAbs <= bnd)

@[simp] abbrev BSTree.balanced(tree: BSTree α) := tree.boundedBalancingFactor 1

@[simp] abbrev BSTree.is_avl[PartialOrder α][IsTotal α (·≤·)](tree: BSTree α): Prop :=
  tree.balanced ∧ tree.well_formed

end Propositions/- }}} -/
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
| tree@(.Node _ left right bf) => 
  tree.toBS.balancingFactor = bf ∧ left.invariant ∧ right.invariant

section Lemmas/- {{{ -/
namespace AVLRefinement
open testing_aeneas hiding max min BSTree
open Spec
attribute [local simp] AVLTree.toBS
attribute [-simp] Bool.exists_bool
/- attribute [-simp] exists_eq_left -/

section Auxiliary/- {{{ -/
@[pspec]
theorem max_spec(a b: I8)
: ∃ c,
  testing_aeneas.max a b = Result.ok c ∧
  c.val = max a.val b.val
:= by/- {{{ -/
  simp [testing_aeneas.max]
  if a > b then
    exists a; simp; scalar_tac
  else
    exists b; simp; scalar_tac/- }}} -/

@[pspec]
theorem min_spec(a b: I8)
: ∃ c,
  testing_aeneas.min a b = Result.ok c ∧
  c.val = min a.val b.val
:= by -- NOTE: symmetrical to max_spec{{{
  simp [testing_aeneas.min]
  if a < b then
    exists a; simp; scalar_tac
  else
    exists b; simp; scalar_tac/- }}} -/

@[pspec]
theorem negate_spec(a: I8)
: a > I8.min + 1
-> ∃ v,
    -.a = .ok v ∧ v = -a.val
:= by/- {{{ -/
  intro bnd
  have hMin: I8.min = -I8.max -1 := by simp [I8.min, I8.max]
  have hMax: I8.max  = -I8.min -1 := by simp [I8.min, I8.max]
  simp [HNeg.hNeg, Scalar.neg, -Scalar.check_bounds, Scalar.tryMk, Scalar.tryMkOpt, Scalar.cMin, Scalar.min, Scalar.cMax, Scalar.max]
  split <;> simp [*]
  case _ v heq =>
    simp at *
    obtain ⟨h, pp⟩ := heq
    simp [Scalar.ofIntCore] at pp
    rw [<-pp]
  case _ v heq =>
    simp at heq
    scalar_tac/- }}} -/

theorem implication_over_all{tree: BSTree α}{P Q: BSTree α -> Prop}
: tree.all_subtrees P -> (∀ x, P x -> Q x) -> tree.all_subtrees Q
:= by
  cases tree
  case Nil => simp
  case Node value left right =>
    simp; intro Px lih rih impl; split_conjs
    · apply impl; assumption
    · apply implication_over_all lih impl
    · apply implication_over_all rih impl

end Auxiliary/- }}} -/

section Rotate/- {{{ -/
theorem rotateLeft_preserves_wf[PartialOrder α][IsTotal α (·<=·)]{tree: BSTree α}
: tree.well_formed <-> tree.rotateLeft.well_formed
:= by/- {{{ -/
  simp [BSTree.rotateLeft]
  split <;> simp
  case _ v₂ A v₁ B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E
    intro A_wf B_wf 
    constructor
    case mp =>
      intro ⟨E_wf, B_inv, E_inv, A_inv, inner_inv⟩
      have v_rel: v₂ < v₁ := by apply inner_inv; simp
      split_conjs <;> try assumption
      · intros; simp [*]
      · intros x pred
        obtain (h | h) | h := pred <;> try simp [*]
        exact Trans.trans (A_inv _ h) v_rel
    case mpr =>
      intro ⟨A_inv,B_inv,E_wf,inner_inv,E_inv⟩
      have v_rel: v₂ < v₁ := by apply inner_inv; simp
      split_conjs <;> try assumption
      · intros; simp [*]
      · intros x pred
        obtain (h | h) | h := pred <;> try simp [*]
        exact Trans.trans v_rel (E_inv _ h)/- }}} -/

theorem rotateRight_preserves_wf[PartialOrder α][IsTotal α (·<=·)]{tree: BSTree α}
: tree.well_formed <-> tree.rotateRight.well_formed
:= by -- NOTE: symmetrical to rotateLeft_preserves_wf{{{
      -- NOTE: FLIP  doesn't help here, because we also need to flip on the order. It'd be 
  simp [BSTree.rotateRight]
  split <;> simp
  case _ v₁ v₂ A B E => -- Node v₁ (Node v₂ A B) E => Node v₂ A (Node v₁ B E)
    intro A_wf B_wf 
    constructor
    case mp =>
      intro ⟨A_inv,B_inv,E_wf,inner_inv,E_inv⟩
      have v_rel: v₂ < v₁ := by apply inner_inv; simp
      split_conjs <;> try assumption
      · intros; simp [*]
      · intros x pred
        obtain (h | h) | h := pred <;> try simp [*]
        exact Trans.trans v_rel (E_inv _ h)
    case mpr =>
      intro ⟨E_wf, B_inv, E_inv, A_inv, inner_inv⟩
      have v_rel: v₂ < v₁ := by apply inner_inv; simp
      split_conjs <;> try assumption
      · intros; simp [*]
      · intros x pred
        obtain (h | h) | h := pred <;> try simp [*]
        exact Trans.trans (A_inv _ h) v_rel/- }}} -/

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
: tree.invariant
-> tree.toBS.boundedBalancingFactor 2
-> ∃ tree',
    AVLTreeIsize.rotateLeft tree = .ok tree' ∧
    tree' = (tree: BSTree Isize).rotateLeft ∧
    tree'.invariant
:= by/- {{{ -/
  rw [AVLTreeIsize.rotateLeft.eq_def]
  intro tree_inv noOverflow
  split_all <;> try simp_all [BSTree.rotateLeft]
  case _ self v₁ A bf₁ inner v₂ B C bf₂ =>
    repeat progress
    simp_all [BSTree.rotateLeft]; scalar_tac/- }}} -/

@[pspec]
theorem rotateRight_spec(tree: AVLTree Isize)
: tree.invariant
-> tree.toBS.boundedBalancingFactor 2
-> ∃ tree',
    AVLTreeIsize.rotateRight tree = .ok tree' ∧
    tree' = (tree: BSTree Isize).rotateRight ∧
    tree'.invariant
:= by -- NOTE: Symmetrical to rotateLeft_spec, but without using `simp_all` {{{
  rw [AVLTreeIsize.rotateRight.eq_def]
  intro tree_inv noOverflow
  split_all <;> try (simp [BSTree.rotateRight, *] at *; try assumption) 
  -- I need that `try` in the `assumption` because      ┐▲
  -- otherwise the case which is closed by `simp` fails ├┘
  -- because `simp` has nothing to do                   ┘
  case _ self v₁ A bf₁ inner v₂ B C bf₂ =>
    repeat progress
    simp [*, BSTree.rotateRight]
    scalar_tac/- }}} -/

theorem rotateLeft_toSet(tree: BSTree α)
: tree.rotateLeft.toSet = tree.toSet
:= by/- {{{ -/
  cases tree
  case' Node value left right => cases right 
  all_goals open Set in simp [insert_comm, insert_union, union_assoc, BSTree.rotateLeft]/- }}} -/

theorem rotateRight_toSet(tree: BSTree α)
: tree.rotateRight.toSet = tree.toSet
:= by/- {{{ -/
  cases tree
  case' Node value left right => cases left 
  all_goals open Set in simp [insert_comm, insert_union, union_assoc, BSTree.rotateRight]/- }}} -/
  
end Rotate/- }}} -/

section Rebalance/- {{{ -/

theorem rebalance_preserves_inv_left{value: Isize}{left right: AVLTree Isize}{bf: I8}
: let tree := AVLTree.Node value left right bf
  tree.invariant
-> tree.toBS.balancingFactor = 2 
-> left.toBS.balanced -- left.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1)
-> right.toBS.balanced -- right.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1)
-> left.toBS.balancingFactor ≠ 0
-> ∃ tree',
    AVLTreeIsize.rebalance tree = .ok tree' ∧
    tree.toBS.rebalance = tree'.toBS ∧
    tree'.invariant ∧ -- TODO: These don't actually depend on AVLTreeIsize, but just on BSTree. Rework them.
    tree'.toBS.balanced ∧ -- tree'.toBS.all_subtrees (·.balancingFactor.natAbs ≤ 1) ∧
    tree'.toBS.height + 1 = tree.toBS.height
:= by /- {{{ -/
  intro tree tree_inv bf_2 left_bnd right_bnd left_heavy
  have ⟨bf_def, left_inv, right_inv⟩ := tree_inv
  unfold tree at *
  simp [AVLTreeIsize.rebalance.eq_def]

  have: bf = 2#i8 := by -- NOTE: Spiritually this should be just `scalar_tac`.
    apply Scalar.eq_equiv bf 2#i8 |>.mpr
    simp [<-bf_2, <-bf_def]
  simp [this]

  -- The core of the proof relies on the fact that, since we have restricted the values
  -- that tree.balancingFactor and left.balancingFactor can take, we can actually 
  -- determine the values of the heights of the relevant subtrees. In particular, we
  -- can write them as a function of a shared value H.
  generalize right_H: right.toBS.height = H at *
  -- We write subtree_H to refer to the proposition that relates subtree's height with H
  have left_H : left.toBS.height = H + (2: Int) := by 
    simp at *
    omega -- scalar_tac doesn't seem to work

  cases left
  case Nil => 
    -- Left cannot be nil, because then its balancingFactor would be 0, which we disallow!
    simp [AVLTreeIsize.balance_factor, balancingFactor_Node] at bf_2
    contradiction
  case Node v1 left1 right1 bf1 =>
    simp at left_inv
    have ⟨bf1_def, left1_inv, right1_inv⟩ := left_inv
    simp [bf1_def] at left_bnd left_heavy
    simp [AVLTreeIsize.balance_factor]

    -- Depending on the balancing factor of left, we encounter ourselves in the LEFT-LEFT
    -- or LEFT-RIGHT case. We handle these separately
    split_ifs
    case pos bf1_is_1 => /- {{{ -/
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
      · simp [bf_2, bf1_is_1, bf1_def, tree_inv]
      · simp [bf_2, bf1_is_1, bf1_def, left_inv]; split_conjs
        · apply implication_over_all left1_bnd (by scalar_tac)
        · apply implication_over_all right1_bnd (by scalar_tac)
        · apply implication_over_all right_bnd (by scalar_tac)
      simp only [BSTree.rotateRight] at tree'_spec
      simp [*, BSTree.rotateRight, balancingFactor_Node, BSTree.rebalance, Nat.max]
      split_conj <;> scalar_tac
      /- }}} -/

    case pos _ bf1_is_n1 => /- {{{ -/
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

      simp [BSTree.rebalance, bf_2, bf1_def, bf1_is_n1]

      -- We can apply the spec of rotateLeft to get to the following
      -- intermediary step, which is similar to the LEFT-LEFT case.
      progress with rotateLeft_spec as ⟨left', left'_spec, left'_inv⟩
      · simp [*]; split_conjs
        · apply implication_over_all left1_bnd (by omega)
        · apply implication_over_all right1_bnd (by omega)
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
      cases right1
      case Nil =>
        -- This can't be nil, because otherwise left.balancingFactor could never be negative!
        simp [bf1_is_n1] at bf1_def
      case Node v2 left2 right2 bf2 => 
        simp [BSTree.rotateLeft] at left'_spec left_H right1_bnd ⊢
        have: left2.toBS.height ⊔ right2.toBS.height = H := by omega
        obtain ⟨bf2_bal, left2_bnd, right2_bnd⟩ := right1_bnd

        -- Now we can simply apply the rotateRight spec and solve the goal through simplification
        progress as ⟨tree', tree'_spec, tree'_inv⟩
        · simp [*]; omega
        · simp [*]; split_conjs
          · omega
          · omega
          · omega
          · apply implication_over_all left1_bnd  (by omega) 
          · apply implication_over_all left2_bnd  (by omega) 
          · apply implication_over_all right2_bnd (by omega) 
          · apply implication_over_all right_bnd  (by omega)
        simp [*, BSTree.rotateRight, Nat.max]
        omega/- }}} -/

    case neg bf1_ne_1 bf1_ne_n1 => -- {{{
      -- We have specifically disallowed this case by asking that left.balancingFactor ≠ 0
      -- and that left is balanced.
      scalar_tac/- }}} -//- }}} -/

theorem rebalance_preserves_inv_right{value: Isize}{left right: AVLTree Isize}{bf: I8}
: let tree := AVLTree.Node value left right bf
  tree.invariant
-> tree.toBS.balancingFactor = -2
-> left.toBS.balanced
-> right.toBS.balanced
-> right.toBS.balancingFactor ≠ 0
-> ∃ tree',
    AVLTreeIsize.rebalance tree = .ok tree' ∧
    tree.toBS.rebalance = tree'.toBS ∧
    tree'.invariant ∧
    tree'.toBS.balanced ∧
    tree'.toBS.height + 1 = tree.toBS.height
:= by /- {{{ -/
  intro tree tree_inv bf_2 left_bnd right_bnd right_heavy
  have ⟨bf_def, left_inv, right_inv⟩ := tree_inv
  unfold tree at *
  simp [AVLTreeIsize.rebalance.eq_def]

  have: bf = (-2)#i8 := by 
    apply Scalar.eq_equiv bf (-2)#i8 |>.mpr
    simp [<-bf_2, <-bf_def]
  simp [this]

  -- The core of the proof relies on the fact that, since we have restricted the values
  -- that tree.balancingFactor and left.balancingFactor can take, we can actually 
  -- determine the values of the heights of the relevant subtrees. In particular, we
  -- can write them as a function of a shared value H.
  generalize left_H: left.toBS.height = H at *
  -- We write subtree_H to refer to the proposition that relates subtree's height with H
  have right_H : right.toBS.height = H + (2: Int) := by 
    simp [balancingFactor_Node] at *
    omega -- scalar_tac doesn't seem to work

  cases right
  case Nil => 
    -- Left cannot be nil, because then its balancingFactor would be 0, which we disallow!
    simp [AVLTreeIsize.balance_factor, balancingFactor_Node] at bf_2
  case Node v1 left1 right1 bf1 =>
    simp at right_inv
    have ⟨bf1_def, left1_inv, right1_inv⟩ := right_inv
    simp [bf1_def] at right_bnd right_heavy
    simp [AVLTreeIsize.balance_factor]

    -- Depending on the balancing factor of left, we encounter ourselves in the RIGHT-RIGHT
    -- or RIGHT-LEFT case. We handle these separately
    split_ifs
    case pos bf1_is_1 => /- {{{ -/
      simp [bf1_is_1] at bf1_def
      -- We're in the RIGHT-RIGHT case. This is the general shape of this case
      /-
        ┌──tree──┐       
        ▼        ▼       
       left  ┌─right─┐                   ┌────right────┐   
             ▼       ▼          ====>    ▼             ▼
           left1  ┌─right1┐          ┌─tree─┐      ┌─right1─┐           
                  │       │          ▼      ▼      ▼        ▼  
                  ▼       ▼         left  left1  left2    right2  
                left2   right2
      -/
      have left1_H: left1.toBS.height = H := by
        simp [balancingFactor_Node] at *
        omega
      have right1_H: right1.toBS.height = H + 1:= by
        simp [balancingFactor_Node] at *
        omega

      -- This case can be solved directly by using the rotateLeft spec
      -- However, to do so we need to provide some specific preconditions
      -- which require manipulating the hypothesis a bit.
      simp at *
      progress as ⟨tree', tree'_spec,tree'_inv⟩
      · simp [bf_2, bf1_is_1, bf1_def, tree_inv]
      · obtain ⟨bf1_bnd, left1_bnd, right1_bnd⟩ := right_bnd
        simp [bf_2, bf1_is_1, bf1_def, left_inv]; split_conjs
        · apply implication_over_all left_bnd (by scalar_tac)
        · apply implication_over_all left1_bnd (by scalar_tac)
        · apply implication_over_all right1_bnd (by scalar_tac)
      simp [*, BSTree.rotateLeft, balancingFactor_Node, BSTree.rebalance, Nat.max]
      split_conjs <;> scalar_tac/- }}} -/
    case pos _ bf1_is_1 => /- {{{ -/
      -- This is the RIGHT-LEFT case, which corresponds to the following shape
      /-
           ┌────tree────┐
           │     H+3    │
           ▼            ▼
         left     ┌───right───┐
           H      │    H+2    │
                  ▼           ▼
             ┌──left1──┐    right1
             │   H+1   │      H
             ▼         ▼
           left2     right2
            ≤H         ≤H
      -/
      have right1_H: right1.toBS.height = H:= by
        simp [balancingFactor_Node] at *
        omega
      have left1_H: left1.toBS.height = H + 1 := by
        simp [balancingFactor_Node] at *
        omega
      obtain ⟨bf1_bnd, left1_bnd, right1_bnd⟩ := right_bnd

      simp at bf_2
      simp [BSTree.rebalance, bf_2, bf1_def, bf1_is_1]

      -- We can apply the spec of rotateLeft to get to the following
      -- intermediary step, which is similar to the LEFT-LEFT case.
      progress with rotateRight_spec as ⟨left', left'_spec, left'_inv⟩
      · simp [bf_2, bf1_is_1, bf1_def, left1_inv, right1_inv]
      · simp [balancingFactor_Node]; split_conjs
        · omega
        · apply implication_over_all left1_bnd (by omega)
        · apply implication_over_all right1_bnd (by omega)
      -- After this operation, this is the current state of our tree
      /-
          ┌────tree────┐
          │     H+3    │
          ▼            ▼
        left     ┌───left1───┐           
                 │  (right') │           
                 ▼     H+2   ▼
               left2    ┌───left───┐           
              (left1')  │ (right1')│           
                        ▼    H+1   ▼           
                      right2     right1
                      (left2')  (right2')
                         H         ≤H
      -/
      cases left1
      case Nil =>
        -- This can't be nil, because otherwise right.balancingFactor could never be negative!
        simp [balancingFactor_Node, bf1_is_1] at bf1_def
        scalar_tac
      case Node v2 left2 right2 bf2 => 
        simp [BSTree.rotateRight] at left'_spec
        simp [BSTree.rotateRight]
        have: left2.toBS.height ⊔ right2.toBS.height = H := by
          simp at right_H
          omega
        have ⟨bf2_bal, left2_bnd, right2_bnd⟩ := left1_bnd
        simp [balancingFactor_Node] at left1_bnd

        -- Now we can simply apply the rotateLeft spec and solve the goal through simplification
        progress as ⟨tree', tree'_spec, tree'_inv⟩
        · unfold AVLTree.invariant
          simp only [left'_inv,right_inv]
          simp [balancingFactor_Node, *]
          omega
        · simp [balancingFactor_Node, left_H]; split_conjs
          · simp [*]; omega
          · apply implication_over_all left_bnd (by omega)
          · simp [*, balancingFactor_Node]; split_conjs
            · omega
            · apply implication_over_all left2_bnd (by omega)
            · omega
            · apply implication_over_all right2_bnd (by omega)
            · apply implication_over_all right1_bnd (by omega)
        simp [tree'_inv, tree'_spec, BSTree.rotateLeft, *, balancingFactor_Node, Nat.max]
        split_conjs <;> omega/- }}} -/
    case neg bf1_ne_1 bf1_ne_n1 => -- {{{
      -- We have specifically disallowed this case by asking that left.balancingFactor ≠ 0
      -- and that left is balanced.
      scalar_tac/- }}} -//- }}} -/

theorem rebalance_preserves_wf[LinearOrder α][IsTotal α (·≤·)]{tree: BSTree α}
: tree.well_formed
-> tree.rebalance.well_formed
:= by/- {{{ -/
  cases tree <;> simp [BSTree.rebalance]
  case Node value left right =>
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

        if bf1_1: (left1.height - right1.height : Int) = 1 then
          -- LEFT-LEFT case
          simp [bf1_1, BSTree.rotateRight]
          split_conjs <;> simp_all -- The problem with this simp_all is that it deletes v1_value

          have v1_value: v1 < value := left_bs _ (by simp)

          -- NOTE: Closing dependent arrows
          intro x hyp
          obtain (h | h) | h := hyp
          · rw [h]; assumption
          · apply right1_bs; assumption
          · trans value <;> try assumption
            apply right_bs; assumption
        else if bf1_n1: (left1.height - right1.height : Int) = -1 then
          -- LEFT-RIGHT case
          simp [bf1_n1]

          cases right1
          case Nil => 
            simp [BSTree.rotateRight, BSTree.rotateLeft]
            split_conjs <;> try assumption

            -- NOTE: Closing dependent arrows
            intro x x_right
            trans value <;> try assumption
            apply right_bs; assumption
          case Node v2 left2 right2 =>
            have ⟨left2_wf, righ2_wf, left2_bs, right2_bs⟩ := right1_wf
            have v1_v2 : v1 < v2 := by exact right1_bs v2 (by simp)
            have v2_value : v2 < value := by exact left_bs v2 (by simp)

            simp [BSTree.rotateRight, BSTree.rotateLeft, *]
            -- NOTE: Closing dependent arrows
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
                apply right_bs; assumption
        else
          -- We have that rebalance acts as the identity funciton
          -- so we can close the goal with our current assumptions
          simp [bf1_n1, bf1_1]
          split_conjs <;> assumption

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

        if bf1_1: (left1.height - right1.height : Int) = -1 then
          -- RIGHT-RIGHT case
          simp [bf1_1, BSTree.rotateLeft]
          split_conjs <;> simp_all

          have v1_value: value < v1 := right_bs _ (by simp)

          -- NOTE: Closing dependent arrows
          intro x hyp
          obtain (h | h) | h := hyp
          · rw [h]; assumption
          · trans value <;> try assumption
            apply left_bs; assumption
          · apply left1_bs; assumption
        else if bf1_n1: (left1.height - right1.height : Int) = 1 then
          -- RIGHT-LEFT case
          simp [bf1_n1]

          cases left1
          case Nil => 
            simp [BSTree.rotateRight, BSTree.rotateLeft]
            split_conjs <;> try assumption

            -- NOTE: Closing dependent arrows
            intro x x_right
            trans value <;> try assumption
            apply left_bs; assumption
          case Node v2 left2 right2 =>
            have ⟨left2_wf, righ2_wf, left2_bs, right2_bs⟩ := left1_wf
            have v1_v2 : v2 <v1  := by exact left1_bs v2 (by simp)
            have v2_value : value < v2 := by exact right_bs v2 (by simp)

            simp [BSTree.rotateRight, BSTree.rotateLeft, *]
            -- NOTE: Closing dependent arrows
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
                apply right1_bs; assumption
        else
          -- We have that rebalance acts as the identity funciton
          -- so we can close the goal with our current assumptions
          simp [bf1_n1, bf1_1]
          split_conjs <;> assumption
    else
      simp [bf_n2, bf_2]
      split_conjs <;> assumption/- }}} -/

theorem rebalance_toSet[LinearOrder α][IsTotal α (·≤·)](tree: BSTree α)
: tree.toSet = tree.rebalance.toSet
:= by/- {{{ -/
  cases tree <;> simp [BSTree.rebalance]
  case Node value left right =>
    split -- Here there are actually 3 cases
    case' isTrue => split_ifs <;> cases left -- First case, destructure left
    case' isFalse => split
    case' isTrue => split_ifs <;> cases right -- second case, destructure right
    -- Third case, can be solved through `simp`
    all_goals simp [rotateLeft_toSet, rotateRight_toSet]/- }}} -/

end Rebalance/- }}} -/

section Insert/- {{{ -/
/- theorem insert_height[BEq α][LE α][LT α][DecidableLT α](value: α)(tree: BSTree α) -/
/- : (tree.insert value |>.height) <= tree.height + 1 -/
/- := by/1- {{{ -1/ -/
/-   cases tree -/
/-   case Nil => simp [BSTree.insert] -/
/-   case Node curr left right => -/
/-     simp -/
/-     split_ifs <;> simp [Nat.max] -/
/-     · have := insert_height value left -/
/-       scalar_tac -/
/-     · have := insert_height value right -/
/-       scalar_tac/1- }}} -1/ -/

theorem insert_rebalance_toSet[BEq α][LE α][LinearOrder α][DecidableLT α](value: α)(tree: BSTree α)
: (tree.insert_rebalance value).toSet = insert value tree.toSet 
:= by/- {{{ -/
  cases tree <;> simp [BSTree.insert_rebalance]
  case Node curr left right =>
    if value_lt_curr: value < curr then
      simp [*]
      split_ifs <;> simp [<-rebalance_toSet, insert_rebalance_toSet, Set.insert_comm, Set.insert_union]
    else if curr_lt_value: curr < value then
      simp [*]
      split_ifs <;> simp [<-rebalance_toSet, insert_rebalance_toSet, Set.insert_comm, Set.insert_union]
    else
      have value_curr: value = curr := eq_of_le_of_le (le_of_not_gt (by assumption)) (le_of_not_gt (by assumption))
      simp [*]
      split_ifs <;> simp [<-rebalance_toSet]/- }}} -/

@[pspec]
theorem insert_and_warn_spec{tree: AVLTree Isize}(value: Isize)
: tree.invariant
-> tree.toBS.is_avl -- TODO:  Look into deactivating the `exists` lemma.
-> ∃ tree' b,
  AVLTreeIsize.insertAndWarn tree value = .ok (tree', b) ∧
  tree' = tree.toBS.insert_rebalance value ∧  -- This is also only true if we didn't have to rebalance all previous nodes.
  (if b 
   then (tree'.toBS.height = tree.toBS.height + 1 ∧ tree'.toBS = tree.toBS.insert value) 
   else (tree'.toBS.height = tree.toBS.height)) ∧
  tree'.invariant ∧
  tree'.toBS.is_avl
:= by/- {{{ -/
  intro tree_inv ⟨tree_bal, tree_wf⟩
  rw [AVLTreeIsize.insertAndWarn]

  -- To prove that `AVLTreeIsize.insertAndWarn` follows the spec of 
  -- `BSTree.insert_rebalance` we analyze the different types of inputs
  -- to both functions
  cases tree
  case Nil => 
    -- When the tree is empty, the result is trivially true since both
    -- functions are the identity function.
    simp [BSTree.insert_rebalance]
  case Node curr left right bf =>
    simp [BSTree.insert_rebalance] at *
    obtain ⟨bf_inv, left_inv, right_inv⟩ := tree_inv
    obtain ⟨bf_bal, left_bal, right_bal⟩ := tree_bal
    obtain ⟨left_wf, right_wf, left_bs, right_bs⟩ := tree_wf

    -- If the tree is not empty, we compare `value` with `curr` to decide
    -- where to insert the `value`
    split -- NOTE: If I do `split_ifs` here I get a `bf=2` hypothesis? Which makes no sense?
    case isTrue value_lt_curr =>
      -- In this case, we're inserting the value in the left hand side.
      progress as ⟨left', b, left'_spec, b_spec, left'_inv, left'_avl⟩
      · show left.toBS.is_avl; constructor <;> assumption
      obtain ⟨left'_bal,left'_wf⟩ := left'_avl

      -- This previous insert may have increased the height of the left subtree.
      -- We need to proceed differently depending on whether this has happened.
      if b_val: b then
        -- If the height of the tree increased, we need to update the balancing factor.
        simp [b_val] at b_spec ⊢
        obtain ⟨left'_height, left'_is_insert⟩ := b_spec

        progress as ⟨bf', bf'_spec⟩

        -- We have that, in fact, the update to `bf` is correct
        have bf'_def: bf' = (left'.toBS.height - right.toBS.height: Int) := by
          simp [<-bf_inv, balancingFactor_Node, left'_height, bf'_spec, left'_inv, right_inv]
          omega
        simp [bf'_def] at bf'_spec
        -- If when updating the balancing factor we have that this node becomes
        -- unbalanced, then we perform the rebalance operation.
        split
        case isTrue bf'_2 =>
          have right_avl: right.toBS.is_avl := by constructor <;> assumption
          simp [bf'_2] at bf'_def
          -- NOTE: I would have preferred to do `simp [bf'_def] at bf'_2`, but
          -- because bf'_def is in terms of bf'.val, the substitution doesn't
          -- take place

          simp [<-left'_spec, <-left'_is_insert, <-bf'_def]
          
          have tree'_wf: (AVLTree.Node curr left' right bf').toBS.well_formed := by
            simp [left'_wf, right_wf]
            split_conjs
            · have := SetRefinement.insert_spec left value left_wf |>.left
              simp [left'_is_insert, <-this, value_lt_curr]
              exact left_bs
            · exact right_bs
          have: left'.toBS.balancingFactor ≠ 0 := by
            -- The reason why this is true is because when inserting an element 
            -- into `tree`, we at most increase the the height of the tree by
            -- one. For bf' = 2 and bf1' = 0 to hold, we would need for 
            -- bf = 2 to also hold, but we have tree.bal!
            intro bf1'_0
            cases left 
            case Nil => 
              -- Can't be, because bf = 2
              simp at *; omega
            case Node v1 left right bf1 =>
              simp at left'_is_insert
              if h: value.val < v1 then
                simp [h] at left'_is_insert
                simp [left'_is_insert, Nat.max] at left'_height bf1'_0
                omega
              else if h2: v1.val < value then
                simp [h,h2] at left'_is_insert
                simp [left'_is_insert, Nat.max] at left'_height bf1'_0
                omega
              else
                have: v1 = value := eq_of_le_of_le (le_of_not_gt (by assumption)) (le_of_not_gt (by assumption))
                simp [this] at left'_is_insert
                simp [left'_is_insert, balancingFactor_Node] at left'_height

          progress with rebalance_preserves_inv_left as ⟨tree'', tree''_spec, tree''_inv, tree''_bal, tree''_height⟩
          · simp [*]

          simp [left'_height] at bf'_def
          simp at tree''_spec

          simp [*]
          simp [<-left'_spec]
          simp [tree''_spec, tree''_inv, tree''_bal]
          split_conjs
          · simp [left'_height] at tree''_height
            simp [Nat.max] at *
            have : left.toBS.height >= right.toBS.height := by scalar_tac
            omega
          · rw [<-tree''_spec]
            exact rebalance_preserves_wf tree'_wf
            
        case isFalse bf'_ne_2 =>
          -- No need to rebalance

          -- If bf + 1 is not 2 then bf ≠ 1 so bf = 0 or bf = -1
          have bf_ub: bf.val < 1 := by scalar_tac
          have bf_lb: -1 <= bf.val := by scalar_tac
          have false_branch: ¬ bf'.val.natAbs = 2 := by scalar_tac
          simp [bf'_def] at false_branch
          
          simp_all
          split_conjs <;> try assumption
          · if h: bf = 0#i8 then
              simp [h, left'_is_insert]
              simp [Scalar.eq_equiv] at h
              simp [<-bf_inv, balancingFactor_Node] at h
              have: left.toBS.height = right.toBS.height := by omega
              simp [this]
              omega
            else if h2: bf.val = (-1)#i8 then
              simp [h, left'_is_insert]
              simp [Scalar.eq_equiv] at h
              simp [<-bf_inv, balancingFactor_Node] at h
              have: right.toBS.height = left.toBS.height + 1 := by omega
              simp [this]
            else
              simp [Scalar.eq_equiv] at h h2
              simp [<-bf_inv, balancingFactor_Node] at h h2
              omega
          · omega
          · simp [left'_spec, insert_rebalance_toSet, value_lt_curr]
            assumption
      else
        -- If the height of the tree did not increase, there's no need to rebalance.
        simp [b_val] at b_spec ⊢

        have: ¬ bf = 2#i8 := by scalar_tac
        simp [this]

        simp [b_spec, Nat.max]
        split_conjs <;> try assumption
        · simp [<-left'_spec, b_spec, bf_inv]
          split <;> (first | rfl | omega)
        · simp [left'_spec, insert_rebalance_toSet, value_lt_curr]
          assumption
    case' isFalse _ => split -- NOTE: This is just to continue with the if statements
    case isTrue ne_value_lt_curr curr_lt_value =>
      -- In this case, we're inserting the value in the right hand side.
      progress as ⟨right', b, right'_spec, b_spec, right'_inv, right'_avl⟩
      · show right.toBS.is_avl; constructor <;> assumption
      obtain ⟨right'_bal,right'_wf⟩ := right'_avl

      -- Now we need to analyze whether the height of the tree increased or not
      if b_val: b then
        -- If the height of the tree increased, we need to update the balancing factor.
        simp [b_val] at b_spec ⊢
        obtain ⟨right'_height, right'_is_insert⟩ := b_spec

        progress as ⟨bf', bf'_spec⟩

        have bf'_def: bf' = (left.toBS.height - right'.toBS.height: Int) := by
          simp [<-bf_inv, balancingFactor_Node, right'_height, bf'_spec, right'_inv, right_inv]
          omega
        simp [bf'_def] at bf'_spec

        -- If when updating the balancing factor we have that this node becomes
        -- unbalanced, then we perform the rebalance operation.
        split
        case isTrue bf'_2 =>
          have right_avl: right.toBS.is_avl := by constructor <;> assumption
          simp [bf'_2] at bf'_def

          -- BSTree.insert_rebalance catch up
          simp [BSTree.insert_rebalance, ne_value_lt_curr, curr_lt_value, balancingFactor_Node, <-right'_is_insert, <-bf'_def]
          
          have tree'_wf: (AVLTree.Node curr left right' bf').toBS.well_formed := by
            simp [right'_wf, left_wf]
            split_conjs
            · exact left_bs
            · simp [right'_spec, insert_rebalance_toSet, curr_lt_value]
              exact right_bs
          have: right'.toBS.balancingFactor ≠ 0 := by
            -- The reason why this is true is because when inserting an element 
            -- into `tree`, we at most increase the the height of the tree by
            -- one. For bf' = 2 and bf1' = 0 to hold, we would need for 
            -- bf = 2 to also hold, but we have tree.bal!
            intro bf1'_0
            cases right 
            case Nil => 
              -- Can't be, because bf = 2
              simp at *; omega
            case Node v1 right right bf1 =>
              simp at right'_is_insert
              if h: value.val < v1 then
                simp [h] at right'_is_insert
                simp [right'_is_insert, Nat.max] at right'_height bf1'_0
                omega
              else if h2: v1.val < value then
                simp [h,h2] at right'_is_insert
                simp [right'_is_insert, Nat.max] at right'_height bf1'_0
                omega
              else
                have: v1 = value := eq_of_le_of_le (le_of_not_gt (by assumption)) (le_of_not_gt (by assumption))
                simp [this] at right'_is_insert
                simp [right'_is_insert, balancingFactor_Node] at right'_height

          progress with rebalance_preserves_inv_right as ⟨tree'', tree''_spec, tree''_inv, tree''_bal, tree''_height⟩
          · simp [*]

          simp [right'_spec] at bf'_def
          simp at tree''_spec

          simp [<-bf'_def]
          simp [<-right'_spec]
          simp [tree''_spec, tree''_inv, tree''_bal]
          split_conjs
          · simp [right'_height] at tree''_height
            simp [Nat.max] at *
            have : right.toBS.height >= left.toBS.height := by scalar_tac
            omega
          · rw [<-tree''_spec]
            exact rebalance_preserves_wf tree'_wf
            
        case isFalse bf'_ne_n2 =>
          -- No need to rebalance

          -- If bf - 1 is not -2 then bf ≠ -1 so bf = 0 or bf = 1
          have bf_ub: 0 <= bf.val := by scalar_tac
          have bf_lb: bf.val <= 1 := by scalar_tac
          have false_branch: ¬ bf'.val.natAbs = 2 := by scalar_tac
          simp [bf'_def] at false_branch
          
          simp [<-right'_spec, false_branch, left_inv, right_inv, bf'_def]
          /- simp_all -/
          split_conjs <;> try assumption
          · simp [right'_height]
            if h: bf = 0#i8 then
              simp [h, right'_is_insert]
              simp [Scalar.eq_equiv] at h
              simp [<-bf_inv, balancingFactor_Node] at h
              have: left.toBS.height = right.toBS.height := by omega
              simp [this]
              omega
            else if h2: bf.val = 1#i8 then
              simp [h, right'_is_insert]
              simp [Scalar.eq_equiv] at h
              simp [<-bf_inv, balancingFactor_Node] at h
              have: left.toBS.height = right.toBS.height + 1:= by omega
              simp [this]
            else
              simp [Scalar.eq_equiv] at h h2
              simp [<-bf_inv, balancingFactor_Node] at h h2
              omega
          · simp only [bf'_def, right'_height] at bf'_spec
            simp only [<-bf_inv, balancingFactor_Node] at bf_ub bf_lb
            omega
          · simp [right'_spec, insert_rebalance_toSet, ne_value_lt_curr, curr_lt_value]
            assumption
      else
        -- If the height of the tree did not increase, there's no need to rebalance.
        simp [b_val] at b_spec ⊢
        simp [<-right'_spec, b_spec, bf_inv]

        have: ¬ bf = (-2)#i8 := by scalar_tac
        simp [this]

        simp [b_spec, Nat.max, <-bf_inv]
        split_conjs <;> try assumption
        · simp [right'_spec, b_spec, bf_inv]
          split <;> try omega
          rfl
        · simp [right'_spec, insert_rebalance_toSet, curr_lt_value]
          assumption
    case isFalse value_ge_curr curr_ge_value =>
      -- In this case, we do not insert the value, and therefore we do not
      -- change the tree. Our previous hypothesis allow us to close the goal
      -- quicly.
      have: value = curr := by scalar_tac
      subst this; simp [BSTree.insert_rebalance]
      simp [bf_inv] at *
      have: bf.val.natAbs ≠ 2 := by scalar_tac
      simp [*]; split_conjs <;> assumption/- }}} -/

@[pspec]
theorem insert_spec{tree: AVLTree Isize}(value: Isize)
: tree.invariant
-> tree.toBS.is_avl
-> ∃ tree',
  AVLTreeIsize.insert tree value = .ok tree' ∧
  tree' = tree.toBS.insert_rebalance value ∧
  tree'.invariant ∧
  tree'.toBS.is_avl
:= by /- {{{ -/
  intro tree_inv tree_avl
  rw [AVLTreeIsize.insert]
  progress with insert_and_warn_spec as ⟨tree', b, tre'_spec, b_spec, tree'_inv, tree'_avl⟩
  split_conjs <;> assumption/- }}} -/

end Insert/- }}} -/

section Contains/- {{{ -/
@[pspec]
theorem contains_spec(tree: AVLTree Isize)(target: Isize)
: ∃ b,
    AVLTreeIsize.contains tree target = .ok b ∧
    b = tree.toBS.contains target
:= by/- {{{ -/
  cases tree <;> rw [AVLTreeIsize.contains] <;> simp
  case Node curr left right =>
    split_ifs <;> (try progress with contains_spec) <;> simp [*]/- }}} -/
end Contains/- }}} -/

end AVLRefinement
end Lemmas/- }}} -/

