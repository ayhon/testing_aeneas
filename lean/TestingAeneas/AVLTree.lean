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
    (left.height - right.height: Int).natAbs ≤ 1 ∧
    left.balanced ∧ right.balanced

@[simp] abbrev BSTree.leftHeavy(tree: BSTree α) := tree.balancingFactor > 0

@[simp] abbrev BSTree.rightHeavy(tree: BSTree α) := tree.balancingFactor < 0

@[simp] abbrev BSTree.is_avl[PartialOrder α][IsTotal α (·≤·)](tree: BSTree α): Prop :=
  tree.balanced ∧ tree.well_formed

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
    (left.toBS.height - right.toBS.height : Int) = bf ∧
    left.invariant ∧ right.invariant

section Lemmas/- {{{ -/
namespace AVLRefinement
open testing_aeneas hiding max min BSTree
open Spec
attribute [local simp] AVLTree.toBS

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

@[pspec]
theorem negate_spec(a: I8)
: a > I8.min + 1
-> ∃ v,
    -.a = .ok v ∧ v = -a.val
:= by
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
    scalar_tac

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
-> (tree: BSTree Isize).balanced
-> ∃ tree',
    AVLTreeIsize.rotateLeft tree = .ok tree' ∧
    tree' = (tree: BSTree Isize).rotateLeft ∧
    tree'.invariant
:= by
  rw [AVLTreeIsize.rotateLeft.eq_def]
  intro tree_inv balanced
  split <;> simp [BSTree.rotateLeft]; split <;> simp [AVLTree.invariant] at *; try assumption
  case _ self v₁ A bf₁ inner v₂ B C bf₂ =>
    obtain ⟨bf₁_spec, A_inv, bf₂_spec, B_inv, C_inv⟩ := tree_inv
    obtain ⟨bf₁_inv, -, bf₂_inv, -⟩ := balanced

    progress as ⟨aux, aux_spec⟩
    progress as ⟨aux2, aux2_spec⟩
    progress as ⟨bf₄, bf₄_spec⟩
    simp only [aux_spec, aux2_spec] at bf₄_spec; clear aux aux_spec aux2 aux2_spec

    progress as ⟨aux, aux_spec⟩
    progress as ⟨aux2, aux2_spec⟩
    progress as ⟨bf₃, bf₃_spec⟩
    simp only [aux_spec, aux2_spec] at bf₃_spec; clear aux aux_spec aux2 aux2_spec

    simp [*]; split_conjs <;> scalar_tac

@[pspec]
theorem rotateRight_spec(tree: AVLTree Isize)
: tree.invariant
-> (tree: BSTree Isize).balanced
-> ∃ tree',
    AVLTreeIsize.rotateRight tree = .ok tree' ∧
    tree' = (tree: BSTree Isize).rotateRight ∧
    tree'.invariant
:= by -- NOTE: Symmetrical to rotateLeft_spec
  rw [AVLTreeIsize.rotateRight.eq_def]
  intro tree_inv balanced
  split <;> simp [BSTree.rotateRight]; split <;> simp [AVLTree.invariant] at *; try assumption
  case _ self v₁ A bf₁ inner v₂ B C bf₂ =>
    obtain ⟨bf₁_inv, bf₂_inv, -⟩ := balanced
    obtain ⟨bf₁_spec, bf₂_spec, B_inv, C_inv, A_inv⟩ := tree_inv

    progress as ⟨aux, aux_spec⟩
    progress as ⟨aux2, aux2_spec⟩
    progress as ⟨bf₄, bf₄_spec⟩
    simp only [aux_spec, aux2_spec] at bf₄_spec; clear aux aux_spec aux2 aux2_spec

    progress as ⟨aux, aux_spec⟩
    progress as ⟨aux2, aux2_spec⟩
    progress as ⟨bf₃, bf₃_spec⟩
    simp only [aux_spec, aux2_spec] at bf₃_spec; clear aux aux_spec aux2 aux2_spec

    simp [*]; split_conjs <;> scalar_tac

theorem rotateRight_balanced(tree: BSTree α)
: tree.balanced
-> tree.leftHeavy
-> tree.rotateRight.balanced
:= by sorry

@[pspec]
theorem rebalance_spec(tree: AVLTree Isize)
: tree.invariant
-> (tree : BSTree Isize).balanced
-> ∃ tree',
    AVLTreeIsize.rebalance tree = .ok tree' ∧
    tree'.toBS = tree.toBS.rebalance
:= by
  intro avl_inv balanced
  rw [AVLTreeIsize.rebalance.eq_def]
  split
  case _ =>
    simp [BSTree.rebalance]
  case _ X vX Z D bfX =>
    obtain ⟨bfX_spec, Z_avl, D_avl⟩ := avl_inv
    split_ifs 
    case pos bfX_is_2 =>
      subst bfX_is_2
      simp [AVLTreeIsize.balance_factor]
      cases Z <;> simp at *
      case Nil =>
        simp [BSTree.rebalance, *]
      case Node vZ A Y bfZ =>
        obtain ⟨bfZ_spec, A_inv, Y_inv⟩ := Z_avl
        split_ifs
        case pos bfZ_is_1 =>
          /-
                 ⟨X⟩
                Y  ᵈ  >>     Y
              Z  ᶜ         Z   X
             ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
          -/
          subst bfZ_is_1
          unfold BSTree.rebalance
          simp [*] at *
        case pos _ bfZ_is_n1 =>
          /-
                X           ⟨X⟩            
             ⟨Z⟩  ᵈ  >>    Y  ᵈ   >>     Y
             ᵃ  Y        Z  ᶜ          Z   X
               ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
          -/
          subst bfZ_is_n1
          unfold BSTree.rebalance
          simp [*] at *
        case neg _ _ =>
          simp [*] at *
    case pos _ bfX_is_n2 =>
      -- NOTE: I expect this to be symmetrical to the previous case
      subst bfX_is_n2
      simp [AVLTreeIsize.balance_factor]
      cases D <;> simp at *
      case Node vD A Y bfD =>
        obtain ⟨bfD_spec, A_inv, Y_inv⟩ := D_avl
        split_ifs
        case pos bfD_is_1 =>
          /- NOTE: Letters not accurate due to copy-paste
                 ⟨X⟩
                Y  ᵈ  >>     Y
              Z  ᶜ         Z   X
             ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
          -/
          subst bfD_is_1
          unfold BSTree.rebalance
          simp [*] at *
        case pos _ bfD_is_n1 =>
          /- NOTE: Letters not accurate due to copy-paste
                X           ⟨X⟩            
             ⟨Z⟩  ᵈ  >>    Y  ᵈ   >>     Y
             ᵃ  Y        Z  ᶜ          Z   X
               ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
          -/
          subst bfD_is_n1
          unfold BSTree.rebalance
          simp [*] at *
        case neg _ _ =>
          simp at *; simp [BSTree.rebalance, *] -- NOTE: Same as bellow `neg` branch
    case neg bf1_ne_2 bf1_ne_n2 =>
      -- Here I simply have to show that BSTree does nothing as well.
      simp at *; simp [BSTree.rebalance, *]


theorem rebalance_correct_left[PartialOrder α][IsTotal α (·≤·)](value: α)(left right: BSTree α)
: left.is_avl
-> right.is_avl
-> (BSTree.Node value left right).well_formed
-> (left.height - right.height: Int) = 2
-> left.balancingFactor ≠ 0 -- Look at the note with (`EXTRA_HYPOT`)
/- -> right.balancingFactor ≠ 0 -- TODO: You can't do both at once! Choose between left or right -/
-> (BSTree.Node value left right).rebalance.is_avl
:= by
  intro left_avl right_avl tree_wf bf1_is_2 bf1_left_ne_0
  simp
  apply And.intro <;> simp [BSTree.rebalance, bf1_is_2,]
  case left => -- Rebalance balances the tree
    clear tree_wf -- We won't need this, remove to manage number of hypothesis
    simp [BSTree.is_avl] at left_avl right_avl
    obtain ⟨left_bal, -⟩ := left_avl
    obtain ⟨right_bal, -⟩ := right_avl
    split_ifs
    case pos bf2_n1 => -- LEFT-RIGHT: bf1 = 2, bf2 = -1
      /-
            X           ⟨X⟩            
         ⟨Z⟩  ᵈ  >>    Y  ᵈ   >>     Y
         ᵃ  Y        Z  ᶜ          Z   X
           ᵇ ᶜ       ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
      -/
      generalize H_def: right.height = H at *
      have left_H: left.height = H + 2 := by scalar_tac
      cases left_def:left <;> simp [*] at *
      case Node v1 left1 right1 =>
        have: right1.height = left1.height + 1 := by scalar_tac
        have left1_H: left1.height = H := by 
          simp [this] at left_H
          scalar_tac
        simp [*] at *
        cases h:right1 <;> try simp [BSTree.rotateLeft, BSTree.rotateRight, *] at *
        case Node v2 left2 right2 =>
          unfold Nat.max at *
          scalar_tac

    case pos bf2_ne_1 bf2_1 =>
      /-
             ⟨X⟩
            Y  ᵈ  >>     Y
          Z  ᶜ         Z   X
         ᵃ ᵇ          ᵃ ᵇ ᶜ ᵈ
      -/
      generalize H_def: right.height = H at *
      have left_H: left.height = H + 2 := by scalar_tac
      -- TODO: This part above can probably be abstracted away if we don't use the split_ifs tactic
      cases left <;> simp [*] at *
      case Node v1 left1 right1 =>
        have: left1.height = right1.height + 1 := by scalar_tac
        simp [this] at left_H
        have right1_H: right1.height = H := by scalar_tac
        simp [*] at *; clear left_H
        simp [BSTree.rotateRight, BSTree.rotateLeft, *]
        scalar_tac
    case neg bf2_ne_1 bf2_ne_n1 =>
      have bf2_0: left.balancingFactor = 0 := by
        cases left <;> simp at *
        case Node v1 left1 right1 => scalar_tac
      -- TODO: This is a contradiction because of `insert_height`.
      --  If we rebalance after an insertion, we should have that the modified tree
      --  doesn't differ by more than 1 in the heights of its nodes. This, combined
      --  with the hypothesis that the original tree was a proper AVL ensures that
      --  left.balancingFactor ≠ 0
      -- NOTE: Added hypothesis bf1_left_ne_0 and bf1_right_ne_0 (`EXTRA_HYPOT`)
      contradiction
  case right => -- Rebalance balances keeps well_formedness
    obtain ⟨left_wf, right_wf, left_bs_inv, right_bs_inv⟩ := tree_wf
    split_ifs
    case pos bf2_n1 =>
      simp [BSTree.rotateRight, BSTree.rotateLeft]
      cases left <;> simp [*] <;> try assumption
      case Node v1 left1 right1 =>
        simp at left_wf left_bs_inv bf2_n1
        cases right1 <;> simp at left_wf
        case Nil =>
          simp [*]
          split_conjs
          · intro x in_right; apply right_bs_inv; simp [*]
          · intro x in_left1; apply left_wf.right; simp [*]
          · intro x x_in_right
            have: v1 < value := left_bs_inv v1 (by simp)
            trans value <;> try assumption
            apply right_bs_inv; assumption
        case Node v2 left2 right2 =>
          simp [*]
          split_conjs
          · obtain ⟨-, -, -, -, -, left1_inv,-⟩ := left_wf; assumption
          · 
            obtain ⟨-, -, -, left2_inv, -, -, right1_bs_inv⟩ := left_wf
            intro x x_in_right2
            have: v1 < value := left_bs_inv v1 (by simp)
            trans value <;> try assumption
            -- TODO: Draw the case
            sorry
          all_goals sorry
    case pos bf2_ne_1 bf2_n1 =>
      sorry
    case neg bf2_ne_1 bf2_ne_n1 =>
      sorry

theorem rebalance_correct_right[PartialOrder α][IsTotal α (·≤·)](value: α)(left right: BSTree α)
: left.is_avl
-> right.is_avl
-> (BSTree.Node value left right).well_formed
-> (left.height - right.height: Int) = -2
-> right.balancingFactor ≠ 0
-> (BSTree.Node value left right).rebalance.is_avl
:= sorry

@[pspec]
theorem insert_and_warn{tree: AVLTree Isize}{value: Isize}
: tree.invariant
-> tree.toBS.is_avl
-> ∃ tree' b tree'',
  AVLTreeIsize.insertAndWarn tree value = .ok (tree', b) ∧
  tree.toBS.insert value = tree'' ∧
  b = (tree''.balancingFactor.natAbs == 2) ∧
  tree''.rebalance = tree'.toBS ∧
  tree'.toBS.is_avl
:= by
  intro avl_inv tree_avl
  rw [AVLTreeIsize.insertAndWarn]
  split <;> simp [BSTree.rebalance]
  case _ v1 left right bf =>
    split
    case isTrue v1_eq_value =>
      have: (left.toBS.height - right.toBS.height: Int).natAbs ≠ 2 := by scalar_tac
      have: (left.toBS.height - right.toBS.height: Int) ≠ 2 := by scalar_tac
      have: (right.toBS.height - left.toBS.height: Int) ≠ 2 := by scalar_tac
      simp [*] at *
      split_conjs
      · intro; scalar_tac
      · scalar_tac
      · simp [*] -- from direct assumption
      · simp [*] -- from direct assumption
      · simp [*] -- from direct assumption
      · simp [*] -- from direct assumption
      · obtain ⟨-, -, -, -, -, _, -⟩ := tree_avl
        assumption
      · obtain ⟨-, -, -, -, -, -, _⟩ := tree_avl
        assumption
    case isFalse v1_ne_value =>
      split_ifs

      any_goals sorry


@[pspec]
theorem insert_spec(tree: AVLTree Isize)(value: Isize)
: tree.invariant
-> tree.toBS.is_avl
-> ∃ tree' tree'',
    AVLTreeIsize.insert tree value = .ok tree' ∧
    tree.toBS.insert value = tree'' ∧
    tree'.toBS.is_avl ∧
    tree'.toBS = tree''.rebalance -- The condition |tree.balancingFactor| <= 1 implies tree''.rebalance = tree''
:= by
  intro avl_inv tree_is_avl
  unfold AVLTreeIsize.insert
  progress as ⟨tree',      b,      tree'', 
               tree'_spec, b_spec, tree''_spec, tree'_avl⟩
  simp [*]

theorem insert_height[BEq α][LE α][LT α][DecidableLT α](value: α)(tree: BSTree α)
: (tree.insert value |>.height) <= tree.height + 1
:= by
  cases tree
  case Nil => simp [BSTree.insert]
  case Node curr left right =>
    simp
    split_ifs <;> simp <;> unfold Nat.max
    · have :=  insert_height value left
      scalar_tac -- TODO: I expected scalar_tac to close this as well through transitivity
    · have := insert_height value right
      scalar_tac


@[pspec]
theorem contains_spec(tree: AVLTree Isize)(target: Isize)
: ∃ b,
    AVLTreeIsize.contains tree target = .ok b ∧
    b = tree.toBS.contains target
:= by
  cases tree <;> rw [AVLTreeIsize.contains] <;> simp
  case Node curr left right =>
    split_ifs <;> (try progress with contains_spec) <;> simp [*]

end AVLRefinement
end Lemmas/- }}} -/
