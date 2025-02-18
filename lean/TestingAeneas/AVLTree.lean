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

theorem rotateLeft_preserves_wf[PartialOrder α][IsTotal α (·<=·)]{tree: BSTree α}
: tree.well_formed <-> tree.rotateLeft.well_formed
:= by
  simp [BSTree.rotateLeft]
  split <;> simp
  case _ v₂ A v₁ B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E
    intro A_wf B_wf 
    apply Iff.intro
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
        exact Trans.trans v_rel (E_inv _ h)

theorem rotateRight_preserves_wf[PartialOrder α][IsTotal α (·<=·)]{tree: BSTree α}
: tree.well_formed <-> tree.rotateRight.well_formed
:= by -- NOTE: symmetrical to rotateLeft_preserves_wf
      -- NOTE: FLIP  doesn't help here, because we also need to flip on the order. It'd be 
  simp [BSTree.rotateRight]
  split <;> simp
  case _ v₁ v₂ A B E => -- Node v₁ (Node v₂ A B) E => Node v₂ A (Node v₁ B E)
    intro A_wf B_wf 
    apply Iff.intro 
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
        exact Trans.trans (A_inv _ h) v_rel

theorem rotateLeft_preserves_contains[LinearOrder α]{tree: BSTree α}{target: α}
: tree.well_formed -> -- Since rotate preserves well-formedness, contains is also preserved
(tree.contains target <-> tree.rotateLeft.contains target)
:= by
  intro tree_wf 
  apply Iff.intro
  case mp =>
    intro target_in_tree
    simp [BSTree.rotateLeft]
    split <;> simp [*] at *
    case _ v2 A v1 B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E
      obtain ⟨A_wf, B_wf, E_wf, B_inv, E_inv, A_inv, inner_inv⟩ := tree_wf
      have v2_v1 := inner_inv v1 (by simp)
      if lt_v1: target < v1 then
        if lt_v2: target < v2 then
          simp [*] at *; right; assumption
        else if gt_v2: target > v2 then
          simp [*] at *; obtain _ | (_ | _) := target_in_tree <;> repeat (first | (try left); assumption | right)
        else
          have: target = v2 := eq_of_le_of_le (le_of_not_gt gt_v2) (le_of_not_gt lt_v2)
          subst this; simp; right; intro h
          have := ne_of_lt (Trans.trans h v2_v1)
          contradiction
      else if gt_v1: target > v1 then
        have: v2 < target := Trans.trans v2_v1 gt_v1
        simp [not_lt_of_ge (le_of_lt this), ne_of_lt this, ne_of_lt gt_v1, not_lt_of_ge (le_of_lt gt_v1)] at *
        assumption
      else
        have: target = v1 := eq_of_le_of_le (le_of_not_gt gt_v1) (le_of_not_gt lt_v1)
        subst this; left; rfl
  case mpr =>
    simp [BSTree.rotateLeft]
    split <;> simp [*] at *
    case _ v2 A v1 B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E
      obtain ⟨A_wf, B_wf, E_wf, B_inv, E_inv, A_inv, inner_inv⟩ := tree_wf
      have v2_v1 := inner_inv v1 (by simp)
      if lt_v1: target < v1 then
        if lt_v2: target < v2 then
          simp [*, ne_of_lt lt_v1, ne_of_lt lt_v2]
        else if gt_v2: target > v2 then
          simp [*, ne_of_lt lt_v1, ne_of_lt gt_v2];
        else
          have: target = v2 := eq_of_le_of_le (le_of_not_gt gt_v2) (le_of_not_gt lt_v2)
          subst this; simp
      else if gt_v1: target > v1 then
        have: v2 < target := Trans.trans v2_v1 gt_v1
        simp [not_lt_of_ge (le_of_lt this), ne_of_lt this, ne_of_lt gt_v1, not_lt_of_ge (le_of_lt gt_v1)] at *
      else
        have: target = v1 := eq_of_le_of_le (le_of_not_gt gt_v1) (le_of_not_gt lt_v1)
        subst this
        simp [ne_of_lt v2_v1, not_lt_of_ge (le_of_lt v2_v1)]

theorem rotateRight_preserves_contains[LinearOrder α]{tree: BSTree α}{target: α}
: tree.well_formed -> -- Since rotate preserves well-formedness, contains is also preserved
(tree.contains target <-> tree.rotateRight.contains target)
:= by -- NOTE: Adapted copy-paste from rotateLeft_preserves_contains
  intro tree_wf 
  apply Iff.intro
  case mp => 
    intro target_in_tree
    simp [BSTree.rotateRight]
    split <;> simp [*] at *
    case _ v2 v1 A B E => -- Node v₂ (Node v₁ A B) E  => Node v₁ (Node v₂ A B) E
      obtain ⟨A_wf, B_wf, A_inv, B_inv, E_wf, inner_inv, E_inv⟩ := tree_wf
      have v1_v2 := inner_inv v1 (by simp)
      if lt_v1: target < v1 then
        have: target < v2 := Trans.trans lt_v1 v1_v2
        simp [this, lt_v1, ne_of_lt this, ne_of_lt lt_v1] at *
        assumption
      else if gt_v1: target > v1 then
        if lt_v2: target < v2 then
          simp [*] at *; obtain _ | (_ | _) := target_in_tree <;> repeat (first | (try left); assumption | right)
        else if gt_v2: target > v2 then
          simp [*] at *; right; assumption
        else
          have: target = v2 := eq_of_le_of_le (le_of_not_gt gt_v2) (le_of_not_gt lt_v2)
          subst this; simp; right; intro h
          have := ne_of_lt (Trans.trans h v1_v2)
          contradiction
      else
        have: v1 = target := eq_of_le_of_le (le_of_not_gt lt_v1) (le_of_not_gt gt_v1) 
        subst this; simp
  case mpr =>
    simp [BSTree.rotateRight]
    split <;> simp [*] at *
    case _ v2 v1 A B E => -- Node v₂ A (Node v₁ B E) => Node v₁ (Node v₂ A B) E
      obtain ⟨A_wf, B_wf, A_inv, B_inv, E_wf, inner_inv, E_inv⟩ := tree_wf
      have v1_v2 := inner_inv v1 (by simp)
      if lt_v1: target < v1 then
        have: target < v2 := Trans.trans lt_v1 v1_v2 
        simp [ne_of_lt lt_v1, ne_of_lt this, this, lt_v1]
      else if gt_v1: target > v1 then
        if lt_v2: target < v2 then
          simp [*, ne_of_lt gt_v1, ne_of_lt lt_v2]
        else if gt_v2: target > v2 then
          simp [*, ne_of_lt gt_v1, ne_of_lt gt_v2];
        else
          have: target = v2 := eq_of_le_of_le (le_of_not_gt gt_v2) (le_of_not_gt lt_v2)
          subst this; simp
      else
        have: v1 = target := eq_of_le_of_le (le_of_not_gt lt_v1) (le_of_not_gt gt_v1) 
        subst this; simp [v1_v2]

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


theorem rebalance_correct_left[LinearOrder α][IsTotal α (·≤·)](value: α)(left right: BSTree α)
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
  case right => -- Rebalance keeps well_formedness
    obtain ⟨left_wf, right_wf, left_bs_inv, right_bs_inv⟩ := tree_wf
    split_ifs
    case pos bf2_n1 =>
      cases left <;> simp [*] <;> try assumption
      case Node v1 left1 right1 =>
        simp at bf2_n1
        /- obtain ⟨left1_wf, right1_wf, left1_inv, right1_inv⟩ := left_wf -/
        apply rotateRight_preserves_wf.mp
        unfold BSTree.well_formed; split_conjs <;> try assumption
        apply rotateLeft_preserves_wf.mp; assumption
        intro x hyp
        -- NOTE: This was a lot of moving theorems around. 
        -- TODO: Look into how I could streamline the process
        have := SetRefinement.contains_spec x (rotateLeft_preserves_wf.mp left_wf) |>.mpr hyp
        have := rotateLeft_preserves_contains left_wf |>.mpr this
        apply left_bs_inv
        exact SetRefinement.contains_spec x left_wf |>.mp this
    case pos bf2_ne_1 bf2_n1 =>
      clear bf2_ne_1
      -- NOTE: Adapted copy-paste from previous case
      cases left <;> simp [*] <;> try assumption
      case Node v1 left1 right1 =>
        simp at bf2_n1
        apply rotateRight_preserves_wf.mp
        unfold BSTree.well_formed; split_conjs <;> try assumption
    case neg bf2_ne_1 bf2_ne_n1 =>
      split <;> simp at bf2_ne_1 bf2_ne_n1
      · unfold BSTree.well_formed; split_conjs <;> try assumption
      · unfold BSTree.well_formed; split_conjs <;> try assumption
        -- TODO: Could this be simplified if I don't split the `tree_wf` hypothesis at the beginning?

theorem rebalance_correct_right[LinearOrder α][IsTotal α (·≤·)](value: α)(left right: BSTree α)
: left.is_avl
-> right.is_avl
-> (BSTree.Node value left right).well_formed
-> (left.height - right.height: Int) = -2
-> right.balancingFactor ≠ 0
-> (BSTree.Node value left right).rebalance.is_avl
:= by -- NOTE: Adapted copy-paste from rebalance_correct_left
  intro left_avl right_avl tree_wf bf1_is_2 bf1_left_ne_0
  simp
  apply And.intro <;> simp [BSTree.rebalance, bf1_is_2,]
  case left => -- Rebalance balances the tree
    clear tree_wf -- We won't need this, remove to manage number of hypothesis
    simp [BSTree.is_avl] at left_avl right_avl
    obtain ⟨left_bal, -⟩ := left_avl
    obtain ⟨right_bal, -⟩ := right_avl
    split_ifs
    case pos bf2_n1 =>
      generalize H_def: left.height = H at *
      have left_H: right.height = H + 2 := by scalar_tac
      cases left_def:right <;> simp [*] at *
      case Node v1 left1 right1 =>
        have: left1.height = right1.height + 1 := by scalar_tac
        have left1_H: right1.height = H := by 
          simp [this] at left_H
          scalar_tac
        simp [*] at *
        cases h:left1 <;> try simp [BSTree.rotateLeft, BSTree.rotateRight, *] at *
        case Node v2 left2 right2 =>
          unfold Nat.max at *
          scalar_tac
    case pos bf2_ne_1 bf2_1 =>
      generalize H_def: left.height = H at *
      have right_H: right.height = H + 2 := by scalar_tac
      cases right <;> simp [*] at *
      case Node v1 left1 right1 =>
        have: right1.height = left1.height + 1 := by scalar_tac
        simp [this] at right_H
        have left1_H: left1.height = H := by scalar_tac
        simp [*] at *; clear right_H
        simp [BSTree.rotateLeft, BSTree.rotateRight,  *]
        scalar_tac
    case neg bf2_ne_1 bf2_ne_n1 =>
      have bf2_0: right.balancingFactor = 0 := by
        cases right <;> simp at *
        case Node v1 right1 left1 => scalar_tac
      contradiction
  case right => -- Rebalance keeps well_formedness
    obtain ⟨left_wf, right_wf, left_bs_inv, right_bs_inv⟩ := tree_wf
    split_ifs
    case pos bf2_n1 =>
      cases right <;> simp [*] <;> try assumption
      case Node v1 left1 right1 =>
        simp at bf2_n1
        apply rotateLeft_preserves_wf.mp
        unfold BSTree.well_formed; split_conjs <;> try assumption
        apply rotateRight_preserves_wf.mp; assumption
        intro x hyp
        have := SetRefinement.contains_spec x (rotateRight_preserves_wf.mp right_wf) |>.mpr hyp
        have := rotateRight_preserves_contains right_wf |>.mpr this
        apply right_bs_inv
        exact SetRefinement.contains_spec x right_wf |>.mp this
    case pos bf2_ne_1 bf2_n1 =>
      clear bf2_ne_1
      -- NOTE: Adapted copy-paste from previous case
      cases right <;> simp [*] <;> try assumption
      case Node v1 left1 right1 =>
        simp at bf2_n1
        apply rotateLeft_preserves_wf.mp
        unfold BSTree.well_formed; split_conjs <;> try assumption
    case neg bf2_ne_1 bf2_ne_n1 =>
      split <;> simp at bf2_ne_1 bf2_ne_n1
      · unfold BSTree.well_formed; split_conjs <;> try assumption
      · unfold BSTree.well_formed; split_conjs <;> try assumption

theorem unnecessary_rebalance_is_id(tree: BSTree α)
: tree.balancingFactor.natAbs ≠ 2
-> tree.rebalance = tree
:= by
  cases tree
  case Nil => simp [BSTree.rebalance]
  case Node v left right =>
    simp; intro abs_bf_ne_2
    have bf_ne_2: (left.height - right.height: Int) ≠ 2 := by scalar_tac
    have bf_ne_n2: (left.height - right.height: Int) ≠ -2 := by scalar_tac
    simp [BSTree.rebalance, bf_ne_2, bf_ne_n2]

@[pspec]
theorem insert_and_warn_spec{tree: AVLTree Isize}(value: Isize)
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
    obtain ⟨⟨bf1_bal, left_bal, right_bal⟩, left_wf, right_wf, left_bst, right_bst⟩ := tree_avl
    split
    case isTrue v1_eq_value => -- No value needs to be inserted
      have: (left.toBS.height - right.toBS.height: Int).natAbs ≠ 2 := by scalar_tac
      have: (left.toBS.height - right.toBS.height: Int) ≠ 2 := by scalar_tac
      have: (left.toBS.height - right.toBS.height: Int) ≠ -2 := by scalar_tac
      simp [*] at *
      split_conjs
      · scalar_tac
      · assumption
    case isFalse v1_ne_value => -- We need to insert the value in either left or right
      obtain ⟨bf_def, left_avl_inv, right_avl_inv⟩ := avl_inv
      split
      case isTrue value_v1=> -- value < v1
        have ⟨tree', b, tree'', tree'_spec, tree''_spec, b_spec, tree'_tree'', tree'_avl⟩ := insert_and_warn_spec value left_avl_inv (by simp [left_bal, left_wf])
        simp [tree'_spec, tree''_spec]
        cases tree''
        case Nil =>
          simp at b_spec; simp [b_spec]

          sorry
        case Node =>
          sorry
      case isFalse v1_value => -- v1 < value
        have v1_value: v1.val < value := by scalar_tac


        sorry


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
    split_ifs <;> simp [Nat.max]
    · have := insert_height value left
      scalar_tac
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
