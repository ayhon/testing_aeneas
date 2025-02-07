import TestingAeneas.Definitions
import Aeneas

open Aeneas.Std

namespace Lemmas
open testing_aeneas (BinTree)

def toTree: BinTree α -> Tree α
| .Nil => .nil
| .Node u lhs rhs => .node u (toTree lhs) (toTree rhs)

instance: Coe (BinTree α) (Tree α) where
  coe := toTree

def BinTree_Tree_equiv{tree tree': BinTree α}
: (tree: Tree α) = tree' ↔ tree = tree'
:= match tree, tree' with
   | .Nil,        .Nil 
   | .Node _ _ _, .Nil
   | .Nil,        .Node _ _ _    => by simp [toTree]
   | .Node u l r, .Node u' l' r' => by
      simp [toTree]; intro
      apply Iff.intro
      · intro ⟨lh, rh⟩
        split_conjs <;> apply BinTree_Tree_equiv.mp <;> assumption
      · intro ⟨lh, rh⟩; subst lh rh; simp

section Insert
def Tree.insert: Tree α -> α -> Tree α
| .nil, a => .node a .nil .nil
| .node v lhs rhs, a => .node v lhs (Tree.insert rhs a)

@[pspec]
theorem insert_spec{a: α}{tree: BinTree α}
: ∃ tree',
    BinTree.insert tree a = Result.ok tree' ∧
    Tree.insert ↑tree a = ↑tree'
:= by
  rw [BinTree.insert] 
  match tree with
   | .Nil => simp [BinTree.nil, toTree, Tree.insert]
   | .Node v lhs rhs => 
        simp [BinTree.nil, toTree, Tree.insert]
        progress as ⟨tree', tree'_spec⟩
        simp [BinTree.nil, toTree, Tree.insert, toTree]
        assumption
end Insert
    

section Size
def Tree.size: Tree α -> Nat
| .nil => 0
| .node _ lhs rhs => 1 + Tree.size lhs + Tree.size rhs

@[pspec]
def size_spec{tree: BinTree α}
(noOverflow: Tree.size (tree: Tree α) <= U32.max)
: ∃ size,
    BinTree.size tree = Result.ok size ∧
    Tree.size (tree: Tree α) = size.toNat
:= by
  rw [BinTree.size]
  match tree with
  | .Nil => simp [Tree.size, toTree]
  | .Node v lhs rhs => 
    simp [Tree.size, toTree]
    simp [Tree.size, toTree] at noOverflow
    -- I have to include the preconditions explicitly in the proof
    -- but I would have expected `scalar_tac` to deduce them automatically.
    -- Is it because I'm using `with`? If I don't include them, I get a
    -- maximum recursion depth exceeded.
    have: ↑(Tree.size (toTree lhs)) < U32.max := by scalar_tac
    have⟨lhs_size, st, lhs_size_spec⟩:= @size_spec _ lhs (by scalar_tac); simp [st]
    -- ↑ maximum recursion depth exceeded using progress. I assume that it's because of `tree`
    --   being taken as tree and not lhs or rhs

    have: ↑1#u32 + ↑lhs_size ≤ U32.max := by scalar_tac
    progress with U32.add_spec as ⟨inter, inter_def⟩

    have: ↑(Tree.size (toTree lhs)) < U32.max := by scalar_tac
    have⟨rhs_size, st, rhs_size_spec⟩:= @size_spec _ rhs (by scalar_tac); simp [st]

    have: ↑inter + ↑rhs_size ≤ U32.max := by scalar_tac
    progress with U32.add_spec as ⟨res, res_def⟩

    simp [res_def, inter_def, lhs_size_spec, rhs_size_spec]
    scalar_tac
end Size

/-
With the previous definitions I can finally move along to proving the lemma
which relates insert and size. What I would like to be able to do is assert
that the following rust assertion is never triggered.
```rust
let n = tree.size()
assert!(  tree.insert(x).size() == n + 1  )
```
To do so, I've proven that `insert` and `size` conform to the specification
given in Lean. Now it would be enough to prove that under Lean's specification
the following property is true.

However, `size` requires an extra precondition stating that the size of the 
tree does not overflow. This is not captured by the specification. So after 
proving the property on the specification, we need to prove that it's transfered 
to the model.
-/

theorem length_insert(tree: Tree α)(a: α)
: (Tree.insert tree a |> Tree.size) = Tree.size tree + 1
:= match tree with
   | .nil => by 
      rw [Tree.insert]
      simp [Tree.size]
   | .node v lhs rhs => by 
      rw [Tree.insert]
      simp [Tree.size]
      rw [length_insert rhs]
      linarith

theorem rust_length_insert(tree: BinTree α)(a: α)
(noOverflow: Tree.size (tree: Tree α) < U32.max)
: do {(<- tree.insert a).size} = do {(<-tree.size) + 1#u32}
:= by
   progress as ⟨tree', insert_spec⟩
   /- progress with size_spec as ⟨size, size_spec'⟩ -/ -- maximum recursion depth again
   have⟨size, size_st, size_spec'⟩:= @size_spec _ tree (by scalar_tac)
   simp [size_st, size_spec']

   have⟨size', size'_st, size'_spec⟩:= @U32.add_spec size 1#u32 (by scalar_tac)
   simp [size'_st, size'_spec]

   /- TODO:
      Here I would like to apply `size_spec` and basically change completely into the
      Lean model, so that I can apply length_insert and conclude the theorem. To do
      so I need to apply the `size_spec` theorem over `tree'`, which I'm entitled to
      do because from noOverflow I'm able to derive it using `length_insert`.
   -/
   sorry

   
end Lemmas
