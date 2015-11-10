module 03hw where

open import Data.Bool hiding (_≟_)
open import Data.List hiding (partition)
open import Data.Vec hiding (split) renaming (_++_ to _+++_)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decid

-- Task 1.
----------
-- Implement tree-sort by implementing the functions
-- below.
data Tree (A : Set) : Set where
  empty : Tree A
  node : Tree A → A → Tree A → Tree A


-- insert an element into the tree, keeping the
-- invariant that all elements of the left hand
-- side of the tree are always smaller or equal
-- and all elements of the right hand side are
-- always larger.
insert : ℕ → Tree ℕ → Tree ℕ
insert el empty = node empty el empty
insert el (node t x t₁) with ⌊ el ≤? x ⌋
insert el (node t x t₁) | true = node (insert el t) x t₁
insert el (node t x t₁) | false = node t x (insert el t₁)

-- Convert the list into a sorted tree
sortTree : List ℕ → Tree ℕ
sortTree [] = empty
sortTree (x ∷ l) = insert x (sortTree l)

-- flatten a tree back to a list
join : Tree ℕ → List ℕ
join empty = []
join (node t x t₁) = join t ++ x ∷ join t₁

-- implement tree sort using the above functions
treeSort : List ℕ → List ℕ
treeSort l = join (sortTree l)


-- Task 2.
----------
-- Modify the above definitions to also prove that the sorted
-- list has the same length als the input-list.
-- The signature of treeSort will change to:
--
--     treeSort : {n : ℕ} → Vec ℕ n → Vec ℕ n

data TreeN (A : Set) : ℕ → Set where
  empty : TreeN A 0
  node : ∀ {l r} → TreeN A l → A → TreeN A r → TreeN A (suc (l + r))

insertCastLemma : ∀ l r → TreeN ℕ (suc (l + suc r)) →  TreeN ℕ (suc (suc (l + r)))
insertCastLemma l r = subst (λ n → TreeN ℕ (suc n)) (+-suc l r)

-- insert an element into the tree, keeping the
-- invariant that all elements of the left hand
-- side of the tree are always smaller or equal
-- and all elements of the right hand side are
-- always larger.
insertN : ∀ {n} → ℕ → TreeN ℕ n → TreeN ℕ (suc n)
insertN el empty = node empty el empty
insertN el (node t x t₁) with ⌊ el ≤? x ⌋
insertN el (node t x t₁) | true = node (insertN el t) x t₁
insertN el (node {l} {r} t x t₁) | false = insertCastLemma l r (node t x (insertN el t₁))

-- Convert the list into a sorted tree
sortTreeN : ∀ {n} → Vec ℕ n → TreeN ℕ n
sortTreeN [] = empty
sortTreeN (x ∷ l) = insertN x (sortTreeN l)

joinCastLemma : ∀ l r → Vec ℕ (l + suc r) → Vec ℕ (suc (l + r))
joinCastLemma l r = subst (Vec ℕ) (+-suc l r)

-- flatten a tree back to a list
joinN : ∀ {n} → TreeN ℕ n → Vec ℕ n
joinN empty = []
joinN (node {l} {r} t x t₁) = joinCastLemma l r (joinN t +++ x ∷ joinN t₁)

-- implement tree sort using the above functions
treeSortN : ∀ {n} → Vec ℕ n → Vec ℕ n
treeSortN l = joinN (sortTreeN l)


-- Task 3.
----------
-- Below you find the definition of list catamorphisms and
-- list paramorphisms.

record Cata (A R : Set) : Set where
  constructor mkCata
  field
    nil : R
    cons : A → R → R

cata : {A R : Set} → Cata A R → List A → R
cata φ [] = Cata.nil φ
cata φ (x ∷ l) = Cata.cons φ x (cata φ l)


record Para (A R : Set) : Set where
  constructor mkPara
  field
    nil : R
    cons : A → List A → R → R

para : {A R : Set} → Para A R → List A → R
para ξ [] = Para.nil ξ
para ξ (x ∷ l) = Para.cons ξ x l (para ξ l)

-- Implement removal of an element from a list as
-- paramorphism:
remove : ℕ → List ℕ → List ℕ
remove a = para (mkPara [] (λ x xs r → if ⌊ x ≟ a ⌋ then r else x ∷ r))

exList1 : List ℕ
exList1 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

exList2 : List ℕ
exList2 = 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

testRemove : remove 3 exList1 ≡ (1 ∷ 2 ∷ 4 ∷ [])
testRemove = refl

open import Function
-- Write the list reversal function as a catamorphism:
rev : Cata ℕ (List ℕ → List ℕ)
rev = mkCata (λ z → z) (λ x f → f ∘ ((_∷_) x))

test2 : (cata rev exList1) [] ≡ exList2
test2 = refl
