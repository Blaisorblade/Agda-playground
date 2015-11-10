module 03hw where

open import Data.List hiding (partition)
open import Data.Vec hiding (split; _++_)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec

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
insert el t = {!!}

-- Convert the list into a sorted tree
sortTree : List ℕ → Tree ℕ
sortTree l = {!!}

-- flatten a tree back to a list
join : Tree ℕ → List ℕ
join t = {!!}

-- implement tree sort using the above functions
treeSort : List ℕ → List ℕ
treeSort l = {!!}


-- Task 2.
----------
-- Modify the above definitions to also prove that the sorted
-- list has the same length als the input-list.
-- The signature of treeSort will change to:
--
--     treeSort : {n : ℕ} → Vec ℕ n → Vec ℕ n


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
remove a = para {!!}

exList1 : List ℕ
exList1 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

exList2 : List ℕ
exList2 = 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

testRemove : remove 3 exList1 ≡ (1 ∷ 2 ∷ 4 ∷ [])
testRemove = refl

-- Write the list reversal function as a catamorphism:
rev : Cata ℕ (List ℕ → List ℕ)
rev = mkCata {!!} {!!}

test2 : (cata rev exList1) [] ≡ exList2
test2 = refl
