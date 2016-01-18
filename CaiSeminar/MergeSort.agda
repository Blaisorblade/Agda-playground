module MergeSort where

-- Based on:
-- Altenkirch, McBride, McKinna:
-- Why dependent types matter.

open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc)
open import Data.Sum using (inj₁; inj₂)
import Level
open import Relation.Binary.PropositionalEquality using (cong; refl; subst; sym; _≡_)
open import Relation.Binary using (DecTotalOrder) 

data Parity : Set where
  p₀ : Parity
  p₁ : Parity

parityToℕ : Parity → ℕ
parityToℕ p₀ = 0
parityToℕ p₁ = 1

data DealTree (A : Set) : (n : ℕ) → Set where
  empty : DealTree A 0
  leaf : A → DealTree A 1
  node : ∀{n : ℕ} → (p : Parity)
    → (DealTree A ((parityToℕ p) + n))
    → (DealTree A n)
    → DealTree A ((parityToℕ p) + n + n)

insert : ∀{A} → {n : ℕ} → A → DealTree A n → DealTree A (1 + n)
insert x empty = leaf x
insert x (leaf y) = node p₀ (leaf y) (leaf x) 
insert x (node p₀ l r) = node p₁ (insert x l) r
insert x (node {m} p₁ l r) = subst (DealTree _) (cong suc (+-suc m m)) (node p₀ l (insert x r)) 

deal : {n : ℕ} → Vec ℕ n → DealTree ℕ n
deal [] = empty
deal (x ∷ l) = insert x (deal l)

list₁ : Vec ℕ _
list₁ = 1 ∷ 2 ∷ 3 ∷ []

testDeal₁ : deal list₁ ≡ node p₁ (node p₀ (leaf 3) (leaf 1)) (leaf 2)
testDeal₁ = refl

data SortedVec : (n : ℕ) → (lb : ℕ) → Set where
  [] : ∀ {lb : ℕ} → SortedVec 0 lb
  cons : ∀ {n lb : ℕ} → (x : ℕ) → lb ≤ x → SortedVec n x → SortedVec (suc n) lb

merge : ∀ {lb m n : ℕ} → SortedVec m lb → SortedVec n lb → SortedVec (m + n) lb
merge [] ys = ys
merge xs [] = subst (λ m → SortedVec m _) (sym (+-right-identity _)) xs
merge {lb} {m = suc m} {n = suc n} (cons x lb≤x xs) (cons y lb≤y ys) with DecTotalOrder.total decTotalOrder x y
... | inj₁ x≤y = cons x lb≤x (merge xs (cons y x≤y ys))
... | inj₂ y≤x = subst (λ m → SortedVec m lb) (sym ((+-suc (suc m) n))) (cons y lb≤y (merge (cons x y≤x xs) ys))

mergeTree : ∀ {n : ℕ} → DealTree ℕ n → SortedVec n 0
mergeTree empty = []
mergeTree (leaf x) = cons x z≤n []
mergeTree (node _ l r) = merge (mergeTree l) (mergeTree r)

mergeSort : ∀ {n : ℕ} → Vec ℕ n → SortedVec n 0
mergeSort l = mergeTree (deal l)
