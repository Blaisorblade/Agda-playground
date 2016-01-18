module WhyDependentTypesMatter where

open import Data.List
open import Data.Vec
open import Data.Nat
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

deal₁ : List ℕ → (List ℕ × List ℕ)
deal₁ [] = [] , []
deal₁ (x ∷ []) = x ∷ [] , []
deal₁ (x ∷ y ∷ l) with deal₁ l
... | l₁ , l₂ = x ∷ l₁ ,  y ∷ l₂

data DealTree₁ (A : Set) : Set where
  empty : DealTree₁ A
  leaf : A → DealTree₁ A
  node : DealTree₁ A → DealTree₁ A → DealTree₁ A

{-
insert : ∀ {A} → A → DealTree₁ A → DealTree₁ A
insert = {!!}

deal₂ : List ℕ → DealTree₁ ℕ
deal₂ [] = empty
deal₂ (x ∷ l) = insert x (deal₂ l)

-}

data Parity : Set where
  p₀ : Parity
  p₁ : Parity

_+′_ : Parity → ℕ → ℕ
p₀ +′ n = n
p₁ +′ n = suc n

data DealTree (A : Set) : ℕ → Set where
  empty : DealTree A 0
  leaf : (a : A) → DealTree A 1
  node : ∀ {s} → (p : Parity) → (l : DealTree A (p +′ s)) → (r : DealTree A s) → DealTree A ((p +′ s) + s)

open import Data.Nat.Properties.Simple

insert : ∀ {A n} → A → DealTree A n → DealTree A (suc n)
insert a empty = leaf a
insert a (leaf x) = node p₀ (leaf x) (leaf a)
insert a (node p₀ l r) = node p₁ (insert a l) r
insert {A} a (node {m} p₁ l r) =  subst (λ x → DealTree A (suc x)) (+-suc m m) (node p₀ l (insert a r))

deal : ∀ {n} → Vec ℕ n → DealTree ℕ n
deal [] = empty
deal (x ∷ l) = insert x (deal l)

{-
open import Data.Vec
dealVec : ∀ {n} → Vec ℕ n → DealTree ℕ
dealVec [] = empty
dealVec (x ∷ v) = insert x (dealVec v)
-}

-- list₁ : List ℕ
-- list₁ = 1 ∷ 2 ∷ 3 ∷ []

-- testDeal₁ : deal list₁ ≡ node p₁ (node p₀ (leaf 3) (leaf 1)) (leaf 2)
-- testDeal₁ = refl

{-
merge : List ℕ → List ℕ → List ℕ
merge [] r = r
merge (x ∷ xs) [] = x ∷ xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes p = x ∷ y ∷ merge xs ys
... | no ¬p = y ∷ x ∷ merge xs ys
-}

merge : ∀ {n m} → Vec ℕ n → Vec ℕ m → Vec ℕ (n + m)
merge [] r = r
merge (x ∷ xs) [] = subst (Vec ℕ) (sym (+-right-identity (suc _))) (x ∷ xs)
merge {suc n} (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes p = x ∷ merge xs (y ∷ ys)
... | no ¬p = y ∷ subst (Vec ℕ) (sym (+-suc n _)) (merge (x ∷ xs) ys)


-- mergeTree : ∀ {n} → DealTree ℕ n → Vec ℕ n
-- mergeTree empty = []
-- mergeTree (leaf a) =  a ∷ []
-- mergeTree (node _ l r) = merge (mergeTree l) (mergeTree r)

-- mergeSort : List ℕ → List ℕ
-- mergeSort l = mergeTree (deal l)
