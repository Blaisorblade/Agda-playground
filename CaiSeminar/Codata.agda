module Codata where

open import Data.Nat hiding (fold)
open import Data.Vec hiding (take; zipWith; head; tail)
open import Size

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : ∀ {j : Size< i} →  Stream {j} A
open Stream

infixr 5 _∷_


zeros : Stream ℕ
head zeros = 0
tail zeros = zeros


test : Stream ℕ
-- test = 0 ∷ 1 ∷ 2 ∷ test
head test = 0
head (tail test) = 1
head (tail (tail test)) = 1
tail (tail (tail test)) = test

{-
_:::_ : ∀ {A} → A → Stream A → Stream A
x ::: xs = {!!}
-}

zipWith : ∀ {i A B C} → (A → B → C) → Stream {i} A → Stream {i} B → Stream {i} C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)


fib : ∀ {i} → Stream {i} ℕ
head fib = 0
head (tail fib) = 1
tail (tail fib) = zipWith _+_ (fib) (tail fib)

fib2 : ∀ i → Stream {i} ℕ
head (fib2 i) = 0
head (tail (fib2 i) {j}) = 1
tail (tail (fib2 i) {j}) {k} = zipWith _+_ (fib2 k) (tail {↑ k} (fib2 (↑ k)) {k})

{-
tail :
Have: {i = i₁ : Size} {A : Set} →
      Stream A → {j = j₁ : Size< i₁} → Stream A
-}

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.List hiding (unfold)

unfold : ∀ {A} {S : Set} → (step : S → A × S) → (s : S) → Stream A
head (unfold step s) = proj₁ (step s)
tail (unfold step s) = unfold step (proj₂ (step s))

fold : ∀ {A S : Set} → (step : ⊤ ⊎ A × S → S) → List A → S
fold f [] = f (inj₁ tt)
fold f (x ∷ xs) = f (inj₂ (x , (fold f xs)))

nat : Stream ℕ
nat = unfold (λ x → x , suc x) 0

coalg : ∀ {A} {B : Set} → (A → B) → Stream A → B × Stream A
coalg f xs = f (head xs) , tail xs

streammap : ∀ {A B} → (A → B) → Stream A → Stream B
streammap f = unfold (coalg f)
