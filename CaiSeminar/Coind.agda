module Coind where

open import Coinduction
open import Data.Nat
open import Data.Vec hiding (take; zipWith; head; tail)

data Stream (A : Set) : Set where
  _∷_ : A → ∞ (Stream A) → Stream A

infixr 5 _∷_

zeros : Stream ℕ
zeros = 0 ∷ ♯ zeros

take : {A : Set} → (n : ℕ) → Stream A → Vec A n
take zero xs = []
take (suc n) (x ∷ xs) = x ∷ (take n (♭ xs))

test : Stream ℕ
test = 0 ∷ ♯ (1 ∷ ♯ (2 ∷ ♯ test))

zipWith : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
zipWith f (x ∷ xs) (y ∷ ys) = (f x y) ∷ (♯ (zipWith f (♭ xs) (♭ ys)))


head : ∀ {A} → Stream A → A
head (x ∷ _) = x

tail : ∀ {A} → Stream A → Stream A
tail (x ∷ xs) = ♭ xs

zipWith2 : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
zipWith2 f xs ys = f (head xs) (head ys) ∷ ♯ (zipWith f (tail xs) (tail ys))

{-# NON_TERMINATING #-}
fib : Stream ℕ
fib = 0 ∷ ♯ (1 ∷ ♯ zipWith _+_ fib (tail fib))

{-
fib2 : Stream ℕ
fib2 = 0 ∷ ♯ (1 ∷ ♯ zipWith _+_ fib2 (tail fib2))
-}
