module RawArrow where

{- Answer to http://stackoverflow.com/q/13112642/53974, derived from
the other answer. -}

open import Data.Product --actually needed by RawArrow
open import Data.Fin     --only for examples
open import Data.Nat     --ditto

record RawArrow (A : (S : Set) → (T : {s : S} → Set) → Set) : Set₁ where
  field
    arr    : ∀ {B C} → (B → C) → A B C
    _>>>_  : ∀ {B C D} → A B C → A C D → A B D
    first  : ∀ {B C D} → A B C → A (B × D) (C × D)
    second : ∀ {B C D} → A B C → A (D × B) (D × C)
    _***_  : ∀ {B C B' C'} → A B C → A B' C' → A (B × B') (C × C')
    _&&&_  : ∀ {B C C'} → A B C → A B C' → A B (C × C')

_=>_ : (S : Set) → (T : {s : S} → Set) → Set
A => B = (a : A) -> B {a}

test1 : Set
test1 = ℕ => ℕ
-- With → we can also write:
test2 : Set
test2 = (n : ℕ) → Fin n
-- But also with =>, though it's more cumbersome:
test3 : Set
test3 = ℕ => (λ {n : ℕ} → Fin n)
--Note that since _=>_ uses Set instead of being level-polymorphic, it's still
--somewhat limited. But I won't go the full way.

--fnRawArrow : RawArrow _=>_
-- Alternatively:
fnRawArrow : RawArrow (λ A B → (a : A) → B {a})

fnRawArrow = record
  { arr    = λ f → f
  ; _>>>_  = λ g f x → f (g x)
  ; first  = λ { f (x , y) → (f x , y) }
  ; second = λ { f (x , y) → (x , f y) }
  ; _***_  = λ { f g (x , y) → (f x , g y) }
  ; _&&&_  = λ f g x → (f x , g x)
  }
