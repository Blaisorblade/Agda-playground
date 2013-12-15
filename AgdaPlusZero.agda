module AgdaPlusZero where

data Nat : Set where
  Z : Nat
  S  : Nat → Nat

_+_ : Nat → Nat → Nat
Z  + n = n
S m + n = S (m + n)

open import Relation.Binary.PropositionalEquality

lem-plus-Z : (n : Nat) → n + Z ≡ n
lem-plus-Z Z = refl
lem-plus-Z (S n) = cong S (lem-plus-Z n)
-- Alternatively, there's a special case which allows to write:
-- lem-plus-Z (S n) rewrite lem-plus-Z n = refl
