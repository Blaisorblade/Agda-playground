module DependentTypesAtWork-+ where

open import DependentTypesAtWork-Nat

_+_ : Nat -> Nat -> Nat
zero   + n = n
succ m + n = succ (m + n)

infixl 40 _+_

open import DependentTypesAtWork-eq

+-succ-n : ∀ m n → m + succ n == succ (m + n)
+-succ-n zero zero = refl
+-succ-n zero (succ n) = refl
+-succ-n (succ m) n = congruence succ (+-succ-n m n)

-- +-comm : ∀ m n → m + n == n + m
-- +-comm zero zero = refl zero
-- +-comm zero (succ n) = congruence succ (+-comm zero n)
-- +-comm (succ m) zero = congruence succ (+-comm m zero)
-- +-comm (succ m) (succ n) = eq-trans (+-succ-n (succ m) n) (congruence succ (+-comm (succ m) n))

-- +-succ-n m n: m + succ n == succ (m + n); succ (m + n) == succ (n + m) by congruence succ (+-comm m n); finally, succ (n + m) == succ n + m. Do all this after m |-> succ m, and get transitivity of equality in some way.
-- +-succ-n (succ m) n : (succ m) + succ n == succ ((succ m) + n). congruence succ (+-comm (succ m) n) : (succ ((succ m) + n) == succ (n + succ m)); finally, by definition, succ (n + succ m) == (succ n + succ m)

+-zero-right-unit : ∀ m → m + zero == m
+-zero-right-unit zero = refl
+-zero-right-unit (succ m) = congruence succ (+-zero-right-unit m)

+-comm : ∀ m n → m + n == n + m
+-comm m zero = +-zero-right-unit m
--+-comm m (succ n) = eq-trans (+-succ-n m n) (congruence succ (+-comm m n))
+-comm m (succ n) rewrite +-succ-n m n = congruence succ (+-comm m n)
