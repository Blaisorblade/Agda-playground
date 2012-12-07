module DependentTypesAtWork-plus1 where

open import DependentTypesAtWork-Nat
open import DependentTypesAtWork-eq

-- From 2.5, Gödel System T
plus₁ : Nat -> Nat -> Nat
plus₁ m n = natrec n (\_ -> succ) m

plus₁-succ-n : ∀ m n → plus₁ m (succ n) == succ (plus₁ m n)
plus₁-succ-n zero n = refl
plus₁-succ-n (succ m) n = congruence succ (plus₁-succ-n m _)

plus₁-comm : ∀ m n → plus₁ m n == plus₁ n m
plus₁-comm zero     zero      = refl
plus₁-comm (succ m) zero      = congruence succ (plus₁-comm m zero)
--plus₁-comm m (succ n) = eq-trans (plus₁-succ-n m n) (congruence succ (plus₁-comm m n))
plus₁-comm m        (succ n)  rewrite plus₁-succ-n m n = congruence succ (plus₁-comm m n)