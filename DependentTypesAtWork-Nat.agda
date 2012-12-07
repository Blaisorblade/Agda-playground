module DependentTypesAtWork-Nat where

-- From 2.2, Natural Numbers
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

-- From 2.5, Gödel System T
--natrec : {C : Set} -> C -> (Nat -> C -> C) -> Nat -> C
--natrec base step zero = base
--natrec base step (succ n) = step n (natrec base step n)

-- From 4.4, Induction Principles
natrec : {C : Nat -> Set} -> C zero -> ((n : Nat) → C n → C (succ n)) → (n : Nat) → C n
natrec base step zero = base
natrec base step (succ n) = step n (natrec base step n)
--Note that the equations are the same, only the type is more general! That happens maybe not always but often - the reason is that the equations only define
--the computational behavior, which is the same; moreover, already the base definition (without dependent types) has no error cases.

