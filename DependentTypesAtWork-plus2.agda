module DependentTypesAtWork-plus2 where

open import DependentTypesAtWork-Nat
open import DependentTypesAtWork-eq

-- Let's define plus₂ by induction on the other argument.
plus₂ : Nat -> Nat -> Nat
plus₂ m n = natrec m (\_ -> succ) n

zero-plus₂-right-unit : ∀ {n} → n == plus₂ n zero
zero-plus₂-right-unit = refl
--zero-plus₂-right-unit-useless : ∀ {n} → n == plus₂ n zero
--zero-plus₂-right-unit-useless = eq-refl refl

zero-plus₂-left-unit : ∀ {n} → plus₂ zero n == n
zero-plus₂-left-unit {zero} = refl
zero-plus₂-left-unit {succ n} = congruence succ zero-plus₂-left-unit

-- Ensure that we can lift out the succ also on the left side; on the right side this is obvious to Agda from the definition.
plus₂-succ-n : ∀ m n → plus₂ (succ m) n == succ (plus₂ m n)
plus₂-succ-n m zero = refl
plus₂-succ-n m (succ n) = congruence succ (plus₂-succ-n m n)

plus₂-comm : ∀ m n → plus₂ m n == plus₂ n m
plus₂-comm zero zero = refl
plus₂-comm zero (succ n) with zero-plus₂-right-unit {succ n}
... | refl rewrite (zero-plus₂-left-unit {succ n}) = refl
--Doesn't work:
--plus₂-comm zero (succ n) rewrite zero-plus₂-right-unit {succ n} | (zero-plus₂-left-unit {succ n}) = refl
--Also doesn't work:
--plus₂-comm zero (succ n) rewrite zero-plus₂-right-unit {succ n} = ?
plus₂-comm (succ m) n = lemma₀ where
  --  rewrite congruence succ (plus₂-comm m n)
  lemma₀ : plus₂ (succ m) n == plus₂ n (succ m)
  lemma₀ rewrite plus₂-succ-n m n = congruence succ (plus₂-comm m n)
  -- lemma₀ rewrite (refl {a = zero}) = {!!} -- BUG - Generates non-well-formed goal
{-
plus₂-comm : ∀ m n → plus₂ m n == plus₂ n m
plus₂-comm zero zero = refl
plus₂-comm zero (succ n) = comm-zero-null n where
  comm-zero-null : ∀ n → plus₂ zero (succ n) == plus₂ (succ n) zero
  --comm-zero-null {n}  = eq-trans {!!} lemma-succ-m-rev
  comm-zero-null n with zero-plus₂-right-unit {succ n}
  ... | refl rewrite (zero-plus₂-left-unit {succ n}) = refl
  --Doesn't work:
  --comm-zero-null n rewrite (zero-plus₂-right-unit {succ n}) | (zero-plus₂-left-unit {succ n}) = refl
plus₂-comm (succ m) n = {!!}
-}
