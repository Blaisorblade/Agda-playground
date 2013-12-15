module MixfixAmbiguity where

-- open import Data.Bot
open import Data.Nat

-- Ꙭ
-- icicles-mode

-- ∶: :: ∷

-- _≡_,_ = 1
-- _,_ = 1

_a_b_c_ = 1
_b_ = 1
_a_c_ = 1

-- ≟

-- Ambiguous, can't be disambiguated with parentheses - not for all objects.
--foo = 1 a 2 b 3 c 4

-- Doesn't type-check, but that's irrelevant to the example.
-- foo2 = 1 a (2 b 3) c 4
