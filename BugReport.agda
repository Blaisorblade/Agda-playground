module BugReport where

data _==_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a == a

infixl 20 _==_

-- Works:
--eq-trans : ∀ {A} {a : A} → ∀ {b c} → a == b → b == c → a == c
--eq-trans (refl c) (refl .c) = refl c

eq-trans : ∀ {a b c} → a == b → b == c → a == c
eq-trans {.c} {.c} {c} (refl .c) (refl .c) = {!!}
