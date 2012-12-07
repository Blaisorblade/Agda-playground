module DependentTypesAtWork-eq where
import Level

--From 3.3, Other Interesting Inductive Families
data _==_ {l} {A : Set l} (a : A) : A → Set l where
  refl : a == a
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

infixl 20 _==_

eq-trans : ∀ {l} {A : Set l} {a : A} → ∀ {b c} → a == b → b == c → a == c
eq-trans refl refl = refl

eq-refl : ∀ {l} {A : Set l} {a b : A} → a == b → b == a
eq-refl refl = refl

--From 4.3, Equality
subst : {A : Set} -> {C : A -> Set} -> (a' a'' : A) → a' == a'' → C a' → C a''
subst .a a refl x = x

-- For some confusing reason, while this is close to subst the result is not: this is not a coercion between types, just
-- a producer of proofs. I'm not sure what that means.
congruence : ∀ {l} {T : Set l} → {A : Set} -> (C : A -> T) -> {a' a'' : A} → a' == a'' → C a' == C a''
congruence C {a} {.a} refl = refl
