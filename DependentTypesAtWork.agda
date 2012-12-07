module DependentTypesAtWork where

open import DependentTypesAtWork-Nat
open import DependentTypesAtWork-+
open import DependentTypesAtWork-plus1
open import DependentTypesAtWork-plus2
open import DependentTypesAtWork-eq

{-
eq-succ : ∀ {m n} → m == n → (succ m == succ n)
--eq-succ {.m} {.m} (refl m) = refl (succ m) --Works
--eq-succ {m} {n} = congruence succ {m} {n} -- Abstracted version
eq-succ = congruence succ -- Abstracted version, v2
--eq-succ = subst {C = succ} --This would probably work, given enough polymorphism. Except that for some 
-}

eq-plus₁-step : ∀ {m n} → (m + n == plus₁ m n) → (succ m + n) == plus₁ (succ m) n
eq-plus₁-step {m} {n} m+n=plus₁mn = congruence succ {m + n} {plus₁ m n} m+n=plus₁mn

eq-plus₁-rec : (m n : Nat) → (m + n) == (plus₁ m n)
eq-plus₁-rec m n = natrec {λ m → (m + n) == (plus₁ m n)} refl (λ m₁ m+n=plus₁mn → eq-plus₁-step {m₁} {n} m+n=plus₁mn) m

eq-plus₁ : (m n : Nat) → (m + n) == (plus₁ m n)
eq-plus₁ zero n     = refl
eq-plus₁ (succ m) n = congruence succ {m + n} {plus₁ m n} (eq-plus₁ m n)

-- More compact, but (?) less readable (?)
eq-plus₁-rec₂ : (m n : Nat) → (m + n) == (plus₁ m n)
eq-plus₁-rec₂ m n = natrec {λ m → (m + n) == (plus₁ m n)} refl (λ m₁ m+n=plus₁mn → congruence succ m+n=plus₁mn) m

eq-plus₁' : (m n : Nat) → (m + n) == (plus₁ m n)
eq-plus₁' zero n     = refl
eq-plus₁' (succ m) n = congruence succ (eq-plus₁' m n)

{-
eq-plus₂ : (m n : Nat) → (m + n) == (plus₂ m n)
eq-plus₂ zero zero = refl
eq-plus₂ zero (succ n) = congruence succ (eq-plus₂ zero n)
eq-plus₂ (succ m) zero = congruence succ (eq-plus₂ m zero)
--eq-plus₂ (succ m) (succ n) = eq-trans (+-comm (succ m) (succ n)) (congruence succ (eq-trans (+-comm n (succ m)) (eq-plus₂ (succ m) n)))

-- Explanation of the last (now commented out) equation:
-- n + (succ m) = {+-comm n (succ m)}
-- succ m + n = {eq-plus₂ (succ m) n}
-- plus₂ (succ m) n

-- (succ m) + (succ n) = {+-comm (succ m) (succ n)}
-- (succ n) + (succ m) = {congruence succ of the proof that `n + (succ m) = plus₂ (succ m) n`}
-- succ (plus₂ (succ m) n) = plus₂ (succ m) (succ n)

eq-plus₂ (succ m) (succ n) rewrite +-comm (succ m) (succ n) = congruence succ lemma where
  lemma : n + succ m == plus₂ (succ m) n
  --lemma = (congruence succ (eq-trans (+-comm n (succ m)) (eq-plus₂ (succ m) n)))
  lemma rewrite +-comm n (succ m) | eq-plus₂ (succ m) n = refl
-}

eq-plus₂ : (m n : Nat) → (m + n) == (plus₂ m n)
eq-plus₂ m zero = lemma₀ where
  -- Instead of recursion on eq-plus₂:
  --lemma₀ {zero} = refl
  --lemma₀ {(succ m)} = congruence succ (eq-plus₂ m zero)
  -- Use the properties of zero.
  lemma₀ : ∀ {m} → m + zero == plus₂ m zero
  lemma₀ = +-zero-right-unit _
eq-plus₂ m (succ n) rewrite +-comm m (succ n) = congruence succ lemma-after-comm where
  lemma-after-comm : n + m == plus₂ m n
  lemma-after-comm rewrite +-comm n m | eq-plus₂ m n = refl

