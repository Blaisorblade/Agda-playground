module CyclicFin where

open import Agda.Builtin.Equality
open import Agda.Builtin.TrustMe
open import Agda.Builtin.Nat
open import Data.Nat
  renaming ( _+_ to _+ℕ_ ; _^_ to _^ℕ_ ; _<_ to _<ℕ_ )
import Data.Nat.Properties as NatProp
open import Data.Nat.DivMod

open import Relation.Nullary.Decidable.Core
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data U (bits : ℕ) : Set where
    unsigned : (n : ℕ) -> ( n <ℕ (2 ^ℕ bits)) -> U bits


fromNat32 : (n : ℕ)
        -> ((n % (2 ^ℕ 32)) <ℕ (2 ^ℕ 32))
fromNat32  m =  m%n<n m (pred ubound)
  where
    ubound = 2 ^ℕ 32

-- Question: how to write `fromNat` below, generalizing `fromNat32`?
-- Hard!

-- 1. We can modify the question to make this easy.
-- Comments from DivMod recommend writing `m / suc n` and `m % suc n`, since
-- then the proof of {False} can be inferred.
fromNatSimpl : {bits : ℕ} -> (n : ℕ) ->
  n % (suc (pred (2 ^ℕ bits))) <ℕ suc (pred (2 ^ℕ bits))
fromNatSimpl {bits} m = m%n<n m (pred ubound)
  where
    ubound = 2 ^ℕ bits

-- 2. Or we can answer the original question.

2^b≢0 : ∀ n → 2 ^ℕ n ≢ 0
2^b≢0 n 2^n≡0 with NatProp.m^n≡0⇒m≡0 2 n 2^n≡0
... | ()

2^b≢0' : ∀ n → False ((2 ^ℕ n) ≟ 0)
2^b≢0' n = fromWitnessFalse (2^b≢0 n)

-- 2a. Clever way — thanks to Zambonifofex for the idea.

fromNat : {bits : ℕ} -> (n : ℕ) ->
  (n % 2 ^ℕ bits) {2^b≢0' bits} <ℕ 2 ^ℕ bits
fromNat {bits} m with 2 ^ℕ bits | 2^b≢0' bits
fromNat {bits} m | suc n | _ = m%n<n m n
-- Trying `fromNat {bits} m with 2 ^ℕ bits` gives a type error,
-- because the resulting goal still mentions `2^b≢0' bits` as a proof that an
-- arbitrary number (that we abstracted over) is non-zero; so abstract over that
-- proof too.

-- 2b. Hard way.

cong% : ∀ {m n₁ n₂} .{≢0 : False (n₂ ≟ 0)} → (n₁≡n₂ : n₁ ≡ n₂) →
  (m % n₁) {subst (λ n → False (n ≟ 0)) (sym n₁≡n₂) ≢0} ≡ (m % n₂) {≢0}
cong% refl = refl

fromNat' : {bits : ℕ} -> (n : ℕ) ->
  (n % 2 ^ℕ bits) {2^b≢0' bits} <ℕ 2 ^ℕ bits
fromNat' {bits} m =
  begin-strict
    m % ubound
  ≡⟨ cong% (sym ubound+1-1≡ubound) ⟩
    m % suc (pred ubound)
  <⟨ fromNatSimpl {bits} m ⟩
    suc (pred ubound)
  ≡⟨ ubound+1-1≡ubound ⟩
    ubound
  ∎
 --
  where
    ubound = 2 ^ℕ bits
    ubound≠0 : ubound ≢ 0
    ubound≠0 = 2^b≢0 bits
    ubound+1-1≡ubound : suc (pred ubound) ≡ ubound
    ubound+1-1≡ubound = NatProp.suc[pred[n]]≡n ubound≠0
    m' = m % ubound
    open NatProp.≤-Reasoning
