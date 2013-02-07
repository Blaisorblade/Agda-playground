module DeltaGroupoid where

open import Level
open import Algebra
open import Data.Product
open import Data.Bool

open import Algebra.Structures
open import Algebra.FunctionProperties
--open import Relation.Binary.PropositionalEquality
--open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

data Delta (t : Set) : t → t → Set where
  Change : (a : t) → (b : t) → Delta t a b

id : ∀ {t a} → Delta t a a
id {t} {a} = Change a a

inv : ∀ {t a b} → Delta t a b → Delta t b a
inv (Change x₁ x₂) = Change x₂ x₁

append : ∀ {t a b c} → Delta t a b → Delta t b c → Delta t a c
append (Change x₁ x₂) (Change .x₂ y₂) = Change x₁ y₂
  --if (eq x₁ y₂) then NoChange else Change x₁ y₂

assoc-append : ∀ {t a b c d} → (x : Delta t a b) → (y : Delta t b c) → (z : Delta t c d) → append (append x y) z ≡ append x (append y z)
assoc-append {t} {a} {b} {c} {d} (Change .a .b) (Change .b .c) (Change .c .d) = refl

append-idL : ∀ {t a b} → (x : Delta t a b) → append id x ≡ x
append-idL {t} {a} {b} (Change .a .b) = refl

append-idR : ∀ {t a b} → (x : Delta t a b) → append x id ≡ x
append-idR (Change _ _) = refl

left-inv : ∀ {t a b} → (x : Delta t a b) → append x (inv x) ≡ id
left-inv {t} {a} {b} (Change .a .b) = refl
right-inv : ∀ {t a b} → (x : Delta t a b) → append (inv x) x ≡ id
right-inv {t} {a} {b} (Change .a .b) = refl

reassemble : ∀ {t} → (a : t) → {b : t} → Delta t a b → t
reassemble .a {.b} (Change a b) = b

-- What's there to prove after all? Well, there is still something.

reassemble-id : ∀ {t} {a : t} → reassemble a id ≡ a
reassemble-id = refl

lemma-reassemble-result : ∀ {t} → (a : t) → {b : t} → (d1 : Delta t a b) → b ≡ reassemble a d1
lemma-reassemble-result {t} a (Change .a b) = refl


make<_>-compatible-with-<_> : ∀ {t} → {a b c : t} → (d2 : Delta t b c) → (d1 : Delta t a b) → Delta t (reassemble a d1) c
make<_>-compatible-with-<_> {t} {a} {b} {c} d2 d1 = (subst (λ x → Delta t x c) (lemma-reassemble-result a d1) d2)
-- Check that this is indeed right associativity. It seems too obvious.

reassemble-right-assoc : ∀ {t} → {a b c : t} → (d1 : Delta t a b) → (d2 : Delta t b c) →
  reassemble (reassemble a d1) (make< d2 >-compatible-with-< d1 >)
    ≡ reassemble a (append d1 d2)
reassemble-right-assoc (Change a b) (Change .b c) = refl 

{-
DeltaIsSemigroup : {t : Set} → ∀ {eq} → IsSemigroup _≡_ (append {t} {eq})
DeltaIsSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc = assoc-append
  ; ∙-cong = cong₂ append
  }

DeltaIsMonoid : {t : Set} → ∀ {eq} → IsMonoid _≡_ (append {t} {eq}) NoChange
DeltaIsMonoid {t} = record
  { isSemigroup = DeltaIsSemigroup
  ; identity = append-idL , append-idR
  }

-- Delta is in fact not a group. We can only provide inverses if we give up having a single identity and make this a category.
{-
DeltaIsGroup : (t : Set) → (eq : t → t → Bool) → Group zero zero
DeltaIsGroup t eq = record {
                   Carrier = Delta t eq;
                   _≈_ = _≡_;
                   _∙_ = append;
                   ε = NoChange;
                   _⁻¹ = inv;
                   isGroup = record { isMonoid = DeltaIsMonoid; inverse = {!!} , {!!}; ⁻¹-cong = cong inv } }
-}
-}
