module DeltaGroup where

open import Level
open import Algebra
open import Data.Product
open import Data.Bool

open import Algebra.Structures
open import Algebra.FunctionProperties
--open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

data Delta (t : Set) (eq : t → t → Bool): Set where
  NoChange : Delta t eq
  Change   : t → t → Delta t eq

inv : ∀ {t eq} → Delta t eq → Delta t eq
inv NoChange = NoChange
inv (Change x₁ x₂) = Change x₂ x₁

append : ∀ {t eq} → Delta t eq → Delta t eq → Delta t eq
append NoChange b = b
append a NoChange = a
append {eq = eq} (Change x₁ x₂) (Change y₁ y₂) = Change x₁ y₂
  --if (eq x₁ y₂) then NoChange else Change x₁ y₂

append-idL : ∀ {t eq} → (x : Delta t eq) → append NoChange x ≡ x
append-idL x = refl

append-idR : ∀ {t eq} → (x : Delta t eq) → append x NoChange ≡ x
append-idR NoChange = refl
append-idR (Change _ _) = refl

ifTrue : {T : Set} → ∀ (a b : T) → (if_then_else_ true a b) ≡ a
ifTrue a b = refl

assoc-append : ∀ {t eq} → (x y z : Delta t eq) → append (append x y) z ≡ append x (append y z)
assoc-append NoChange y z = refl
-- What a mess!
--assoc-append x NoChange z = cong (λ x₁ → append x₁ z) (append-idR x)
--assoc-append x y NoChange with append-idR (append x y) | append-idR y
--... | eq₁ | eq₂ = trans eq₁ (sym ((cong (append x) eq₂)))

-- With rewrite, life is simpler!
assoc-append x NoChange z rewrite (append-idR x) = refl
assoc-append x y NoChange rewrite append-idR (append x y) | append-idR y = refl
assoc-append {t} {eq} (Change x₁ x₂) (Change y₁ y₂) (Change z₁ z₂) = refl
{-assoc-append {t} {eq} (Change x₁ x₂) (Change y₁ y₂) (Change z₁ z₂) with eq x₁ y₂ | eq y₁ z₂
... | true | true = x
  where
    equal = ifTrue (NoChange {t} {eq}) (Change x₁ y₂)
    x : (append (if true then NoChange else Change x₁ y₂) (Change z₁ z₂) ≡
      append (Change x₁ x₂) (if true then NoChange else Change y₁ z₂))
    x with true
    ... | true = {!!}
    ... | false = {!!}

assoc-append (Change x₁ x₂) (Change y₁ y₂) (Change z₁ z₂) | true | false = {!!}
... | false | eqB = {!!}-}

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