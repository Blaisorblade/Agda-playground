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

reassemble-result : ∀ {t} → (a : t) → {b : t} → (d1 : Delta t a b) → reassemble a d1 ≡ b
reassemble-result {t} a {b} (Change .a .b) = refl

reassemble-append-res : ∀ {t} → {a b c : t} → (d1 : Delta t a b) → (d2 : Delta t b c) → c ≡ reassemble a (append d1 d2)
reassemble-append-res {t} {a} {b} {c} (Change .a .b) (Change .b .c) = refl

-- Check that this is indeed right associativity. It seems too obvious.

--reassemble-right-assoc : ∀ {t} → {a b c : t} → {d1 : Delta t a b} → {d2 : Delta t b c} → reassemble (reassemble a d1) d2 ≡ reassemble a (append d1 d2)
--reassemble-right-assoc = ?
reassemble-right-assoc1 : ∀ {t} → {a b c : t} → (d1 : Delta t a b) → (d2 : Delta t b c) → reassemble b d2 ≡ reassemble a (append d1 d2)
reassemble-right-assoc1 {t} {a} {b} {c} d1 d2 = trans (reassemble-result b d2) (reassemble-append-res d1 d2)

reassemble-right-assoc : ∀ {t} → {a b c : t} → (d1 : Delta t a b) → (d2 : Delta t b c) →
  reassemble (reassemble a d1)
    (subst (λ x → Delta t x c)
      (sym (reassemble-result a d1))
    d2)
    ≡ reassemble a (append d1 d2)
reassemble-right-assoc (Change a b) (Change .b c) = refl 
{-
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
-}
