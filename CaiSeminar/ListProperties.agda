module ListProperties where

open import Algebra using (Monoid)
open import Algebra.FunctionProperties using (Associative; Identity; RightIdentity)
open import Algebra.Morphism
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties.Simple
open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Function using () renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core using (_Preserves_⟶_; Rel)

-- some basic definitions
id : ∀ {A : Set} → A → A
id x = x

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

map : ∀ {A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {A} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)



-- Some definitions for later. Don't peek!
nat-monoid : Monoid _ _
nat-monoid = record {
        Carrier = ℕ;
        _≈_     = _≡_;
        _∙_     = _+_;
        ε       = 0;
        isMonoid = record {
          isSemigroup = record {
            isEquivalence = isEquivalence;
            assoc         = +-assoc;
            ∙-cong        = cong₂ _+_
          };
          identity = (λ _ → refl) , +-right-identity
        }
      }

-- Define a monoid morphism between two monoids.
-- The first few implicit parameters are just universe levels for the monoid definitions.
-- By definition, the monoid morphism must at least have the same level.
record _-Monoid⟶_ {r₁ r₂ r₃ r₄}
                    (From : Monoid r₁ r₂) (To : Monoid r₃ r₄) : 
                    Set (r₁ ⊔ r₂ ⊔ r₃ ⊔ r₄) where
       private
         module F = Algebra.Monoid From
         module T = Algebra.Monoid To
       open Definitions F.Carrier T.Carrier T._≈_
       
       field
         -- this is the actual function computing the morphism
         ⟦_⟧ : Morphism
         -- the morphism must respect the given equality, obviously
         ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
         -- it should also respect the monoid's operation ∙ and the identity ε
         ∙-homo : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_
         ε-homo : Homomorphic₀ ⟦_⟧ F.ε T.ε