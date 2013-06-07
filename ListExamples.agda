module ListExamples where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Level

-- Declare a heterogeneous, typed list.
-- We use Γ for lists of types. Set is Agda's name for Type.

data MyList : List Set → Set₁ where
  nil : MyList []
  -- Braces enclose implicit arguments. They can be placed anywhere.
  -- This would be useful also in Scala (http://blaisorbladeprog.blogspot.de/2013/01/flexible-implicits-from-agda-for-scala.html)
  cons : ∀ {τ Γ} → (v : τ) → (vs : MyList Γ) → MyList (τ ∷ Γ)

-- An inductive definition of a proof that a list of types contains another list of types.
data _contains_ : List Set → List Set → Set₁ where
  empty : [] contains []
  dropFirst : ∀ {Γ₁ Γ₂ τ} → (contain : Γ₁ contains Γ₂) → (τ ∷ Γ₁) contains Γ₂
  keepFirst : ∀ {Γ₁ Γ₂ τ} → (contain : Γ₁ contains Γ₂) → (τ ∷ Γ₁) contains (τ ∷ Γ₂)

filterTypes : ∀ {Γ Γ′} → MyList Γ → Γ contains Γ′ → MyList Γ′

filterTypes nil         empty               = nil
filterTypes (cons v vs) (dropFirst contain) = filterTypes vs contain
filterTypes (cons v vs) (keepFirst contain) = cons v (filterTypes vs contain)

-- If you want to see better what's going on
filterTypes2 : ∀ Γ Γ′ → MyList Γ → Γ contains Γ′ → MyList Γ′

filterTypes2 .[]      .[]       nil         empty                = nil
filterTypes2 (x ∷ xs) Γ′        (cons v vs) (dropFirst contains) = filterTypes2 xs Γ′ vs contains
-- Here, type refinement tells that x and .x must match, so we use a dot for the second and do 
filterTypes2 (x ∷ xs) (.x ∷ Γ₂) (cons v vs) (keepFirst contains) = cons v (filterTypes2 xs Γ₂ vs contains)


{-
filterTypes2 (x ∷ xs) Γ′ (cons x₁ x₂) (dropFirst x₃) = filterTypes2 xs Γ′ x₂ x₃
filterTypes2 (x ∷ xs) .(x ∷ Γ₂) (cons x₁ x₂) (keepFirst {.xs} {Γ₂} x₃) = cons x₁ (filterTypes2 xs Γ₂ x₂ x₃)
-}
{-
filterTypes2 [] [] nil empty = nil
filterTypes2 (τ₁ ∷ τs) Γ′ (cons x l) (dropFirst contains) = filterTypes2 _ _ l contains
filterTypes2 (τ₁ ∷ τs) .(τ₁ ∷ Γ₂) (cons x l) (keepFirst {.τs} {Γ₂} contains) = cons x (filterTypes2 τs Γ₂ l contains)
-}

{-
filterTypes {[]} {[]} nil empty = nil
filterTypes {[]} {x ∷ Γ′} nil ()
filterTypes (cons x l) contains = {!!}
-}


--open import decSetoid

data Pair : Set₁ where
  pair : ∀ (τ : Set) (v : τ) → Pair

{-
filterTypes : List Pair → List Set → List Pair
filterTypes [] [] = []
filterTypes [] (x ∷ types) = []
filterTypes (x ∷ pairs) [] = []
--filterTypes (pair τ v ∷ pairs) (τ′ ∷ types) = {!!}
filterTypes (pair τ v ∷ pairs) (τ′ ∷ types) with τ ≟ τ′
... | x = ?
-}
