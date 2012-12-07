-- Adapted by P. Giarrusso from
-- The Agda standard library
--
-- Functors

module LawfulFunctor where

open import Function
open import Level
open import Relation.Binary.PropositionalEquality

record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<$>_ _<$_

  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    fusion : ∀ {A B C} → {f : A → B} → {g : B → C} → _<$>_ g ∘ _<$>_ f ≡ _<$>_ (g ∘ f)
    --fusion : fmap f ∘ fmap g ≡ fmap (f ∘ g)

  fmap = _<$>_

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ y = const x <$> y
