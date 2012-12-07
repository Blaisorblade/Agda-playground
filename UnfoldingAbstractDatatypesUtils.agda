module UnfoldingAbstractDatatypesUtils where

data Maybe₂ a b : Set where
  Nothing₂ : Maybe₂ a b
  Just₂ : a → b → Maybe₂ a b

open import Category.Functor public

{-
FmapT : {f : Set → Set} → Set₁
FmapT {f} = ∀ {a b} → (a → b) → (f a → f b)
-}

MaybeF : ∀ {a} → RawFunctor (Maybe₂ a)
MaybeF {a} = record { _<$>_ = fmapM {a} } where
  fmapM : {a b b' : Set} → (b -> b') -> (Maybe₂ a b -> Maybe₂ a b')
  fmapM f Nothing₂ = Nothing₂
  fmapM f (Just₂ x y) = Just₂ x (f y)

data ADT (f : Set → Set) : Set₁ where
  D : {s : Set} → (s → f s) → s → ADT f

--open import Data.Unit

record ⊤ {l} : Set l where
  constructor tt


{-
TreeMaybe₂ : ∀ a → Set
TreeMaybe₂ a = Rec (♯ (Maybe₂ a (TreeMaybe₂ a)))

treeMaybe₂ : ∀ {a} → ADT (Maybe₂ a) → TreeMaybe₂ a
treeMaybe₂ (D h s) = unfold h s
unfold h s
-}
