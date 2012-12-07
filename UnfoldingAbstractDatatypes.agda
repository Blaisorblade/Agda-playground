{-# OPTIONS --guardedness-preserving-type-constructors #-}

{-
{-# LANGUAGE DeriveFunctor, ExistentialQuantification #-}
data Maybe2 a b = Nothing2 | Just2 a b deriving Functor

--data Functor f => ADT f = forall s. D (s -> f s) s
data ADT f = forall s. D (s -> f s) s

data Tree f = T { unt :: f (Tree f) }

tree :: Functor f => ADT f -> Tree f
tree (D h s) = unfold h s

unfold :: Functor f => (a -> f a) -> a -> Tree f
unfold f x = T (fmap (unfold f) (f x))

-}

module UnfoldingAbstractDatatypes where

open import UnfoldingAbstractDatatypesUtils

open import Data.Nat hiding (fold)
open import Data.List

unfoldr : ∀ {a b} → (b → Maybe₂ a b) → b → List a
unfoldr f y with f y
... | Nothing₂ = []
... | Just₂ x y' = x ∷ unfoldr f y'

open import Coinduction renaming (unfold to unfoldRec)

--test, taken from Coinduction
open import Data.Sum

ℕ₂ : Set
ℕ₂ = ⊤ ⊎ Rec (♯ ℕ₂)

{-
open import Data.Sum
open import Data.Unit
-}

Tree : ∀ {l} → (f : Set l → Set l) → Set l
Tree f = Rec (♯ (f (Tree f)))

unT = unfoldRec

-- Intrinsically nonterminating
unfoldT : ∀ {a f} → RawFunctor f → (a → f a) → a → Tree f

tree : ∀ {f} → RawFunctor f → ADT f → Tree f
tree f (D h s) = unfoldT f h s

unfoldT rf f x = let open RawFunctor rf in fold ((unfoldT rf f) <$> (f x))

open import Level
open import Relation.Binary.PropositionalEquality
open import Function

postulate
  universalUnfoldT : ∀ {F A h f} → (rf : RawFunctor F) →
    let open RawFunctor rf in h ≡ unfoldT {a = A} rf f → unT ∘ h ≡ _<$>_ h ∘ f
  universalUnfoldTRev : ∀ {F A h f} → (rf : RawFunctor F) →
    let open RawFunctor rf in unT ∘ h ≡ _<$>_ h ∘ f → h ≡ unfoldT {a = A} rf f

{-
-- Won't work - normalizing this _type_ involves infinite recursion!!
lemma : ∀ {F A} → (rf : RawFunctor F) →
    let open RawFunctor rf in ∀ {f g f'} → f ∘ g ≡ (_<$>_ g) ∘ f' → (unfoldT {a = A} rf f) ∘ g ≡ unfoldT {a = A} rf f'
lemma {F} {A} rf {f} {g} {f'} eq = cong ? {!!} where
  y = let open RawFunctor rf in cong (_∘_ (_<$>_ (unfoldT {a = A} rf f))) eq
-}

--tree : ∀ f → ADT f → FmapT f → Tree f
{-
data Tree (f : Set → Set) : Set where
  T : f (Tree f) → Tree f
-}
{-
record Tree (f : Set → Set) : Set where
  field treeField : f (Tree f)
-}