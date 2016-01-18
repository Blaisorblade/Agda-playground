module GenericProgramming where

open import Data.Sum
open import Data.Product
open import Function
open import Size

data Functor : Set₁ where
  |Id| : Functor
  |K| : (X : Set) → Functor
  _|+|_ : Functor → Functor → Functor
  _|×|_ : Functor → Functor → Functor

⟦_⟧ : Functor → Set → Set
⟦_⟧ |Id| X = X
⟦_⟧ (|K| X) _ = X
⟦_⟧ (F |+| G) X = (⟦ F ⟧ X) ⊎ (⟦ G ⟧ X)
⟦_⟧ (F |×| G) X = (⟦ F ⟧ X) × (⟦ G ⟧ X)

fmap : ∀ {F X Y} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
fmap {|Id|} f = f
fmap {|K| X} f = id
fmap {F |+| G} f = Data.Sum.map (fmap {F} f) (fmap {G} f)
fmap {F |×| G} f = Data.Product.map (fmap {F} f) (fmap {G} f)

data μ_ (F : Functor) : Set where
  <_> : ⟦ F ⟧ (μ F) → μ F

open import Data.Unit

NatF = |K| ⊤ |+| |Id|
NAT = μ NatF

Z : NAT
Z = < inj₁ tt >

S : NAT → NAT
S n = < inj₂ n >

-- To fix this problem, maybe fuse fold' and map.
fold' : ∀ F {X} → (⟦ F ⟧ X → X) → μ F → X
fold' F φ < x > =
  let f = fold' F φ in
  φ (fmap {F} f x)
