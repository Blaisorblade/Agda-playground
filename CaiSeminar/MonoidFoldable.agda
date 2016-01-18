module MonoidFoldable where


-- Stolen from https://github.com/UlfNorell/agda-prelude/blob/703ef7a4505849a6da84b7d7343b8ad89da12fcb/src/Data/Foldable.agda and https://github.com/UlfNorell/agda-prelude/blob/703ef7a4505849a6da84b7d7343b8ad89da12fcb/src/Data/Monoid.agda
-- Adaptation

open import Function using (id)
open import Data.Maybe
open import Data.List
open import Level renaming (suc to lsuc)

-- Start
record Monoid {a} (A : Set a) : Set a where
  infixr 6 _<>_
  field
    mempty : A
    _<>_   : A → A → A

open Monoid {{...}} public

mconcat : ∀ {a} {A : Set a} {{MonA : Monoid A}} → List A → A
mconcat = foldr _<>_ mempty

record Foldable {a b w} (F : Set a → Set b) : Set (lsuc w ⊔ lsuc a ⊔ b) where
  field
    foldMap : ∀ {A}{W : Set w} {{MonW : Monoid W}} → (A → W) → F A → W

open Foldable {{...}} public

fold : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{MonW : Monoid W}} → F W → W
fold = foldMap id

--- Instances ---

instance
  FoldableList : ∀ {a w} → Foldable {a = a} {w = w} List
  FoldableList = record { foldMap = λ f → foldr (λ x w → f x <> w) mempty }

  FoldableMaybe : ∀ {a w} → Foldable {a = a} {w = w} Maybe
  FoldableMaybe = record { foldMap = λ f → maybe f mempty }
