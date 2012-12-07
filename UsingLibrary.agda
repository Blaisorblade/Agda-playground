module UsingLibrary where

open import Relation.Binary.PropositionalEquality


eq-trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
eq-trans = trans

{- Try out doing more stuff using Agda's library - say, the exercises I did for DependentTypesAtWork.
-}