-- Exercise following
-- http://www2.tcs.ifi.lmu.de/~abel/Equality.pdf

module Equality where
open import Relation.Binary.PropositionalEquality
open import Data.List


++-assoc : ∀ {a} {A : Set a} (xs ys zs : List A) →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
{-
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)
-}

open ≡-Reasoning
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨ refl ⟩
   ys ++ zs
  ≡⟨ refl ⟩
    [] ++ ys ++ zs
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨ refl ⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨ {! -l!} ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨ refl ⟩
    (x ∷ xs) ++ (ys ++ zs)
  ∎
