-- Let's try to use the result of xs++[]=xs as an equality.
-- This problem was posted by Fuuzetsu on the #agda IRC channel.

module VectorEqualityExtras (A : Set) where

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; ≡-to-≅)

open import Function

open import Data.Vec
open import Data.Vec.Properties
open import Data.Vec.Equality
open UsingVectorEquality (setoid A)
open PropositionalEquality

{-
-- Does not work. The problem is that vector equality is semi-heterogeneous, in
-- that the two compared vectors do not need to have, a priori, the same length.
-- So you can't convert it to a homogeneous equality.
xs++[]=xs-propEq : ∀ {n} → (xs : Vec A n) → (xs ++ []) ≡ xs
xs++[]=xs-propEq xs = to-≡ (xs++[]=xs xs)
-}

to-≅ : ∀ {a} {A : Set a} {m n} {xs : Vec A m} {ys : Vec A n} → xs ≈ ys → xs ≅ ys
to-≅ p with length-equal p
to-≅ p | P.refl = ≡-to-≅ (to-≡ p)

≅-to-t-≡ : ∀ {a} {A B : Set a} {xs : A} {ys : B} → (p : xs ≅ ys) → A ≡ B
≅-to-t-≡ H.refl = P.refl

-- If you need a propositional equality, you'll have to use subst on one side.
-- However, we can do that for you, in different ways.

-- A generic way to convert heterogeneous to homogeneous equality.
≅-to-subst-≡ : ∀ {a} {A B : Set a} {xs : A} {ys : B} → (p : xs ≅ ys) → subst (λ x → x) (≅-to-t-≡ p) xs ≡ ys
≅-to-subst-≡ H.refl = P.refl

-- We can use it to build the following:
to-subst-≡′ : ∀ {a} {A : Set a} {m n} {xs : Vec A m} {ys : Vec A n} → (p : xs ≈ ys) → subst (λ x → x) (≅-to-t-≡ (to-≅ p)) xs ≡ ys
to-subst-≡′ = ≅-to-subst-≡ ∘ to-≅

-- A more specific one, with a more precise type for you.
to-subst-≡ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → (p : xs ≈ ys) → subst (Vec A) (length-equal p) xs ≡ ys
to-subst-≡ {xs = xs} p = H.≅-to-≡
  (H.trans
    (H.≡-subst-removable (Vec A) (length-equal p) xs)
    (to-≅ p))

-- Working variants of xs++[]=xs-propEq:
xs++[]=xs-hEq : ∀ {n} → (xs : Vec A n) → (xs ++ []) ≅ xs
xs++[]=xs-hEq xs = to-≅ (xs++[]=xs xs)

xs++[]=xs-subst-propEq : ∀ {n} → (xs : Vec A n) → subst (Vec A) (length-equal (xs++[]=xs xs)) (xs ++ []) ≡ xs

-- Without to-subst-≡, we need an inlined version of it:
{-
xs++[]=xs-subst-propEq xs = H.≅-to-≡
  (H.trans
    (H.≡-subst-removable (Vec A) (length-equal (xs++[]=xs xs)) (xs ++ []))
    (xs++[]=xs-hEq xs))
-}

xs++[]=xs-subst-propEq xs = to-subst-≡ (xs++[]=xs xs)
