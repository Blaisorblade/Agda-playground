--Simplified version
module LeibnizEquality where

{-
data _:=:_ (A : Set) (B : Set) : Set₁ where
  Proof : (∀ {F : Set → Set} → F A → F B) → A :=: B

toPolyId : ∀ {A B} → (A :=: B) → ∀ {C} → C → C
toPolyId (Proof p) = λ {C} → p {λ dummy → C}
-}


open import Level
open import Function using (const; _∘_)

f : ∀ {l} → Set l → Set (suc l)
--f {l} s = Lift {ℓ = suc l} s
f s = Lift s

data _:=:_ {l : Level} (A : Set l) (B : Set l) : Set (suc l) where
  Proof : ({F : Set l → Set l} → F A → F B) → A :=: B
--  Proof : ({F : Set (suc l) → Set l} → F (Lift {ℓ = suc l} A) → F (Lift {ℓ = suc l} B)) → A :=: B

toPolyId : {l : Level} → {A B : Set l} → (A :=: B) → {C : Set l} → C → C
toPolyId (Proof f) = λ {C} → f {const C}

refl : ∀ {l} → ∀ {A : Set l} → A :=: A
refl = Proof (λ z → z)

trans : ∀ {l} → ∀ {A B C : Set l} → A :=: B → B :=: C → A :=: C
trans (Proof a) (Proof b) = Proof (b ∘ a)

symm : ∀ {l} → ∀ {A B : Set l} → A :=: B → B :=: A
symm {l} {A} {B} (Proof p) = Proof (λ {F} → p {λ C → A :=: C} (λ x → x)) -- Proof (λ {F} → p (λ x → x))
{-
--symm {A} {B} (Proof p) with refl {B}
--...            | (Proof r) = Proof (λ {F} → p (λ x → x))
-}