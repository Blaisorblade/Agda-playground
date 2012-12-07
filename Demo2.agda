module Demo2 where

open import Data.Nat

data List (A : Set) : Set where
  ∅ : List A
  _,_ : A -> List A -> List A

infixr 3 _,_

test-123 : List ℕ
--\bn = N
test-123 = 1 , 2 , 3 , ∅

--map : {A B : _} → (A → B) → (List A → List B)
map : ∀ {A B} → (A → B) → (List A → List B)
map f ∅ = ∅
map f (x , xs) = f x , map f xs

-- PART II ∙ Proving Stuff
-- ======================

-- map fusion!
-- map f ∘ map g = map (f ∙ g)
-- but we're going to make this more pointful to avoid function equality.

data _≣_ {A : Set} : A → A → Set where
  refl : ∀ {a} -> a ≣ a

--\_2
cong₂ : ∀ {A B C} → ∀ {x₁ x₂ y₁ y₂} → ∀ (f : A → B → C) → x₁ ≣ x₂ → (y₁ ≣ y₂) → (f x₁ y₁ ≣ f x₂ y₂)
cong₂ f refl refl = refl

map-fusion : ∀ {A B C} {f : B → C} {g : A → B} →
  ∀ xs → map f (map g xs) ≣ map (λ x → f (g x)) xs
map-fusion ∅ = refl
map-fusion (x , xs) = cong₂ _,_ refl (map-fusion xs)
