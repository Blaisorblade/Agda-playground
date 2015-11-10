module week2 where

open import Data.Nat
open import Data.Vec hiding ([_]; take; drop; split; concat)
  renaming (_++_ to _+++_)
open import Data.List hiding ([_]; take; drop; concat)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

data SnocView {A : Set} : List A → Set where
  ⟨⟩ : SnocView []
  _snoc_ : (xs : List A) → (x : A) → SnocView (xs ++ (x ∷ []))

view : ∀ {A} → (xs : List A) → SnocView xs
view [] = ⟨⟩
view (x ∷ xs) with view xs
view (x ∷ _) | ⟨⟩ = [] snoc x
view (x₁ ∷ _) | xs snoc x = (x₁ ∷ xs) snoc x
{-
view (x ∷ .[]) | ⟨⟩ = [] snoc x
view (x ∷ .(ys ++ y ∷ [])) | ys snoc y = (x ∷ ys) snoc y
-}

list₁ : List ℕ
list₁ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

snocList₁ : SnocView list₁
snocList₁ = view list₁

rotateRight : ∀ {A} → List A → List A
rotateRight xs with view xs
rotateRight .[] | ⟨⟩ = []
rotateRight .(xs ++ x ∷ []) | xs snoc x = x ∷ xs

rotatedList₁ : List ℕ
rotatedList₁ = rotateRight (rotateRight list₁)

check : rotatedList₁ ≡ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []
check = refl

-- Example 2

take : ∀ {m} {A : Set} → (n : ℕ) → Vec A (n + m) → Vec A n
take zero xs = []
take (suc n) (x ∷ xs) = x ∷ (take n xs)

drop : ∀ {m} {A : Set} → (n : ℕ) → Vec A (n + m) → Vec A m
drop zero xs = xs
drop (suc n) (x ∷ xs) = drop n xs

takeDropLemma : ∀ {A m} n → (xs : Vec A (n + m)) → (take n xs) +++ (drop n xs) ≡ xs
takeDropLemma zero xs = refl
takeDropLemma (suc n) (x ∷ xs) = cong (λ ys → x ∷ ys) (takeDropLemma n xs)

split : ∀ {A} → (m n : ℕ) → Vec A (m * n) → Vec (Vec A n) m
split zero n [] = []
split (suc m) n xs = (take n xs) ∷ (split m n (drop n xs))

concat : {A : Set} → ∀ {m n} → Vec (Vec A n) m → Vec A (m * n)
concat [] = []
concat (xs ∷ xs₁) = xs +++ concat xs₁

splitConcatLemma : ∀ {A} m n → (xs : Vec A (m * n)) → concat (split m n xs) ≡ xs
splitConcatLemma zero n [] = refl
splitConcatLemma (suc m) n xs =
  begin
    concat (split (suc m) n xs)
  ≡⟨⟩
    take n xs +++ concat (split m n (drop n xs))
  ≡⟨ cong (λ ys → take n xs +++ ys) (splitConcatLemma m n (drop n xs)) ⟩
    take n xs +++ drop n xs
  ≡⟨ takeDropLemma n xs ⟩
    xs
  ∎

data SplitView {A : Set} : (n : ℕ) → (m : ℕ) → Vec A (m * n) → Set where
  [_] : ∀ {m n} → (xss : Vec (Vec A n) m) → SplitView n m (concat xss)

splitView : ∀ {A} → (m n : ℕ) → (xs : Vec A (m * n)) → SplitView n m xs
splitView m n xss with split m n xss | splitConcatLemma m n xss
splitView m n .(concat v) | v | refl = [ v ]

data Bit : Set where
  O : Bit
  I : Bit

Word : ℕ → Set
Word n = Vec Bit n

swab : ∀ {n} → Word (4 * n) → Word (4 * n)
swab {n} xs with splitView 4 n xs
swab _ | [ a ∷ b ∷ c ∷ d ∷ [] ] = concat (b ∷ a ∷ d ∷ c ∷ [])

testWord : Word 16
testWord = O ∷ O ∷ O ∷ I ∷ O ∷ O ∷ I ∷ O ∷ I ∷ O ∷ O ∷ O ∷ O ∷ I ∷ O ∷ O ∷ []

swabWord : Word 16
swabWord = swab {4} testWord
