--
-- Reimplementation of "Type-Safe Diff for Families of Datatypes"
--
module TreeDiff where

open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊓_)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- Monadic combinators, specialized to Maybe.
-- _<=<_ appears in the paper in Sec. 3 (named _⋄_). _>>=_ is inlined there, but I took it out-of-line
-- because with-clauses are handled badly during equational reasoning.

infixr 5 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
(just y) >>= g = g y
nothing >>= _  = nothing

infixl 5 _<=<_
_<=<_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
_<=<_ {A} {B} {C} g f x = f x >>= g

-- Sec. 3
module ForLists (Item : Set) (_≟_ : Decidable {A = Item} _≡_) where
  _==_ : Item → Item → Bool
  x == y = ⌊ x ≟ y ⌋

  ==refl : ∀ x → x == x ≡ true
  ==refl x with x ≟ x
  ==refl x | yes refl = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  data Diff : Set where
    ins : Item → Diff → Diff
    del : Item → Diff → Diff
    cpy : Item → Diff → Diff
    end : Diff

  insert : Item → List Item → Maybe (List Item)
  insert x ys = just (x ∷ ys)

  delete : Item → List Item → Maybe (List Item)
  delete x [] = nothing
  delete x (y ∷ ys) =
    if x == y then
      just ys
    else
      nothing

  patch : Diff → List Item → Maybe (List Item)
  patch (ins x d) ys = (insert x <=< patch d             ) ys
  patch (del x d) ys = (             patch d <=< delete x) ys
  patch (cpy x d) ys = (insert x <=< patch d <=< delete x) ys
  patch end [] = just []
  patch end (x ∷ ys) = nothing

  cost : Diff → ℕ
  cost (ins _ d) = 1 + cost d
  cost (del _ d) = 1 + cost d
  cost (cpy _ d) = 1 + cost d
  cost end       = 0

  _⊓_ : Diff → Diff → Diff
  dx ⊓ dy =
    if ⌊ cost dx ≤? cost dy ⌋ then
      dx
    else
      dy

  diff : List Item → List Item → Diff
  diff [] [] = end
  diff [] (y ∷ ys) = ins y (diff [] ys)
  diff (x ∷ xs) [] = del x (diff xs [])
  diff (x ∷ xs) (y ∷ ys) =
    if x == y then
      cpy x (diff xs ys)
    else
      del x (diff xs (y ∷ ys)) ⊓ ins y (diff (x ∷ xs) ys)

  open ≡-Reasoning

  lem-delete-first : ∀ x xs → delete x (x ∷ xs) ≡ just xs
  lem-delete-first x xs =
    begin
      (if ⌊ x ≟ x ⌋ then just xs else nothing)
    ≡⟨ cong (λ □ → if □ then just xs else nothing) (==refl x) ⟩
      (if true then just xs else nothing)
    ≡⟨⟩
      just xs
    ∎

  -- Prove a property of a conditional by proving it for both branches
  p-if : ∀ {T : Set} test (P : T → Set) t e → P t → P e → P (if test then t else e)
  p-if true  _ _ _ Pt Pe = Pt
  p-if false _ _ _ Pt Pe = Pe

  patch-diff-spec : ∀ xs ys → patch (diff xs ys) xs ≡ just ys

  patch-diff-spec-lem-del : ∀ x xs ys → patch (del x (diff xs ys)) (x ∷ xs) ≡ just ys
  patch-diff-spec-lem-ins : ∀ y xs ys → patch (ins y (diff xs ys)) xs ≡ just (y ∷ ys)
  patch-diff-spec-lem-cong-insert : ∀ x xs ys → patch (diff xs ys) xs >>= insert x ≡ just (x ∷ ys)

  patch-diff-spec-lem-cong-insert x xs ys =
    begin
      patch (diff xs ys) xs >>= insert x
    ≡⟨ cong (λ □ → □ >>= insert x) (patch-diff-spec xs ys) ⟩
      insert x ys
    ≡⟨⟩
      just (x ∷ ys)
    ∎

  patch-diff-spec-lem-del x xs ys =
    begin
      patch (del x (diff xs ys)) (x ∷ xs)
    ≡⟨⟩
      delete x (x ∷ xs) >>= patch (diff xs ys)
    ≡⟨ cong (λ □ → □ >>= patch (diff xs ys))  (lem-delete-first x xs) ⟩
      just xs >>= patch (diff xs ys)
    ≡⟨⟩
      patch (diff xs ys) xs
    ≡⟨ patch-diff-spec xs ys ⟩
      just ys
    ∎

  patch-diff-spec-lem-ins y xs ys =
    begin
      patch (ins y (diff xs ys)) xs
    ≡⟨⟩
      patch (diff xs ys) xs >>= insert y
    ≡⟨ patch-diff-spec-lem-cong-insert y xs ys ⟩
      just (y ∷ ys)
    ∎

  patch-diff-spec [] [] = refl
  patch-diff-spec [] (y ∷ ys) =
    begin
      patch (diff [] (y ∷ ys)) []
    ≡⟨⟩
      patch (ins y (diff [] ys)) []
    ≡⟨ patch-diff-spec-lem-ins y [] ys ⟩
      just (y ∷ ys)
    ∎
  patch-diff-spec (x ∷ xs) [] =
    begin
      patch (diff (x ∷ xs) []) (x ∷ xs)
    ≡⟨⟩
      patch (del x (diff xs [])) (x ∷ xs)
    ≡⟨ patch-diff-spec-lem-del x xs [] ⟩
      just []
    ∎
  -- Most complex clause.
  patch-diff-spec (x ∷ xs) (y ∷ ys) with x ≟ y
  patch-diff-spec (x ∷ xs) (.x ∷ ys) | yes refl =
    begin
      (insert x <=< patch (diff xs ys) <=< delete x) (x ∷ xs)
    ≡⟨⟩
      (if ⌊ x ≟ x ⌋ then just xs else nothing) >>=
      (λ x₁ → patch (diff xs ys) x₁ >>= (λ ys₁ → just (x ∷ ys₁)))
    ≡⟨ cong
        (λ □ →
          (if □ then just xs else nothing) >>=
          (λ x₁ → patch (diff xs ys) x₁ >>= (λ ys₁ → just (x ∷ ys₁))))
        (==refl x)
     ⟩
      (if true then just xs else nothing) >>=
      (λ x₁ → patch (diff xs ys) x₁ >>= (λ ys₁ → just (x ∷ ys₁)))
    ≡⟨⟩
      patch (diff xs ys) xs >>= insert x
    ≡⟨ patch-diff-spec-lem-cong-insert x xs ys ⟩
      just (x ∷ ys)
    ∎

  patch-diff-spec (x ∷ xs) (y ∷ ys) | no ¬p =
    p-if
      (⌊ suc (cost (diff xs (y ∷ ys))) ≤? suc (cost (diff (x ∷ xs) ys)) ⌋)
      (λ d → patch d (x ∷ xs) ≡ just (y ∷ ys))
      (del x (diff xs (y ∷ ys)))
      (ins y (diff (x ∷ xs) ys))
      (patch-diff-spec-lem-del x xs (y ∷ ys)) (patch-diff-spec-lem-ins y (x ∷ xs) ys)

module ForTrees (Label : Set) (a b c : Label)
  where
  data Tree : Set where
    node : Label → List Tree → Tree

  data Diff : Set where
    ins : Label × ℕ → Diff → Diff
    del : Label × ℕ → Diff → Diff
    cpy : Label × ℕ → Diff → Diff
    end : Diff

  ex1 = node a (node b [] ∷ node c [] ∷ node c [] ∷ [])

  patch : Diff → List Tree → Maybe (List Tree)
  patch = {!!}

  diff : List Tree → List Tree → Diff
  diff = {!!}

  patch-diff-spec : ∀ xs ys → patch (diff xs ys) xs ≡ just ys
  patch-diff-spec = {!!}
