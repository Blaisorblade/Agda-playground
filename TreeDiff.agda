--
-- Reimplementation of "Type-Safe Diff for Families of Datatypes"
--
-- I added proofs of patch-diff-spec written on my own; however, the one for
-- Sec. 4 currently fails termination checking, because the relevant termination
-- measure is far from obvious to Agda.

module TreeDiff where

open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊓_) renaming (_≟_ to _≟ℕ_)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open ≡-Reasoning

-- Monadic combinators, specialized to Maybe.
-- _<=<_ appears in the paper in Sec. 3 (named _⋄_). _>>=_ is inlined there, but I took it out-of-line
-- because with-clauses are handled badly during equational reasoning.

infixl 5 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
(just y) >>= g = g y
nothing >>= _  = nothing

infixr 5 _<=<_
_<=<_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
_<=<_ {A} {B} {C} g f x = f x >>= g

-- Development in Sec. 3, adapted so that changes are indexed by source and
-- destination. The main advantage is that this allows operations to not be
-- partial, and makes everything closer to what makes sense in ILC.
--
-- This simplifies the proof. However, patch-diff-spec is especially shortened
-- by doing the proof in a more concise way.
module IlcListDIff (Item : Set) (_≟_ : Decidable {A = Item} _≡_) where
  _==_ : Item → Item → Bool
  x == y = ⌊ x ≟ y ⌋

  data Diff : List Item → List Item → Set where
    ins : ∀ xs ys → (y : Item) → Diff xs ys → Diff xs (y ∷ ys)
    del : ∀ xs ys → (x : Item) → Diff xs ys → Diff (x ∷ xs) ys
    cpy : ∀ xs ys → (x : Item) → Diff xs ys → Diff (x ∷ xs) (x ∷ ys)
    end : Diff [] []

  -- In Diff and here, too many arguments are explicit, so that the generated pattern matches show what is going on.
  patch : ∀ xs ys → Diff xs ys → List Item
  patch xs .(y ∷ ys) (ins .xs ys y d) = y ∷ patch xs ys d

  -- In these two cases, we don't call delete and compare x with itself; the
  -- types ensure that we're trying to delete the actual head of the list, here
  -- pattern matching shows that.
  --
  -- So instead of writing delete x xs, we can write delete x (x ∷ xs) and
  -- simplify that immediately to xs :-). In the proof, this avoids needing the
  -- ==refl and lem-delete-first lemmas (unlike in module ForLists below, which
  -- doesn't use indexed changes).
  patch .(x ∷ xs) ys (del xs .ys x d) = patch xs ys d
  patch .(x ∷ xs) .(x ∷ ys) (cpy xs ys x d) = x ∷ patch xs ys d
  patch .[] .[] end = []

  -- *Very* simple cost function
  cost : ∀ {xs ys} → Diff xs ys → ℕ
  cost (ins xs ys y d) = 1 + cost d
  cost (del xs ys x d) = 1 + cost d
  cost (cpy xs ys x d) = 1 + cost d
  cost end = 0

  _⊓_ : ∀ {xs ys} → Diff xs ys → Diff xs ys → Diff xs ys
  dx ⊓ dy =
    if ⌊ cost dx ≤? cost dy ⌋ then
      dx
    else
      dy

  diff : ∀ xs ys → Diff xs ys
  diff [] [] = end
  diff [] (x ∷ ys) = ins [] ys x (diff [] ys)
  diff (x ∷ xs) [] = del xs [] x (diff xs [])
  diff (x ∷ xs) (y ∷ ys) with x ≟ y
  diff (x ∷ xs) (.x ∷ ys) | yes refl = cpy xs ys x (diff xs ys)
  diff (x ∷ xs) (y ∷ ys)  | no ¬p =
    (del xs (y ∷ ys) x (diff xs (y ∷ ys))) ⊓ (ins (x ∷ xs) ys y (diff (x ∷ xs) ys))

  patch-diff-spec : ∀ xs ys → patch xs ys (diff xs ys) ≡ ys
  patch-diff-spec [] [] = refl
  patch-diff-spec [] (y ∷ ys) rewrite patch-diff-spec [] ys = refl
  patch-diff-spec (x ∷ xs) [] rewrite patch-diff-spec xs [] = refl
  patch-diff-spec (x ∷ xs) (y ∷ ys) with x ≟ y
  patch-diff-spec (x ∷ xs) (.x ∷ ys) | yes refl rewrite patch-diff-spec xs ys = refl
  -- Pattern matching on this comparison result simplifies the proof a lot and avoids needing to use p-if.
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ with (cost (diff xs (y ∷ ys)) ≤? cost (diff (x ∷ xs) ys))
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ | yes _ rewrite patch-diff-spec xs       (y ∷ ys) = refl
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ | no _  rewrite patch-diff-spec (x ∷ xs) ys       = refl

-- Sec. 3
module ForLists (Item : Set) (_≟_ : Decidable {A = Item} _≡_) where
  _==_ : Item → Item → Bool
  x == y = ⌊ x ≟ y ⌋

  ==refl : ∀ x → x == x ≡ true
  ==refl x with x ≟ x
  ==refl x | yes refl = refl
  ... | no ¬x≡x = ⊥-elim (¬x≡x refl)

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
  patch (ins x d)          = insert x <=< patch d
  patch (del x d)          =              patch d <=< delete x
  patch (cpy x d)          = insert x <=< patch d <=< delete x
  patch end       []       = just []
  patch end       (x ∷ ys) = nothing

  -- *Very* simple cost function
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

  lem-delete-first : ∀ x xs → delete x (x ∷ xs) ≡ just xs
  lem-delete-first x xs rewrite ==refl x = refl

  patch-diff-spec : ∀ xs ys → patch (diff xs ys) xs ≡ just ys
  patch-diff-spec-lem-del : ∀ x xs ys → patch (del x (diff xs ys)) (x ∷ xs) ≡ just ys
  patch-diff-spec-lem-del x xs ys rewrite lem-delete-first x xs = patch-diff-spec xs ys

  patch-diff-spec [] [] = refl
  patch-diff-spec [] (y ∷ ys) rewrite patch-diff-spec [] ys = refl
  patch-diff-spec (x ∷ xs) [] rewrite patch-diff-spec-lem-del x xs [] = refl
  patch-diff-spec (x ∷ xs) (y ∷ ys) with x ≟ y
  patch-diff-spec (x ∷ xs) (.x ∷ ys) | yes refl rewrite patch-diff-spec-lem-del x xs ys = refl
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ with (cost (diff xs (y ∷ ys)) ≤? cost (diff (x ∷ xs) ys))
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ | yes _ rewrite patch-diff-spec-lem-del x xs       (y ∷ ys) = refl
  patch-diff-spec (x ∷ xs) (y ∷ ys)  | no _ | no  _ rewrite patch-diff-spec           (x ∷ xs) ys       = refl

-- Sec. 4
module ForTrees (Label : Set) (a b c : Label) (_≟ℓ_ : Decidable {A = Label} _≡_) where
  _==_ : (Label × ℕ) → (Label × ℕ) → Bool
  (x , xn) == (y , yn) = ⌊ x ≟ℓ y ⌋ ∧ ⌊ xn ≟ℕ yn ⌋

  ≟ℕ-refl : ∀ n → ⌊ n ≟ℕ n ⌋ ≡ true
  ≟ℕ-refl n with n ≟ℕ n
  ≟ℕ-refl n | yes p = refl
  ≟ℕ-refl n | no ¬p = ⊥-elim (¬p refl)

  ==refl : ∀ x xn → (x , xn) == (x , xn) ≡ true
  ==refl x xn with x ≟ℓ x
  ==refl x xn | no ¬x≟ℓx = ⊥-elim (¬x≟ℓx refl)
  ==refl x xn | yes refl with xn ≟ℕ xn
  ==refl x xn | yes refl | yes refl = refl
  ==refl x xn | yes refl | no ¬xn≟ℕxn = ⊥-elim (¬xn≟ℕxn refl)

  data Tree : Set where
    node : (x : Label) → (xs : List Tree) → Tree

  data Diff : Set where
    ins : Label × ℕ → Diff → Diff
    del : Label × ℕ → Diff → Diff
    cpy : Label × ℕ → Diff → Diff
    end : Diff

  -- *Very* simple cost function
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

  ex1 = node a (node b [] ∷ node c [] ∷ node c [] ∷ [])

  insert : Label × ℕ → List Tree → Maybe (List Tree)
  insert (x , n) yss with splitAt n yss
  ... | (ys , yss′) =
    if ⌊ length ys ≟ℕ n ⌋ then
      just ((node x ys) ∷ yss′)
    else
      nothing

  delete : Label × ℕ → List Tree → Maybe (List Tree)
  delete (x , n) [] = nothing
  delete (x , n) (node y ys ∷ yss) =
    if (x , n) == (y , length ys) then
      just (ys ++ yss)
    else
      nothing

  patch : Diff → List Tree → Maybe (List Tree)
  patch (ins x d)          = insert x <=< patch d
  patch (del x d)          =              patch d <=< delete x
  patch (cpy x d)          = insert x <=< patch d <=< delete x
  patch end       []       = just []
  patch end       (x ∷ ys) = nothing

  {-# NO_TERMINATION_CHECK #-}

  diff-rest : Label → List Tree → List Tree → Label → List Tree → List Tree → Diff
  diff : List Tree → List Tree → Diff
  diff [] [] = end
  diff [] (node y ys ∷ yss) = ins (y , length ys) (diff [] (ys ++ yss))
  diff (node x xs ∷ xss) [] = del (x , length xs) (diff (xs ++ xss) [])
  diff (node x xs ∷ xss) (node y ys ∷ yss) =
    if (x , length xs) == (y , length ys) then
      cpy (x , length xs) (diff (xs ++ xss) (ys ++ yss))
    else
      diff-rest x xs xss y ys yss

  diff-rest x xs xss y ys yss =
      (ins (y , length ys) (diff (node x xs ∷ xss) (ys ++ yss))) ⊓
      (del (x , length xs) (diff (xs ++ xss) (node y ys ∷ yss)))

  lem-delete-first : ∀ x xs xss → delete (x , length xs) (node x xs ∷ xss) ≡ just (xs ++ xss)
  lem-delete-first x xs xss rewrite ==refl x (length xs) = refl

  -- XXX belongs in Data.List.Properties
  splitAt-++ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → splitAt (length xs) (xs ++ ys) ≡ (xs , ys)
  splitAt-++ [] ys = refl
  splitAt-++ (x ∷ xs) ys rewrite splitAt-++ xs ys = refl

  lem-insert-first : ∀ y ys yss → insert (y , length ys) (ys ++ yss) ≡ just (node y ys ∷ yss)
  lem-insert-first y ys yss rewrite splitAt-++ ys yss | ≟ℕ-refl (length ys) = refl

  {-# NO_TERMINATION_CHECK #-}
  patch-diff-spec : ∀ xss yss → patch (diff xss yss) xss ≡ just yss
  patch-diff-spec-rest : ∀ x xs xss y ys yss → patch (diff-rest x xs xss y ys yss) (node x xs ∷ xss) ≡ just (node y ys ∷ yss)

  patch-diff-spec-lem-ins : ∀ xss y ys yss → patch (ins (y , length ys) (diff xss (ys ++ yss))) xss ≡ just (node y ys ∷ yss)
  patch-diff-spec-lem-ins xss y ys yss rewrite patch-diff-spec xss (ys ++ yss) | lem-insert-first y ys yss = refl

  patch-diff-spec-lem-del : ∀ x xs xss yss → patch (del (x , length xs) (diff (xs ++ xss) yss)) (node x xs ∷ xss) ≡ just yss
  patch-diff-spec-lem-del x xs xss yss rewrite lem-delete-first x xs xss | patch-diff-spec (xs ++ xss) yss = refl

  patch-diff-spec [] [] = refl
  patch-diff-spec [] (node x xs ∷ yss) = patch-diff-spec-lem-ins [] x xs yss
  patch-diff-spec (node x xs ∷ xss) [] = patch-diff-spec-lem-del x xs xss []
  patch-diff-spec (node x xs ∷ xss) (node y ys ∷ yss) with x ≟ℓ y | length xs ≟ℕ length ys
  patch-diff-spec (node x xs ∷ xss) (node .x ys ∷ yss) | yes refl | yes length-xs≟ℕlength-ys
    rewrite ==refl x (length xs) | length-xs≟ℕlength-ys =
      patch-diff-spec-lem-ins (xs ++ xss) x ys yss

  patch-diff-spec (node x xs ∷ xss) (node y ys ∷ yss) | yes _ | no _ = patch-diff-spec-rest x xs xss y ys yss
  patch-diff-spec (node x xs ∷ xss) (node y ys ∷ yss) | no _ | yes _ = patch-diff-spec-rest x xs xss y ys yss
  patch-diff-spec (node x xs ∷ xss) (node y ys ∷ yss) | no _ | no _ = patch-diff-spec-rest x xs xss y ys yss

  patch-diff-spec-rest x xs xss y ys yss with (cost (diff (node x xs ∷ xss) (ys ++ yss))) ≤? (cost (diff (xs ++ xss) (node y ys ∷ yss)))
  patch-diff-spec-rest x xs xss y ys yss | yes p = patch-diff-spec-lem-ins (node x xs ∷ xss) y ys yss
  patch-diff-spec-rest x xs xss y ys yss | no ¬p = patch-diff-spec-lem-del x xs xss (node y ys ∷ yss)
