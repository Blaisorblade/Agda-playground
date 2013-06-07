module ListExamples where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Level

-- Declare a heterogeneous, typed list.
-- We use Γ for lists of types. Set is Agda's name for Type.

data MyList : List Set → Set₁ where
  nil : MyList []
  -- Braces enclose implicit arguments. They can be placed anywhere.
  -- This would be useful also in Scala
  -- (http://blaisorbladeprog.blogspot.de/2013/01/flexible-implicits-from-agda-for-scala.html)
  -- ∀ is used before a list of parameters to omit their type, which
  -- will be deduced by type inference.
  cons : ∀ {τ Γ} → (v : τ) → (vs : MyList Γ) → MyList (τ ∷ Γ)

-- An inductive definition of a proof that a list of types contains another list of types.
data _contains_ : List Set → List Set → Set₁ where
  empty : [] contains []
  dropFirst : ∀ {Γ₁ Γ₂ τ} → (contain : Γ₁ contains Γ₂) → (τ ∷ Γ₁) contains Γ₂
  keepFirst : ∀ {Γ₁ Γ₂ τ} → (contain : Γ₁ contains Γ₂) → (τ ∷ Γ₁) contains (τ ∷ Γ₂)

-- Type signature. Note that the only explicit parameters are the list
-- of values and a proof of containment.

filterTypes : ∀ {Γ Γ′} → MyList Γ → Γ contains Γ′ → MyList Γ′

-- Definition by cases - this is executed using pattern matching. Note
-- that in Agda function definitions must be total; the typechecker
-- will verify that the cases given cover all possible input values.
-- However, these are not all possible combinations of values: many
-- are simply ruled out because they wouldn't typecheck. For instance,
-- if the proof of containment is empty, all arguments lists must be
-- empty lists as well.

filterTypes nil         empty               = nil
filterTypes (cons v vs) (dropFirst contain) = filterTypes vs contain
filterTypes (cons v vs) (keepFirst contain) = cons v (filterTypes vs contain)

-- If you want to see better what's going on, here's a version without
-- implicit parameters. Here you can see more easily the effets of
-- type refinement.

filterTypes2 : ∀ Γ Γ′ → MyList Γ → Γ contains Γ′ → MyList Γ′

filterTypes2 .[]      .[]       nil         empty                = nil
filterTypes2 (t ∷ ts) Γ′        (cons v vs) (dropFirst contains) = filterTypes2 ts Γ′ vs contains

-- Here, since the proof has value `keepFirst contains`, type
-- refinement tells Agda that the first elements of Γ and Γ′ must
-- match. Hence, we must reuse the same variable (t) for both; we must
-- use a dot as a prefix for one occurrence, so the second is .t

filterTypes2 (t ∷ ts) (.t ∷ Γ₂) (cons v vs) (keepFirst contains) = cons v (filterTypes2 ts Γ₂ vs contains)
