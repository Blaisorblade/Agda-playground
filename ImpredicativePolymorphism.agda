-- I had heard that Agda did not have impredicative polymorphism, but I had
-- never fully got what it meant, even though I had heard explanations multiple
-- times. So I decided to try it out.

module ImpredicativePolymorphism where

open import Relation.Binary.PropositionalEquality

-- Agda polymorphism is impredicative? No!

-- What we could write with impredicative polymorphism:

{-
id-type : Set
id-type = ∀ T → (t : T) → T

my-id : ∀ T → (t : T) → T
my-id T t = t

res = my-id id-type my-id

proof : res ≡ res
proof = refl
-}

open import Level

-- Actually working code:
id-type : ∀ ℓ → Set (suc ℓ)
id-type ℓ = ∀ (T : Set ℓ) → (t : T) → T

-- In System F:
-- (∀ T : * . T) : *
--
-- Here, both id-type zero and Set zero (a kind) have type Set (suc zero). Which
-- is very confusing, because it means that my-id zero lives at the same level
-- of types! That is, the usual understanding of levels as objects, types and
-- kinds breaks down here.

-- Note that the type-checker forces us to write Set₁ there, not Set (which is
-- an alias of Set₀). The typechecker is so good that one often does not need to
-- fully understand level errors - it's enough to know that sometimes you need
-- to have a bigger index :-).

-- Level-polymorphic id:
my-id : ∀ ℓ → id-type ℓ
my-id ℓ T t = t

-- in System F
--my-id zero : id-type zero : Set zero
-- here
--my-id zero : id-type zero : Set₁

v : Set₁
v = id-type zero

-- If you ignore the explicit levels, this looks like impredicative
-- polymorphism, right? Instead, it relies on level-polymorphism.
res = my-id (suc zero) (id-type zero) (my-id zero)

-- Can we apply my-id to the level-polymorphic my-id?
--
--res2 = my-id ? ? my-id
--
-- Apparently not: the above line gives this error.
{-
((ℓ : Level) (T : Set ℓ) → T → T) !=< ?1
because this would result in an invalid use of Setω
when checking that the expression my-id has type ?1
-}

-- To understand why the above happens, let us verify that id-type does not have
-- a type itself.
{-
type-of-id-type : ?
type-of-id-type = ∀ ℓ → Set (suc ℓ)
-}
-- Error:
{-
Setω is not a valid type
when checking that the expression (ℓ : _) → Set (suc ℓ) has type ?0
-}

-- This verifies that simple-ml-id is trivially an identity function.

proof : res ≡ (my-id zero)
proof = refl

-- Simpler id, probably typable with ML polymorphism: 
simple-ml-id : ∀ (T : Set) → (t : T) → T
simple-ml-id T t = t

-- Does not typecheck - it would in Haskell, because Haskell is impredicative!
-- res2 = simple-ml-id _ simple-ml-id

-- This verifies that simple-ml-id is trivially an identity function.
proof-id : ∀ t v → simple-ml-id t v ≡ v
proof-id t v = refl
