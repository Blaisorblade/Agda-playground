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

-- Actually working code:
id-type : Set₁
id-type = ∀ T → (t : T) → T
-- Note that the type-checker forces us to write Set₁ there, not Set (which is
-- an alias of Set₀). The typechecker is so good that one often does not need to
-- fully understand level errors - it's enough to know that sometimes you need
-- to have a bigger index :-).

-- Level-polymorphic id:
my-id : ∀ {l} (T : Set l) → (t : T) → T
my-id T t = t
-- Note that id-type is an *instance* of the above type.

-- It looks like this is impredicative polymorphism, right? Instead, this relies
-- on level-polymorphism.
res = my-id id-type my-id

-- This verifies that simple-ml-id is trivially an identity function.

proof : res ≡ res
proof = refl

-- Simpler id, probably typable with ML polymorphism: 
simple-ml-id : ∀ (T : Set) → (t : T) → T
simple-ml-id T t = t

-- Does not compile
-- res2 = simple-ml-id _ simple-ml-id

-- This verifies that simple-ml-id is trivially an identity function.
proof-id : ∀ t v → simple-ml-id t v ≡ v
proof-id t v = refl
