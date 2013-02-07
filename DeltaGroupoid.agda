module DeltaGroupoid where

open import Relation.Binary.PropositionalEquality

-- Define datatype representing a change from a to b. In general, this is an arrow betwen the objects a and b.
record Delta {t : Set} (a : t) (b : t) : Set where
  constructor pp
-- In this case, the type is indexed by the concrete values a and b, which specify all needed information on the change.
-- Categorically, the objects are singletons sets or types. IOW, Delta t is the category having for objects singleton types a.type <: t,
-- and for arrows values of type Delta t a b. Each hom-set is a singleton as well.
-- One can also say that arrows between a and b are total functions between a.type and b.type; since there is only one such total function, this definition is isomorphic.
-- We can thus say that we are dealing with the category of singleton types (which is even cartesian closed, since hom-sets are singletons anyway; we probably need
-- to pick an isomorphism).

{-
Wikipedia gives the construction which I use to turn groups into groupoids (http://en.wikipedia.org/wiki/Groupoid):
Every connected groupoid (that is, one in which any two objects are connected by at least one morphism) is isomorphic to a groupoid of the following form. Pick a group G and a set (or class) X. Let the objects of the groupoid be the elements of X. For elements x and y of X, let the set of morphisms from x to y be G. Composition of morphisms is the group operation of G. If the groupoid is not connected, then it is isomorphic to a disjoint union of groupoids of the above type (possibly with different groups G for each connected component). Thus any groupoid may be given (up to isomorphism) by a set of ordered pairs (X,G).
-}

Change : ∀ {t} a b → Delta {t} a b
Change a b = _

id : ∀ {t a} → Delta {t} a a
id = _

inv : ∀ {t a b} → Delta {t} a b → Delta b a
inv _ = _

append : ∀ {t a b c} → Delta {t} a b → Delta b c → Delta a c
append _ _ = _

reassemble : ∀ {t} a {b} → Delta {t} a b → t
reassemble a {b} _ = b

_⊹_ = reassemble
_●_ = append
infixl 6 _⊹_
infixl 6 _●_

assoc-append : ∀ {t a b c d} → (x : Delta {t} a b) → (y : Delta b c) → (z : Delta c d) → (x ● y) ● z ≡ x ● (y ● z)
assoc-append {t} {a} {b} {c} {d} _ _ _ = refl

append-idL : ∀ {t a b} → (x : Delta {t} a b) → id ● x ≡ x
append-idL {t} {a} {b} _ = refl

append-idR : ∀ {t a b} → (x : Delta {t} a b) → x ● id ≡ x
append-idR _ = refl

left-inv : ∀ {t a b} → (x : Delta {t} a b) → x ● inv x ≡ id
left-inv {t} {a} {b} _ = refl

right-inv : ∀ {t a b} → (x : Delta {t} a b) → inv x ● x ≡ id
right-inv {t} {a} {b} _ = refl

-- What's there to prove after all? Well, there is still something.

reassemble-id : ∀ {t} {a : t} → a ⊹ id ≡ a
reassemble-id = refl

-- Check that this is indeed right associativity. It seems too obvious.
reassemble-right-assoc : ∀ {t a b c} → {d1 : Delta {t} a b} → {d2 : Delta b c} → (a ⊹ d1) ⊹ d2 ≡ a ⊹ (d1 ● d2)
reassemble-right-assoc {t} {a} {b} {c} {d1} {d2} = refl

{-
The idea, below, was to show that the proved theorems are sufficient.
In fact, here it's too easy to prove anything - Agda's auto is enough
to generate the needed proof term, namely refl.
We'd need to do the proofs using only the interface. But that's for later.
-}

example-corollary : ∀ {t a b} → (d : Delta {t} a b) → a ⊹ d ⊹ inv d ≡ a
example-corollary d = refl

example-corollary2 : ∀ {t a b c d e} → {d1 : Delta {t} a b} → {d2 : Delta b c} → {d3 : Delta c d} → {d4 : Delta d e} →
  a ⊹ d1 ⊹ d2 ⊹ d3 ⊹ d4 ≡ a ⊹ (d1 ● d2 ● d3 ● d4)
example-corollary2 = refl

{-
DeltaIsSemigroup : {t : Set} → ∀ {eq} → IsSemigroup _≡_ (append {t} {eq})
DeltaIsSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc = assoc-append
  ; ∙-cong = cong₂ append
  }

DeltaIsMonoid : {t : Set} → ∀ {eq} → IsMonoid _≡_ (append {t} {eq}) NoChange
DeltaIsMonoid {t} = record
  { isSemigroup = DeltaIsSemigroup
  ; identity = append-idL , append-idR
  }

-- Delta is in fact not a group. We can only provide inverses if we give up having a single identity and make this a category.
{-
DeltaIsGroup : (t : Set) → (eq : t → t → Bool) → Group zero zero
DeltaIsGroup t eq = record {
                   Carrier = Delta t eq;
                   _≈_ = _≡_;
                   _∙_ = append;
                   ε = NoChange;
                   _⁻¹ = inv;
                   isGroup = record { isMonoid = DeltaIsMonoid; inverse = {!!} , {!!}; ⁻¹-cong = cong inv } }
-}
-}
