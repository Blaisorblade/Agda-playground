module DeltaGroupoid where

open import Relation.Binary.PropositionalEquality

record Delta (t : Set) (a : t) (b : t) : Set where
  constructor pp

Change : ∀ {t} a b → Delta t a b
Change a b = _

id : ∀ {t a} → Delta t a a
id = _

inv : ∀ {t a b} → Delta t a b → Delta t b a
inv _ = _

append : ∀ {t a b c} → Delta t a b → Delta t b c → Delta t a c
append _ _ = _

assoc-append : ∀ {t a b c d} → (x : Delta t a b) → (y : Delta t b c) → (z : Delta t c d) → append (append x y) z ≡ append x (append y z)
assoc-append {t} {a} {b} {c} {d} _ _ _ = refl

append-idL : ∀ {t a b} → (x : Delta t a b) → append id x ≡ x
append-idL {t} {a} {b} _ = refl

append-idR : ∀ {t a b} → (x : Delta t a b) → append x id ≡ x
append-idR _ = refl

left-inv : ∀ {t a b} → (x : Delta t a b) → append x (inv x) ≡ id
left-inv {t} {a} {b} _ = refl
right-inv : ∀ {t a b} → (x : Delta t a b) → append (inv x) x ≡ id
right-inv {t} {a} {b} _ = refl

reassemble : ∀ {t} → (a : t) → {b : t} → Delta t a b → t
reassemble a {b} _ = b

_⊹_ = reassemble
_●_ = append
infixl 6 _⊹_
infixl 6 _●_

-- What's there to prove after all? Well, there is still something.

reassemble-id : ∀ {t} {a : t} → reassemble a id ≡ a
reassemble-id = refl

-- Check that this is indeed right associativity. It seems too obvious.
reassemble-right-assoc : ∀ {t} → {a b c : t} → {d1 : Delta t a b} → {d2 : Delta t b c} → (a ⊹ d1) ⊹ d2 ≡ a ⊹ (d1 ● d2)
reassemble-right-assoc {t} {a} {b} {c} {d1} {d2} = refl

{-
The idea, below, was to show that the proved theorems are sufficient.
In fact, here it's too easy to prove anything - Agda's auto is enough
to generate the needed proof term, namely refl.
We'd need to do the proofs using only the interface. But that's for later.
-}

example-corollary : ∀ {t} → (a b : t) → (d : Delta t a b) → a ⊹ d ⊹ inv d ≡ a
example-corollary {t} a b d = refl

example-corollary2 : ∀ {t} {a b c d e : t} → {d1 : Delta t a b} → {d2 : Delta t b c} → {d3 : Delta t c d} → {d4 : Delta t d e} →
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
