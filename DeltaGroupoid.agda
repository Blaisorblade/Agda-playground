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

{- reassemble could be considered a derived operation, given an embed method which turns a value into a delta producing
that value. In this framework, we'd need to specify a source, as well.
Then a ⊹ b would correspond to the destination of (embed a src) ● b; we can try to derive the laws about reassemble from the laws it would satisfy in that case.
-}
reassemble : ∀ {t} a {b} → Delta {t} a b → t
reassemble a {b} _ = b

_⊹_ = reassemble
_●_ = append
_⁻¹ = inv
infixl 6 _⊹_
infixl 6 _●_

assoc-append : ∀ {t a b c d} → (x : Delta {t} a b) → (y : Delta b c) → (z : Delta c d) → (x ● y) ● z ≡ x ● (y ● z)
assoc-append {t} {a} {b} {c} {d} _ _ _ = refl

append-idL : ∀ {t a b} → (x : Delta {t} a b) → id ● x ≡ x
append-idL {t} {a} {b} _ = refl

append-idR : ∀ {t a b} → (x : Delta {t} a b) → x ● id ≡ x
append-idR _ = refl

left-inv : ∀ {t a b} → (x : Delta {t} a b) → x ⁻¹ ● x ≡ id
left-inv {t} {a} {b} _ = refl

right-inv : ∀ {t a b} → (x : Delta {t} a b) → x ● x ⁻¹ ≡ id
right-inv {t} {a} {b} _ = refl

-- What's there to prove after all? Well, there is still something.

reassemble-id : ∀ {t} {a : t} → a ⊹ id ≡ a
reassemble-id = refl

reassemble-can-append-deltas-before : ∀ {t a b c} → {d1 : Delta {t} a b} → {d2 : Delta b c} → (a ⊹ d1) ⊹ d2 ≡ a ⊹ (d1 ● d2)
reassemble-can-append-deltas-before {t} {a} {b} {c} {d1} {d2} = refl
-- Check that this is indeed right associativity. It seems too obvious.
{-

Left-commutativity, in Grust's PhD thesis, page 24 (so-called 14):
  y : (x : xs) = x : (y : xs).
This would suggest there is no such thing as right associativity. Or rather, the term exists, but it only refers to how operators are parenthesized.
If we'd define `reassemble a delta` as `deembed (embed a ● delta)`, with embed (deembed a) = a, however, the above statement would become
  embed a ● d1 ● d2 ≡ embed a ● (d1 ● d2)
reassemble-id would become:
  embed a ● id = embed a
(that's weaker though, unless we stipulate that embed is injective and thus left-invertible).
The difference is that ● has inverses, so we'd also be able to deduce that:
  embed a ● inv (embed a) = inv (embed a) ● embed a = id
But reassemble doesn't even allow expresing inv (embed a), much less proving the above theorem.
Moreover, embed doesn't work so well for groupoids as it does for groups. The type of embed, in a groupoid, should be
  embed :: (a : t) → Delta t zero a
where zero : t is the identity for addition. This calls for making collections (or extensions of collections) groups themselves.

OTOH, the original reason for wanting inverses was to be able to
subtract values, not deltas. If I embed values as deltas, inverses of
deltas allow constructing inverses of values.

So, we get that for each interesting type T we might still want a groupoid of deltas, but for a collection of Ts we want
to build not only a group of deltas, but an embedding of values into this group, together with the required zero
element. Having such a group of deltas and embedding, one should be able to form a group of base values. The only
problem is proving closure: operations on embedded elements do not necessarily produce embedded ones. I think we need to
provide deembed and state that `deembed (embed a) = a` (we need the other inverse property above). `deembed a` would
just be `reassemble zero a`, operationally, and viceversa, as stated above, `reassemble a delta = deembed (embed a ●
delta)`; this would be an identity (either an axiom or a theorem), not an implementation.

The above is formally correct, except that we can't usually deembed deltas to collections. Deembed needs to target some larger set. Moreover, the point of
deembed is just to go back to the group of deltas, isn't it? Man, how confused am I...
-}

{-
The idea, below, was to show that the proved theorems are sufficient.
In fact, here it's too easy to prove anything - Agda's auto is enough
to generate the needed proof term, namely refl.
We'd need to do the proofs using only the interface. But that's for later.
-}

example-corollary : ∀ {t a b} → (d : Delta {t} a b) → a ⊹ d ⊹ d ⁻¹ ≡ a
example-corollary d = refl

example-corollary2 : ∀ {t a b c d e} → {d1 : Delta {t} a b} → {d2 : Delta b c} → {d3 : Delta c d} → {d4 : Delta d e} →
  a ⊹ d1 ⊹ d2 ⊹ d3 ⊹ d4 ≡ a ⊹ (d1 ● d2 ● d3 ● d4)
example-corollary2 = refl

open import Relation.Binary
open import Level

record IsGroupoid {α β l : Level} (A : Set α) (Arr : (A -> A -> Set β))
  (eq : {a b : A} → Rel (Arr a b) l) (op : {a b c : A} → (Arr a b) → (Arr b c) → (Arr a c)) : Set (α ⊔ β ⊔ l) where

  infixl 7 _◎_
  infix 4 _≈_

  _◎_ : {a b c : A} → (Arr a b) → (Arr b c) → (Arr a c)
  _◎_ = op
  _≈_ : {a b : A} → Rel (Arr a b) l
  _≈_ = eq

  field
    isEquivalence-eq : {a b : A} → IsEquivalence {A = Arr a b} _≈_

    assoc-op : {a b c d : A} → (x : Arr a b) → (y : Arr b c) → (z : Arr c d) → ((x ◎ y) ◎ z) ≈ (x ◎ (y ◎ z))

    id-op : {a : A} → Arr a a

    op-id-left : ∀ {a b} → (x : Arr a b) → (id-op ◎ x) ≈ x
    op-id-right : ∀ {a b} → (x : Arr a b) → (x ◎ id-op) ≈ x

    inv-op : {a b : A} → Arr a b → Arr b a
    inv-op-left  : ∀ {a b} → (arr : Arr a b) → ((inv-op arr) ◎ arr) ≈ id-op
    inv-op-right : ∀ {a b} → (arr : Arr a b) → (arr ◎ (inv-op arr)) ≈ id-op

DeltaIsGroupoid : {t : Set} → IsGroupoid t (Delta {t}) _≡_ append
DeltaIsGroupoid {t} = record {
                        isEquivalence-eq = isEquivalence;
                        assoc-op = assoc-append;
                        id-op = id;
                        op-id-left = append-idL;
                        op-id-right = append-idL;
                        inv-op = inv;
                        inv-op-left = left-inv;
                        inv-op-right = right-inv }

open ≡-Reasoning

example-corollary-3-gen : {A : Set} → {Arr : A → A → Set} → {_⊗_ : ∀ {a b c} → Arr a b → Arr b c → Arr a c} → IsGroupoid A Arr _≡_ _⊗_ →
  {t1 t2 t3 t4 : A} → {a : Arr t1 t2} → {b : Arr t2 t3} → {c : Arr t3 t4} → (a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)
example-corollary-3-gen isGroup = IsGroupoid.assoc-op isGroup _ _ _

example-corollary-4-operand-associativity : {A : Set} → {Arr : A → A → Set} → (_⊗_ : ∀ {a b c} → Arr a b → Arr b c → Arr a c) → IsGroupoid A Arr _≡_ _⊗_ →
  {t1 t2 t3 t4 t5 : A} → (a : Arr t1 t2) → (b : Arr t2 t3) → (c : Arr t3 t4) → (d : Arr t4 t5) → ((a ⊗ b) ⊗ c) ⊗ d ≡ a ⊗ (b ⊗ (c ⊗ d))
example-corollary-4-operand-associativity _⊗_ isGroup a b c d =
  begin
    ((a ⊗ b) ⊗ c) ⊗ d
  ≡⟨ IsGroupoid.assoc-op isGroup _ _ _ ⟩
    (a ⊗ b) ⊗ (c ⊗ d)
  ≡⟨ IsGroupoid.assoc-op isGroup _ _ _ ⟩
    a ⊗ (b ⊗ (c ⊗ d))
  ∎

  -- This could also be written as:
  --trans (IsGroupoid.assoc-op isGroup _ _ _) (IsGroupoid.assoc-op isGroup _ _ _)
  -- But the above seems clearer.

-- New theorems, mostly concerning Change.

Change-correct : ∀ {t} (a b : t) → a ⊹ Change a b ≡ b
Change-correct a b = refl

append-Change : ∀ {t} (s₁ s₂ s₃ : t) (ds : Delta s₂ s₃) → (Change s₁ s₂) ● ds ≡ Change s₁ (s₂ ⊹ ds)
append-Change s₁ s₂ s₃ ds = refl

-- (s₂ ⊝ (ds ⊕ s₁)) ∘ ds &= t₂ ⊝ t₁ (?)
Change-append-reassemble : ∀ {t} (s₁ s₂ s₃ : t) (ds : Delta s₁ s₃) → ds ● Change (s₁ ⊹ ds) s₂ ≡ Change s₁ s₂
Change-append-reassemble s₁ s₂ s₃ d = refl

-- diff-apply. This doesn't work for non-valid changes, which don't exist here.
Change-reassemble : ∀ {t} (s s′ : t) (ds : Delta s s′) → Change s (s ⊹ ds) ≡ ds
Change-reassemble s s′ ds = refl
-- Change-reassemble s s′ ds = {! refl } -- Auto doesn't work here; C-c C-SPACE
-- produces unsolved metavariables, but reloading solves them.

-- We can take these two as an axiom for our theory, since it holds in this model:
Change-a-a-is-nil : ∀ {t} {a : t} → Change a a ≡ id
Change-a-a-is-nil = refl

append-Change-Change : ∀ {t} (s₁ s₂ s₃ : t) → Change s₁ s₃ ≡ Change s₁ s₂ ● Change s₂ s₃
append-Change-Change s₁ s₂ s₃ = refl

-- or we can try proving them from other axioms. However, since the definition is not abstract, we can't restrict ourselves to the axioms so easily.

append-Change-Change-2 : ∀ {t} (s₁ s₂ s₃ : t) → Change s₁ s₂ ● Change s₂ s₃ ≡ Change s₁ s₃
append-Change-Change-2 s₁ s₂ s₃ =
  begin
    Change s₁ s₂ ● Change s₂ s₃
  ≡⟨ append-Change s₁ s₂ s₃ (Change s₂ s₃) ⟩
    Change s₁ (s₂ ⊹ (Change s₂ s₃))
-- This does not go through, even though it should be correct:
--
--  ≡⟨ cong (λ b → Change s₁ b) (Change-correct s₂ s₃) ⟩
--
  ≡⟨ cong (λ b → Change s₁ s₃) (Change-correct s₂ s₃) ⟩
    Change s₁ s₃
  ∎
  where
    open ≡-Reasoning
