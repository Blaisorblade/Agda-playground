module AgdaBasics where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

_*_ : Nat → Nat → Nat
zero  * n = zero
suc m * n = n + (m * n)

_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

data _==_ {A : Set}(x : A) : A -> Set where
      refl : x == x

lem-plus-zero : (n : Nat) → n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
... | .n | refl = refl

--open import Data.List
infixr 40 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

--data _⋆ (α : Set): Set where
id : {A : Set} -> A -> A
id x = x

true' : Bool
true' = id true

zero' = id zero

apply : {A : Set}{B : A → Set} → ((x : A) → B x) → (a : A) -> B a
apply f a = f a

--_○_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
--      (f: {x : A}{y: B x

--_○_ : {A : Set} {B : A -> Set} {C : (x : A) -> B x -> Set} →
--       (∀ {x} → (y : B x) → C x y) -> (g : (x : A) -> B x) -> (∀ x -> C x (g x))
--(f ○ g) x = f (g x)

_○_ : {A B C : Set} → (f : B -> C) -> (g : A -> B) -> A -> C
(f ○ g) x = f (g x)

plus-two = suc ○ suc

foo : (A : Set) -> Set
foo A = A -> A
--foo = λ (A : Set) z → id z
--foo = id ○ ( λ (x : Set) -> id {x} )

--data Foo : Set₁ where
--  a = Set₀
--  b = Set

--a : Set₁
--a = Set₀
open import Data.Fin

magic : {A : Set} → Fin 0 → A
magic ()

foo₁ : Fin 5
foo₁ = zero

foo₂ : Fin 1
foo₂ = zero

open import Data.Nat
foo₃ : Fin 2
foo₃ = fromℕ≤ {toℕ foo₂} (s≤s z≤n)

foo₄ : Fin 2
foo₄ = # (toℕ foo₂)

open import Relation.Nullary.Decidable

##_ : ∀ {n n₂} → (m : Fin n) {m<n : True (suc (toℕ m) ≤? n₂)} → Fin n₂
##_ m {m<n} = #_ (toℕ m) { m<n = m<n }

open import Data.Unit
foo₅ : Fin 5
foo₅ = ##_ foo₄ {m<n = tt}

--Luckily, won't compile.
--foowrong : Fin 1
--foowrong = ##_ (suc (suc foo₂)) {m<n = {!!}}

foog : Fin 1
foog = ##_ foo₂ {m<n = tt}

data _≤M_ : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → zero ≤M n
  leq-succ : {m n : ℕ} → m ≤M n → suc m ≤M suc n

-- Alternative definition of less-than, inspired by removing pieces
-- from classical set containment. In fact, set containment could also
-- be simplified along the above lines.

data _≤M2_ : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → zero ≤M2 zero
  leq-inc : {m n : ℕ} → m ≤M2 n → m ≤M2 suc n
  leq-cong : {m n : ℕ} → m ≤M2 n → suc m ≤M2 suc n

leq-trans : ∀ {a b c} → a ≤M b → b ≤M c → a ≤M c
leq-trans leq-zero _ = leq-zero
leq-trans (leq-succ a≤Mb) (leq-succ b≤Mc) = leq-succ (leq-trans a≤Mb b≤Mc)

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

data _/=_ : Nat -> Nat -> Set where
  z̸=s : {n : Nat} -> zero /= suc n
  s̸=z : {n : Nat} -> suc n /= zero
  s̸=s : {m n : Nat} -> m /= n -> suc m /= suc n

data Equal? (n m : Nat) : Set where
  eq : n == m -> Equal? n m
  neq : n /= m -> Equal? n m

equal? : (n m : Nat) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z̸=s
equal? (suc n) zero = neq s̸=z
equal? (suc n) (suc m)  with equal? n m
...                     | neq n/==m = neq (s̸=s n/==m)
equal? (suc n) (suc .n) | eq refl = eq refl

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ y :: ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys

lem-filter : {A : Set}(p : A → Bool)(xs : List A) →
  filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x :: xs) with p x
lem-filter p (x :: xs) | true = keep (lem-filter p xs)
lem-filter p (x :: xs) | false = drop (lem-filter p xs)
--lem-filter p (x :: xs) | true = keep (lem-filter p xs)
--lem-filter p (x :: xs) | false = drop (lem-filter p xs)

{-
_=>_ : (A : Set) → (B : {A : Set} -> Set) → Set
A => B = A -> B {A}
v = Nat => Nat
-}
