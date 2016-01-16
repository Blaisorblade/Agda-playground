module Polymorph where

-- Do a calculus with prenex polymorphism.
--
-- Is this closer to Hindley-Milner polymorphism or to predicative System F? I
-- don't know; I'm mainly interested in a simple syntax that can represent
-- Hindley-Milner programs after type inference, not in restricting expressive
-- power to faithfully model a type system. The main reason I don't try
-- representing System F is that impredicativity is hard to interpret in Agda.
--
-- Here we have explicitly-typed, predicative, prenex polymorphism.

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P

open import Data.Product

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (lift; _+_; pred)
open import Data.Vec hiding (drop)

open import Data.List hiding (drop; all)
open import Data.List.All renaming (All to HList) hiding (all)

data Kind : Set where
  ⋆ : Kind

⟦_⟧Kind : Kind → Set₁
⟦ ⋆ ⟧Kind = Set

import ReusableDeBrujin Kind ⟦_⟧Kind as K

data TVar : ℕ → Set where
  this : ∀ {n} → TVar (suc n)
  that : ∀ {n} → TVar n → TVar (suc n)

infixr 6 _⇒_
data MonoType (n : ℕ) : Kind → Set where
  MNat : MonoType n ⋆
  _⇒_ : (σ : MonoType n ⋆) → (τ : MonoType n ⋆) → MonoType n ⋆
  tvar : TVar n → MonoType n ⋆


TContext : ℕ → Set₁
TContext n = Vec Set n

⟦_⟧TVar : ∀ {n} → TVar n → TContext n → Set
⟦_⟧TVar this (x ∷ ρ) = x
⟦_⟧TVar (that tv) (x ∷ ρ) = ⟦ tv ⟧TVar ρ

⟦_⟧MonoType : ∀ {n k} → MonoType n k → TContext n → ⟦ k ⟧Kind
⟦ MNat ⟧MonoType ρ = ℕ
⟦ σ ⇒ τ ⟧MonoType ρ = ⟦ σ ⟧MonoType ρ → ⟦ τ ⟧MonoType ρ
⟦ tvar tv ⟧MonoType ρ = ⟦ tv ⟧TVar ρ

-- Prenex polymorphism; `all` quantifiers aren't allowed everywhere.
data PolyType (n : ℕ) : Kind → Set where
  mono : (mt : MonoType n ⋆) → PolyType n ⋆
  all : PolyType (suc n) ⋆ → PolyType n ⋆

mono0 : (mt : MonoType 0 ⋆) → PolyType 0 ⋆
mono0 = mono

Nat = mono0 MNat

-- Thanks to predicativity, type variables can only be instantiated by
-- polytypes, so we can write this in Agda without --set-in-set.
⟦_⟧PolyType : ∀ {n} → PolyType n ⋆ → TContext n → Set₁
⟦_⟧PolyType (mono mt) ρ = Lift (⟦ mt ⟧MonoType ρ)
⟦_⟧PolyType (all pt) ρ = ∀ (a : Set) → ⟦ pt ⟧PolyType (a ∷ ρ)

TVtoFin : ∀ {n} → TVar n → Fin n
TVtoFin this = zero
TVtoFin (that v) = suc $ TVtoFin v
{-
_≤?_ : ∀ {n} → (a : Fin n) → (b : Fin n) → Dec (a ≤ b)
a ≤? b = toℕ a N.≤? toℕ b
-}

--
-- Untyped deBrujin indexes, based on https://github.com/Gabriel439/Haskell-Morte-Library/issues/1#issue-42860880.

-- XXX
--
-- Time to give up on this redesign. Starting from the usual design is a no-no.
-- It's much easier to reuse the one for typed deBrujin indexes, even if there's
-- a single kind. One could probably specialize it, but there's little point ---
-- and programming with the specialized design is probably harder, since (if the
-- single kind is from a datatype instead of a record, hence without eta) Agda
-- will not identify all kinds, hence it will prevent mixing up types with
-- potentially different kinds.
--
-- XXX

-- 1. Shifting.

-- What one would try writing if variables were integers:
{-
↑[ d , c ]TV x with inject₁ (TVtoFin x) ≤? c
... | yes p = {!x + d!}
... | no ¬p = {!x!}
-}

-- Trick question: should we use (d + n) or (n + d) in the return type?
-- Since + pattern matches only on the LHS, that makes lots of difference.
-- Client-side, d + n appears more convenient, since d is typically known.
-- Implementation-side, it depends.
-- So we define both variants, and tag the (n + d) with ′.
--
-- Client side, use the variant without ′ by default.
--
-- Details: It's often easiest to use P.subst with +-comm to fix type errors,
-- otherwise we need to explicitly prove n + 0 = n and n + suc m = suc (m + n),
-- or even `n + suc zero ≡ suc n`. (That's recorded in history, should you
-- really care.)

-- Variable shift, no cutoff.
↑ : ∀ {n} → (d : ℕ) → TVar n → TVar (d + n)
↑ zero x = x
↑ (suc d) x = that (↑ d x)

↑′ : ∀ {n} → (d : ℕ) → TVar n → TVar (n + d)
↑′ d x = P.subst TVar (+-comm d _) $ ↑ d x

↑′[_,_]TV_ : ∀ {n} → (d : ℕ) → (c : Fin (suc n)) → TVar n → TVar (n + d)
↑′[ d , zero ]TV x = ↑′ d x -- After cutoff, hence shift.
↑′[ d , suc c ]TV this = this -- Before cutoff, no change.
↑′[ d , suc c ]TV that x = that (↑′[ d , c ]TV x)

-- Traverse monotypes. Boring since there are no binders.
↑′[_,_]MT : ∀ {n} → (d : ℕ) → (c : Fin (suc n)) → MonoType n ⋆ → MonoType (n + d) ⋆
↑′[ d , c ]MT MNat = MNat
↑′[ d , c ]MT (mt₁ ⇒ mt₂) = ↑′[ d , c ]MT mt₁ ⇒ ↑′[ d , c ]MT mt₂
↑′[ d , c ]MT (tvar x) = tvar (↑′[ d , c ]TV x)

↑[_,_]MT : ∀ {n} → (d : ℕ) → (c : Fin (suc n)) → MonoType n ⋆ → MonoType (d + n) ⋆
↑[ d , c ]MT mt = P.subst (λ n → MonoType n ⋆)  (+-comm _ d) $ ↑′[ d , c ]MT mt

-- Traverse polytypes.
↑′[_,_]PT : ∀ {n} → (d : ℕ) → (c : Fin (suc n)) → PolyType n ⋆ → PolyType (n + d) ⋆
↑′[ d , c ]PT (mono mt) = mono (↑′[ d , c ]MT mt)
↑′[ d , c ]PT (all pt) = all (↑′[ d , suc c ]PT pt) -- Increase cutoff under binders.
↑[_,_]PT : ∀ {n} → (d : ℕ) → (c : Fin (suc n)) → PolyType n ⋆ → PolyType (d + n) ⋆
↑[ d , c ]PT mt = P.subst (λ n → PolyType n ⋆) (+-comm _ d) $ ↑′[ d , c ]PT mt

-- Substitution.

tvarProvesSuc : ∀ {n} → TVar n → Σ[ m ∈ ℕ ] n ≡ suc m
tvarProvesSuc this = _ , refl
tvarProvesSuc (that f) = _ , refl

finProvesSuc : ∀ {n} → Fin n → Σ[ m ∈ ℕ ] n ≡ suc m
finProvesSuc zero = _ , refl
finProvesSuc (suc f) = _ , refl

-- This integrates a cutoff because it is fused with a negative shift (d = -1, c = 0)
{-
-}
⇣_ : ∀ {n} → TVar (suc n) → TVar n
⇣ this = {!!} -- IMPOSSIBLE
⇣ that x = x

⇣[_]TV_ : ∀ {n} → (c : Fin (suc n)) → TVar (suc n) → TVar n
⇣[ zero ]TV x = ⇣ x -- After cutoff, hence shift.
⇣[ suc c ]TV x with finProvesSuc c
⇣[ suc c ]TV this   | _ , refl = this  -- Before cutoff, no change.
⇣[ suc c ]TV that x | _ , refl = that (⇣[ c ]TV x)

⇣[_]MT_ : ∀ {n} → (c : Fin (suc n)) → MonoType (suc n) ⋆ → MonoType n ⋆
⇣[ c ]MT MNat = MNat
⇣[ c ]MT (mt₁ ⇒ mt₂) = (⇣[ c ]MT mt₁) ⇒ (⇣[ c ]MT mt₂)
⇣[ c ]MT tvar x = tvar (⇣[ c ]TV x)

substTV′[_:=_]_ : ∀ {n} → TVar (suc n) → MonoType n ⋆ → TVar (suc n) → MonoType n ⋆
substTV′[ this := s ] this = s
substTV′[ that x := s ] this with tvarProvesSuc x
... | _ , refl = tvar this
substTV′[ this := s ] that k = tvar k -- Drop
substTV′[ that x := s ] that k with tvarProvesSuc x
... | n , refl = ↑[ suc zero , zero ]MT (substTV′[ x := ⇣[ zero ]MT s ] k)

substMT′[_:=_]_ : ∀ {n} → TVar (suc n) → MonoType n ⋆ → MonoType (suc n) ⋆ → MonoType n ⋆
substMT′[ x := s ] MNat = MNat
substMT′[ x := s ] (mt₁ ⇒ mt₂) = substMT′[ x := s ] mt₁ ⇒ substMT′[ x := s ] mt₂
substMT′[ x := s ] tvar k = substTV′[ x := s ] k

substPT′[_:=_]_ : ∀ {n} → TVar (suc n) → MonoType n ⋆ → PolyType (suc n) ⋆ → PolyType n ⋆
substPT′[ x := s ] mono mt = mono (substMT′[ x := s ] mt)
substPT′[ x := s ] all pt =
    all (substPT′[ that x := ↑[ suc zero , zero ]MT s ] pt)

instantiate′ : ∀ {n} → PolyType (suc n) ⋆ → MonoType n ⋆ → PolyType n ⋆
instantiate′ pt m =  substPT′[ this := m ] pt

{-
this  -- Before cutoff, no change.
⇣[ suc c ]TV that x with finProvesSuc c
... | _ ,  refl = that (⇣[ c ]TV x)

⇣[ suc c ]TV this with finProvesSuc c
... | _ , refl =
⇣[ suc c ]TV that x with finProvesSuc c
... | _ ,  refl =
-}


{-
⇣[_]TV_ : ∀ {n} → (c : Fin (suc n)) → TVar (suc (suc n)) → TVar (suc n)
⇣[ zero ]TV x = ⇣ x -- After cutoff, hence shift.
⇣[ suc c ]TV this = this  -- Before cutoff, no change.
⇣[ suc c ]TV that x with finProvesSuc c
... | _ , refl = that (⇣[ c ]TV x)
-}

{-
substTV′′[_:=_]_!_ : ∀ {n} → TVar (suc n) → MonoType n → TVar (suc n) → (c : Fin n) → MonoType n
substTV′′[ this := s ] this ! c = s
substTV′′[ that x := s ] this ! c  with tvarProvesSuc x
... | _ , refl = tvar this
substTV′′[ this := s ] that tv ! c = {!!}
substTV′′[ that x := s ] that tv ! c = {!!}
-}

{-
substTV[_:=_]_ : ∀ {n} → TVar n → MonoType n → TVar n → MonoType n
substTV[ this := s ] this = s
substTV[ that x := s ] this = tvar this
substTV[ this := s ] that k = tvar (that k)
substTV[ that x := s ] that k = {!substTV[ x := ? ] k!}

_!_substTV[_:=_]_ : ∀ m n → TVar n → MonoType (n + m) → TVar n → MonoType (n + m)
m ! suc n substTV[ this := s ] this = s
m ! suc n substTV[ that x := s ] this = tvar this
m ! suc n substTV[ this := s ] that k = tvar {! that k!}
m ! suc n substTV[ that x := s ] that k = casted
  where
    s′ : MonoType (n + suc m)
    s′ = P.subst MonoType (sym (+-suc n m)) s
    actualRes = suc m ! n substTV[ x := s′ ] k
    casted : MonoType (suc (n + m))
    casted = P.subst MonoType (+-suc n m) actualRes

substMT[_:=_]_ : ∀ {n} → TVar n → MonoType n → MonoType n → MonoType n
substMT[ x := s ] MNat = MNat
substMT[ x := s ] (mt₁ ⇒ mt₂) = substMT[ x := s ] mt₁ ⇒ substMT[ x := s ] mt₂
substMT[ x := s ] tvar k = substTV[ x := s ] k

substPT[_:=_]_ : ∀ {n} → TVar n → MonoType n → PolyType n → PolyType n
substPT[ x := s ] mono mt = mono (substMT[ x := s ] mt)
substPT[ x := s ] all pt =
    all (substPT[ that x := ↑[ suc zero , zero ]MT s ] pt)

shiftM : ∀ {n} → PolyType (suc n) → PolyType n
shiftM = {!!}
--instantiate : ∀ {n} → PolyType (suc n) → TVar (suc n) → MonoType 0 → PolyType n
instantiate : ∀ {n} → PolyType (suc n) → MonoType n → PolyType n
instantiate pt m = shiftM (substPT[ this := ↑[ suc zero , zero ]MT m ] pt)
-}
{-
weakenTV : ∀ {n} → (m : ℕ) → TVar n → TVar (n + m)
weakenTV zero tv = subst TVar (sym (+-right-identity _)) tv
weakenTV (suc m) tv = {!tv!}

weakenMT : ∀ {n} → (m : ℕ) → MonoType n → MonoType (n + m)
weakenMT = {!!}

weakenMT′ : ∀ {n} → (m : ℕ) → MonoType n → MonoType (m + n)
weakenMT′ m mt = subst MonoType (+-comm _ m) (weakenMT m mt)

finProvesSuc : ∀ {n} → Fin n → Σ[ m ∈ ℕ ] n ≡ suc m
finProvesSuc zero = _ , refl
finProvesSuc (suc f) = _ , refl

tSubst : ∀ {n} → TVar (suc n) → Fin (suc n) → MonoType 0 → MonoType n
tSubst this zero m = weakenMT _ m
tSubst this (suc toInst) m with finProvesSuc toInst
... | _ , refl = tvar this
tSubst (that tv) zero m = tvar tv
tSubst (that tv) (suc toInst) m  with finProvesSuc toInst
... | _ , refl = weakenMT′ 1 (tSubst tv toInst m)

instantiateMT : ∀ {n} → MonoType (suc n) → TVar (suc n) → MonoType 0 → MonoType n
instantiateMT MNat toInst m = MNat
instantiateMT (mt₁ ⇒ mt₂) toInst m = instantiateMT mt₁ toInst m ⇒ instantiateMT mt₂ toInst m
instantiateMT (tvar x) toInst m = {!!} {- tSubst x toInst m -}

instantiate : ∀ {n} → PolyType (suc n) → TVar (suc n) → MonoType 0 → PolyType n
instantiate (mono mt) toInst m = mono (instantiateMT mt toInst m)
instantiate (all pt) toInst m = all (instantiate pt (that toInst) m)
-}

subst-lemma-specialcase : ∀ pt mt → ⟦ pt ⟧PolyType (⟦ mt ⟧MonoType [] ∷ []) → ⟦ instantiate′ pt mt ⟧PolyType []
subst-lemma-specialcase (mono mt) s x = {!!}
subst-lemma-specialcase (all pt) s x = λ a → {!!}

open import ReusableDeBrujin (PolyType 0 ⋆) (λ pt → ⟦_⟧PolyType {0} pt [])

-- Think of this context as
-- x : Nat, f : Nat ⇒ Nat ⊢ f x : Nat
-- However, variables are represented by position, not name.
exampleΓ : Context
exampleΓ = Nat ∷ mono (MNat ⇒ MNat) ∷ []

-- Example of the semantics of a context.
example : ⟦ exampleΓ ⟧Context ≡ HList (λ pt → ⟦_⟧PolyType {0} pt []) exampleΓ
example = refl

anHList : HList (λ pt → ⟦_⟧PolyType {0} pt []) exampleΓ
anHList = lift 42 ∷ lift (λ z → z) ∷ []

exampleEnv  : ⟦ exampleΓ ⟧Context
exampleEnv = anHList

-- Representation of terms/typing derivations.
--
-- Of note: When we descend in a lambda abstraction, the type of the argument is
-- pushed at the left, so `this` will refer to it. Hence, this are still de
-- Brujin indexes, and not levels (which work the other way around).
data Term : {n : ℕ} → Context → PolyType n ⋆ → Set where
  lit : ∀ {Γ} → (v : ℕ) → Term Γ Nat
  var : ∀ {τ Γ} → Var Γ τ → Term Γ τ
  app : ∀ {σ τ Γ} → Term Γ (mono0 (σ ⇒ τ)) → Term Γ (mono σ) → Term Γ (mono τ)
  lam : ∀ {σ τ Γ} → Term (mono σ ∷ Γ) (mono τ) → Term Γ (mono (σ ⇒ τ))
  tapp : ∀ {n Γ τ} → Term Γ (all τ) → (mt : MonoType n ⋆) → Term Γ (instantiate′ τ mt)

⟦_⟧Term : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧PolyType []
⟦_⟧Term (var x) ρ   = ⟦ x ⟧Var ρ
⟦_⟧Term (lit v) ρ   = lift v
⟦_⟧Term (app s t) ρ = lift $ lower (⟦ s ⟧Term ρ) $ lower (⟦ t ⟧Term ρ)
⟦_⟧Term (lam t) ρ   = lift $ λ v → lower $ ⟦ t ⟧Term (lift v ∷ ρ)
⟦_⟧Term (tapp t mt) ρ = subst-lemma-specialcase _ mt (⟦ t ⟧Term ρ (⟦ mt ⟧MonoType []))

-- Examples
idNat : Term [] (mono (MNat ⇒ MNat))
idNat = lam (var this)

-- Translate to our STLC embedding the judgment:
-- x : Nat, f : Nat ⇒ Nat ⊢ f x : Nat
-- The deBrujin version of the context is exampleΓ.
exampleTerm : Term exampleΓ Nat
exampleTerm = app (var (that this)) (var this)

-- f : Nat ⇒ Nat ⊢ λ (x : Nat) . f x : Nat ⇒ Nat
exampleTerm-wrapped : Term (mono0 (MNat ⇒ MNat) ∷ []) (mono0 (MNat ⇒ MNat))
exampleTerm-wrapped = lam exampleTerm

-- ⊢ λ (f : Nat ⇒ Nat) (x : Nat) . f x : (Nat ⇒ Nat) ⇒ Nat ⇒ Nat
exampleTerm-closed : Term [] (mono0 ((MNat ⇒ MNat) ⇒ MNat ⇒ MNat))
exampleTerm-closed = lam exampleTerm-wrapped

-- Weakening

weaken-term : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
weaken-term Γ₁≼Γ₂ (lit v) = lit v
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (app s t) = app (weaken-term Γ₁≼Γ₂ s) (weaken-term Γ₁≼Γ₂ t)
weaken-term Γ₁≼Γ₂ (lam t) = lam (weaken-term (keep _ Γ₁≼Γ₂) t)
weaken-term Γ₁≼Γ₂ (tapp t mt) = tapp (weaken-term Γ₁≼Γ₂ t) mt

-- Weakening is needed for various term transformations. As a motivating
-- example, let's implement substitution, term-subst, even though it's not
-- needed for evaluation.

-- We need lots of utilities first; in particular, we
-- need to compare variables. If two variables match, we need to deduce that
-- they have the same STLC type (through lemma-var-≅→types), so that
-- substitution preserves STLC typing.

-- Let's first implement *decision procedures* for equality.

-- Let's start from equality on numbers.
exercise-nat-≟ : (a b : ℕ) → Dec (a ≡ b)
exercise-nat-≟ zero zero = yes refl
exercise-nat-≟ zero (suc b) = no (λ ())
exercise-nat-≟ (suc a) zero = no (λ ())
exercise-nat-≟ (suc a) (suc b) with exercise-nat-≟ a b
exercise-nat-≟ (suc a) (suc .a) | yes refl = yes refl
exercise-nat-≟ (suc a) (suc b)  | no ¬p = no (λ suc-a≡suc-b → ¬p (P.cong pred suc-a≡suc-b))

vthat : ∀ {σ Γ τ} → Var Γ τ → Var (σ ∷ Γ) τ
vthat = that

-- This lemma witnesses that the data constructor `that` is injective.
exercise-lemma-that-injective-≡ : ∀ {Γ σ τ} {x₁ : Var Γ τ} {x₂ : Var Γ τ} → vthat {σ} x₁ ≡ vthat {σ} x₂ → x₁ ≡ x₂
exercise-lemma-that-injective-≡ refl = refl

-- A decision procedure for heterogeneous variable equality. This is designed
-- for what we need in substitution, so doesn't compare variables across
-- contexts --- that would not be a well-defined operation anyway.
exercise-var-≟ : ∀ {Γ τ} → (x₁ : Var τ Γ) → (x₂ : Var τ Γ) → Dec (x₁ ≡ x₂)
exercise-var-≟ this this = yes refl
exercise-var-≟ this (that x₂) = no (λ ())
exercise-var-≟ (that x₁) this = no (λ ())
exercise-var-≟ (that x₁) (that x₂) with exercise-var-≟ x₁ x₂
exercise-var-≟ (that x₁) (that x₂) | yes x₁≡x₂ = yes (P.cong that x₁≡x₂)
exercise-var-≟ (that x₁) (that x₂) | no ¬x₁≡x₂ = no (λ that-x₁≡that-x₂ → ¬x₁≡x₂ (exercise-lemma-that-injective-≡ that-x₁≡that-x₂))

open import Relation.Binary.HeterogeneousEquality as H

-- Inspired from answers to http://stackoverflow.com/q/24139810/53974. The
-- standard H.cong is not flexible enough. This probably belongs in the standard
-- library.
hcong : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
      {ax ay} {x : B ax} {y : B ay} (f : ∀ {z} (x : B z) → C x) →
      ax ≡ ay →
      x ≅ y → f x ≅ f y
hcong f refl refl = refl

-- Only works if τ is an index of Var, not a parameter O_O.
lemma-that-injective-≅ : ∀ {Γ σ₀ σ τ} {x₁ : Var Γ σ} {x₂ : Var Γ τ} → vthat {σ₀} x₁ ≅ vthat {σ₀} x₂ → x₁ ≅ x₂
lemma-that-injective-≅ refl = refl

-- Prove that the *type constructor* Var Γ is injective: if x₁ ≅ x₂, they're in
-- the same type, so Var Γ σ ≡ Var Γ τ. Hence, σ ≡ τ.
lemma-var-≅→types : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → x₁ ≅ x₂ → σ ≡ τ
lemma-var-≅→types this this x₁≅x₂ = refl
lemma-var-≅→types (that x₁) (that .x₁) refl = refl
lemma-var-≅→types this (that x₂) ()
lemma-var-≅→types (that x₁) this ()

var-≅ : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Dec (x₁ ≅ x₂)
var-≅ this this = yes refl
var-≅ this (that x₂) = no (λ ())
var-≅ (that x₁) this = no (λ ())
var-≅ (that x₁) (that x₂) with var-≅ x₁ x₂
var-≅ (that x₁) (that x₂) | yes x₁≅x₂ = yes (hcong that (lemma-var-≅→types x₁ x₂ x₁≅x₂) x₁≅x₂)
var-≅ (that x₁) (that x₂) | no ¬x₁≅x₂ = no (λ that-x₁≅that-x₂ → ¬x₁≅x₂ (lemma-that-injective-≅ that-x₁≅that-x₂))

term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var Γ₂ σ → Term Γ₁ σ → Term Γ₂ τ → Term Γ₂ τ
term-subst Γ₁≼Γ₂ x to-subst (tapp t mt) = tapp (term-subst Γ₁≼Γ₂ x to-subst t) mt
term-subst Γ₁≼Γ₂ x to-subst (lit v) = lit v
term-subst Γ₁≼Γ₂ x to-subst (app s t) = app (term-subst Γ₁≼Γ₂ x to-subst s) (term-subst Γ₁≼Γ₂ x to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (lam t) = lam (term-subst (drop _ Γ₁≼Γ₂) (that x) to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (var x₁) with var-≅ x x₁
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | yes p = weaken-term Γ₁≼Γ₂ (P.subst (Term _) (lemma-var-≅→types _ _ p) to-subst)
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | no ¬p = var x₁
