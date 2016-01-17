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
open import Relation.Binary.HeterogeneousEquality as H

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

-- Import constructors from deBrujin utilities. They will take {Type} as
-- implicit argument, so we can import them once.
open import ReusableDeBrujinSyntax using (keep; drop; ∅; this; that; lemma-var-≅→types; var-≅; ≼-refl)

-- Overload _≼_ by hand.
_≼_ : ∀ {Type} → (Γ₁ Γ₂ : ReusableDeBrujinSyntax.Context Type) → Set
_≼_ {Type} = ReusableDeBrujinSyntax._≼_ Type

open import ReusableDeBrujin Kind ⟦_⟧Kind as K renaming
  ( Context to TContext
  ; Var to TVar
  ; weaken-var to weaken-tvar
  ; ⟦_⟧Context to ⟦_⟧TContext
  ; ⟦_⟧Var to ⟦_⟧TVar
  )

infixr 6 _⇒_
data MonoType (Γ : TContext) : Kind → Set where
  MNat : MonoType Γ ⋆
  _⇒_ : (σ : MonoType Γ ⋆) → (τ : MonoType Γ ⋆) → MonoType Γ ⋆
  tvar : ∀ {k} → TVar Γ k → MonoType Γ k

⟦_⟧MonoType : ∀ {Γ k} → MonoType Γ k → ⟦ Γ ⟧TContext → ⟦ k ⟧Kind
⟦ MNat ⟧MonoType ρ = ℕ
⟦ σ ⇒ τ ⟧MonoType ρ = ⟦ σ ⟧MonoType ρ → ⟦ τ ⟧MonoType ρ
⟦ tvar tv ⟧MonoType ρ = ⟦ tv ⟧TVar ρ

-- Prenex polymorphism; `all` quantifiers aren't allowed everywhere.
data PolyType (Γ : TContext) : Kind → Set where
  mono : (mt : MonoType Γ ⋆) → PolyType Γ ⋆
  all : PolyType (⋆ ∷ Γ) ⋆ → PolyType Γ ⋆

mono0 : (mt : MonoType [] ⋆) → PolyType [] ⋆
mono0 = mono

Nat = mono0 MNat

-- Thanks to predicativity, type variables can only be instantiated by
-- polytypes, so we can write this in Agda without --set-in-set.
⟦_⟧PolyType : ∀ {Γ} → PolyType Γ ⋆ → ⟦ Γ ⟧TContext → Set₁
⟦_⟧PolyType (mono mt) ρ = Lift (⟦ mt ⟧MonoType ρ)
⟦_⟧PolyType (all pt) ρ = ∀ (a : Set) → ⟦ pt ⟧PolyType (a ∷ ρ)

open import ReusableDeBrujin (PolyType [] ⋆) (λ pt → ⟦_⟧PolyType pt [])
  as T

-- Think of this context as
-- x : Nat, f : Nat ⇒ Nat ⊢ f x : Nat
-- However, variables are represented by position, not name.
exampleΓ : Context
exampleΓ = Nat ∷ mono (MNat ⇒ MNat) ∷ []

-- Example of the semantics of a context.
example : ⟦ exampleΓ ⟧Context ≡ HList (λ pt → ⟦_⟧PolyType pt []) exampleΓ
example = refl

anHList : HList (λ pt → ⟦_⟧PolyType pt []) exampleΓ
anHList = lift 42 ∷ lift (λ z → z) ∷ []

exampleEnv  : ⟦ exampleΓ ⟧Context
exampleEnv = anHList

-- Weakening and substitution on types.
weaken-mt : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → MonoType Γ₁ τ → MonoType Γ₂ τ
weaken-mt Γ₁≼Γ₂ MNat = MNat
weaken-mt Γ₁≼Γ₂ (mt₁ ⇒ mt₂) = (weaken-mt Γ₁≼Γ₂ mt₁) ⇒ (weaken-mt Γ₁≼Γ₂ mt₂)
weaken-mt Γ₁≼Γ₂ (tvar x) = tvar (weaken-tvar Γ₁≼Γ₂ x)

weaken-pt : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → PolyType Γ₁ τ → PolyType Γ₂ τ
weaken-pt Γ₁≼Γ₂ (mono mt) = mono (weaken-mt Γ₁≼Γ₂ mt)
weaken-pt Γ₁≼Γ₂ (all t) = all (weaken-pt (keep _ Γ₁≼Γ₂) t)

tvar-subst[_!_:=_]_ : ∀ {Γ₁ Γ₂ σ} → Γ₁ ≼ Γ₂ → TVar Γ₂ σ → MonoType Γ₁ σ → TVar Γ₂ ⋆ → MonoType Γ₂ ⋆
tvar-subst[ Γ₁≼Γ₂ ! x := to-subst ] v with var-≅ _ x v
tvar-subst[ Γ₁≼Γ₂ ! x := to-subst ] v | yes p = weaken-mt Γ₁≼Γ₂ (P.subst (MonoType _) (lemma-var-≅→types _ _ _ p) to-subst)
tvar-subst[ Γ₁≼Γ₂ ! x := to-subst ] v | no ¬p = tvar v

mt-subst[_!_:=_]_ : ∀ {Γ₁ Γ₂ σ} → Γ₁ ≼ Γ₂ → TVar Γ₂ σ → MonoType Γ₁ σ → MonoType Γ₂ ⋆ → MonoType Γ₂ ⋆
mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] MNat = MNat
mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] (mt₁ ⇒ mt₂) = (mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] mt₁) ⇒ (mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] mt₂)
mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] tvar x₁ = tvar-subst[ Γ₁≼Γ₂ ! x := to-subst ] x₁

pt-subst[_!_:=_]_ : ∀ {Γ₁ Γ₂ σ} → Γ₁ ≼ Γ₂ → TVar Γ₂ σ → MonoType Γ₁ σ → PolyType Γ₂ ⋆ → PolyType Γ₂ ⋆
pt-subst[ Γ₁≼Γ₂ ! x := to-subst ] mono mt = mono (mt-subst[ Γ₁≼Γ₂ ! x := to-subst ] mt)
pt-subst[ Γ₁≼Γ₂ ! x := to-subst ] all pt = all (pt-subst[ drop _ Γ₁≼Γ₂ ! that x := to-subst ] pt)

instantiate : ∀ {Γ} → PolyType (⋆ ∷ Γ) ⋆ → MonoType Γ ⋆ → PolyType (⋆ ∷ Γ) ⋆
instantiate pt mt = pt-subst[ drop _ (≼-refl _) ! this := mt ] pt

-- Representation of terms/typing derivations.
--
-- Of note: When we descend in a lambda abstraction, the type of the argument is
-- pushed at the left, so `this` will refer to it. Hence, this are still de
-- Brujin indexes, and not levels (which work the other way around).
data Term : {Δ : TContext} → Context → PolyType Δ ⋆ → Set where
  lit : ∀ {Γ} → (v : ℕ) → Term Γ Nat
  var : ∀ {τ Γ} → Var Γ τ → Term Γ τ
  app : ∀ {σ τ Γ} → Term Γ (mono0 (σ ⇒ τ)) → Term Γ (mono σ) → Term Γ (mono τ)
  lam : ∀ {σ τ Γ} → Term (mono σ ∷ Γ) (mono τ) → Term Γ (mono (σ ⇒ τ))
  tapp : ∀ {Δ Γ} {τ : PolyType (⋆ ∷ Δ) ⋆} → Term Γ (all τ) → (mt : MonoType Δ ⋆) → Term {⋆ ∷ Δ} Γ {! instantiate τ mt !}


{-
subst-lemma-specialcase : ∀ pt mt → ⟦ pt ⟧PolyType (⟦ mt ⟧MonoType [] ∷ []) → ⟦ instantiate′ pt mt ⟧PolyType []
subst-lemma-specialcase (mono mt) s x = {!!}
subst-lemma-specialcase (all pt) s x = λ a → {!!}
-}

⟦_⟧Term : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧PolyType []
⟦_⟧Term (var x) ρ   = ⟦ x ⟧Var ρ
⟦_⟧Term (lit v) ρ   = lift v
⟦_⟧Term (app s t) ρ = lift $ lower (⟦ s ⟧Term ρ) $ lower (⟦ t ⟧Term ρ)
⟦_⟧Term (lam t) ρ   = lift $ λ v → lower $ ⟦ t ⟧Term (lift v ∷ ρ)
-- ⟦_⟧Term (tapp t mt) ρ = {! subst-lemma-specialcase _ mt (⟦ t ⟧Term ρ (⟦ mt ⟧MonoType [])) !}

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
-- weaken-term Γ₁≼Γ₂ (tapp t mt) = tapp (weaken-term Γ₁≼Γ₂ t) mt

-- Weakening is needed for various term transformations. As a motivating
-- example, let's implement substitution, term-subst, even though it's not
-- needed for evaluation.

-- We need lots of utilities first; in particular, we
-- need to compare variables. If two variables match, we need to deduce that
-- they have the same STLC type (through lemma-var-≅→types), so that
-- substitution preserves STLC typing.

-- Let's first implement *decision procedures* for equality.

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

var-subst[_!_:=_]_ : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var Γ₂ σ → Term Γ₁ σ → Var Γ₂ τ → Term Γ₂ τ
var-subst[ Γ₁≼Γ₂ ! x := to-subst ] v with var-≅ _ x v
var-subst[ Γ₁≼Γ₂ ! x := to-subst ] v | yes p = weaken-term Γ₁≼Γ₂ (P.subst (Term _) (lemma-var-≅→types _ _ _ p) to-subst)
var-subst[ Γ₁≼Γ₂ ! x := to-subst ] v | no ¬p = var v

term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var Γ₂ σ → Term Γ₁ σ → Term Γ₂ τ → Term Γ₂ τ
-- term-subst Γ₁≼Γ₂ x to-subst (tapp t mt) = tapp (term-subst Γ₁≼Γ₂ x to-subst t) mt
term-subst Γ₁≼Γ₂ x to-subst (lit v) = lit v
term-subst Γ₁≼Γ₂ x to-subst (app s t) = app (term-subst Γ₁≼Γ₂ x to-subst s) (term-subst Γ₁≼Γ₂ x to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (lam t) = lam (term-subst (drop _ Γ₁≼Γ₂) (that x) to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (var x₁) = var-subst[ Γ₁≼Γ₂ ! x := to-subst ] x₁
