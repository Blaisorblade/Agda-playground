-- Implement simply-typed lambda calculus (STLC) using typed de Brujin indexes,
-- also as a case study in dependent pattern matching.

module TypedDeBrujinWithFix where

infixr 6 _⇒_

data Type : Set where
  Nat : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

open import Data.Nat

-- Step-Indexed Partiality Monad
--
-- Inspired (probably identical) to Rompf and Anin's arXiv:1510.05216v1.
data Result (τ : Set) : Set where
  Error : Result τ
  Val : τ → Result τ

data PartialResult (τ : Set) : Set where
  Timeout : PartialResult τ
  Done : Result τ →  PartialResult τ

-- Needed implementations of monadic bind and return.
-- I'm sure we could overload _>>=_ and return.
_bindPartialResult_ : ∀ {σ τ} → PartialResult σ → (σ → PartialResult τ) → PartialResult τ
_bindPartialResult_ Timeout f = Timeout
_bindPartialResult_ (Done Error) f = Done Error
_bindPartialResult_ (Done (Val x)) f = f x

open import Function
Partial : Set → Set
Partial τ = (fuel : ℕ) → (PartialResult τ)

returnPartial : ∀ {t} → t → Partial t
returnPartial v = λ fuel → Done (Val v)

-- Values are CBV function spaces
⟦_⟧Type : Type → Set
⟦ Nat ⟧Type  = ℕ
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → Partial (⟦ τ ⟧Type)

open import Data.List hiding (drop)

Context : Set
Context = List Type

open import Data.List.All renaming (All to HList)

-- The semantics of a typing context is an environment
⟦_⟧Context : Context → Set
⟦_⟧Context = HList ⟦_⟧Type

open import Relation.Binary.PropositionalEquality as P

-- Think of this context as
-- x : Nat, f : Nat ⇒ Nat ⊢ f x : Nat
-- However, variables are represented by position, not name.
exampleΓ : Context
exampleΓ = Nat ∷ Nat ⇒ Nat ∷ []

-- Example of the semantics of a context.
example : ⟦ exampleΓ ⟧Context ≡ HList ⟦_⟧Type exampleΓ
example = refl

anHList : HList ⟦_⟧Type exampleΓ
anHList = 42 ∷ (λ z → returnPartial z) ∷ []

exampleEnv  : ⟦ exampleΓ ⟧Context
exampleEnv = anHList

-- Typed de Brujin indexes. `this` is the leftmost variable in the context,
-- `that this` the second, and so on. You can read values as natural numbers,
-- but they carry more information -- a Var Γ τ is both a variable and a proof
-- that it is valid in the given context.
data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ ∷ Γ) τ
  that : ∀ {σ Γ τ} → Var Γ τ → Var (σ ∷ Γ) τ

-- ⟦ x ⟧Var is a function that takes an environment ρ and looks x up in it.
⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ this ⟧Var   (v ∷ ρ) = v
⟦ that x ⟧Var (v ∷ ρ) = ⟦ x ⟧Var ρ

-- Representation of terms/typing derivations.
--
-- Of note: When we descend in a lambda abstraction, the type of the argument is
-- pushed at the left, so `this` will refer to it. Hence, this are still de
-- Brujin indexes, and not levels (which work the other way around).
data Term : Context → Type → Set where
  lit : ∀ {Γ} → (v : ℕ) → Term Γ Nat
  var : ∀ {τ Γ} → Var Γ τ → Term Γ τ
  app : ∀ {σ τ Γ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ {σ τ Γ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  fix : ∀ {τ Γ} → Term (τ ∷ Γ) τ → Term Γ τ

{-# TERMINATING #-}
doEval : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧Context → Partial (⟦ τ ⟧Type)
⟦_⟧Term : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧Context → Partial (⟦ τ ⟧Type)

doEval (lit v) ρ fuel = Done (Val v)
doEval (var x) ρ fuel = Done (Val (⟦ x ⟧Var ρ))
doEval (app s t) ρ fuel = (⟦ s ⟧Term ρ fuel) bindPartialResult (λ f →
  ⟦ t ⟧Term ρ fuel bindPartialResult (λ v →
    f v fuel))
doEval (lam t) ρ fuel = Done (Val (λ v → ⟦ t ⟧Term (v ∷ ρ)))

-- This definition is theoretically correct, but does not have the correct
-- operational behavior (and wouldn't have the right cost in a cost monad). In
-- particular, if t is not a lambda abstraction, it executes fuel steps of the
-- fixpoint in a potentially eager way, even when many fewer are needed.
-- Since fuel can be arbitrarily big, this induces an arbitrary slowdown.
doEval (fix t) ρ fuel = (⟦ fix t ⟧Term ρ fuel) bindPartialResult (λ v →
  ⟦ t ⟧Term (v ∷ ρ) fuel)

open import Data.Unit

checkFuel : Partial ℕ
checkFuel zero = Timeout
checkFuel (suc fuel) = Done (Val fuel)

⟦_⟧Term t ρ fuel = (checkFuel fuel) bindPartialResult (doEval t ρ)

-- inline this to pass termination checking:
{-
checkFuel : ∀ {τ} → Partial τ → Partial τ
checkFuel res zero = Timeout
checkFuel res (suc fuel) = res fuel

⟦_⟧Term t ρ = checkFuel (doEval t ρ)

⟦_⟧Term t ρ zero = Timeout
⟦_⟧Term t ρ (suc fuel) = doEval t ρ fuel

-}


{-
⟦_⟧Term (lit v) ρ = {! }Done v
⟦_⟧Term (var x) ρ = Done (⟦ x ⟧Var ρ)
⟦_⟧Term (app s t) ρ = {! ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ) !}
⟦_⟧Term (lam t) ρ = {! λ v → ⟦ t ⟧Term (v ∷ ρ) !}
⟦_⟧Term (fix t) ρ = {!!}
-}
-- Examples
idNat : Term [] (Nat ⇒ Nat)
idNat = lam (var this)

-- Translate to our STLC embedding the judgment:
-- x : Nat, f : Nat ⇒ Nat ⊢ f x : Nat
-- The deBrujin version of the context is exampleΓ.
exampleTerm : Term exampleΓ Nat
exampleTerm = app (var (that this)) (var this)

-- f : Nat ⇒ Nat ⊢ λ (x : Nat) . f x : Nat ⇒ Nat
exampleTerm-wrapped : Term (Nat ⇒ Nat ∷ []) (Nat ⇒ Nat)
exampleTerm-wrapped = lam exampleTerm

-- ⊢ λ (f : Nat ⇒ Nat) (x : Nat) . f x : (Nat ⇒ Nat) ⇒ Nat ⇒ Nat
exampleTerm-closed : Term [] ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat)
exampleTerm-closed = lam exampleTerm-wrapped

-- Back to the code. Let's try implementing weakening, for variables and terms.
-- First attempt. Trivial for variables:
weakenVar₁ : ∀ {Γ σ τ} → Var Γ τ → Var (σ ∷ Γ) τ
weakenVar₁ = that

-- Impossible for terms, because the induction hypothesis is not strong enough.
{-
weakenTerm₁ : ∀ {Γ σ τ} → Term τ Γ → Term τ (σ ∷ Γ)
weakenTerm₁ (lit x) = lit x
weakenTerm₁ (var x) = var (weakenVar₁ x)
weakenTerm₁ (app s t) = app (weakenTerm₁ s) (weakenTerm₁ t)
weakenTerm₁ (lam t) = lam {!!}
-}

-- -- Let's generalize weakening, so that we can weaken a term to any bigger context.
-- -- So first let's define "bigger context".

-- infix 4 _≼_
-- data _≼_ : (Γ₁ Γ₂ : Context) → Set where
--   ∅ : [] ≼ []
--   keep : ∀ {Γ₁ Γ₂} → (τ : Type) →
--          Γ₁ ≼ Γ₂ →
--          (τ ∷ Γ₁) ≼ (τ ∷ Γ₂)
--   drop : ∀ {Γ₁ Γ₂} → (τ : Type) →
--          Γ₁ ≼ Γ₂ →
--          Γ₁ ≼ (τ ∷ Γ₂)

-- -- Now weakening works.
-- weaken-var : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
-- weaken-var (keep τ Γ₁≼Γ₂) this = this
-- weaken-var (keep σ Γ₁≼Γ₂) (that x) = that (weaken-var Γ₁≼Γ₂ x)
-- weaken-var (drop τ₁ Γ₁≼Γ₂) x = that (weaken-var Γ₁≼Γ₂ x)

-- weaken-term : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
-- weaken-term Γ₁≼Γ₂ (lit v) = lit v
-- weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
-- weaken-term Γ₁≼Γ₂ (app s t) = app (weaken-term Γ₁≼Γ₂ s) (weaken-term Γ₁≼Γ₂ t)
-- weaken-term Γ₁≼Γ₂ (lam t) = lam (weaken-term (keep _ Γ₁≼Γ₂) t)

-- -- Weakening is needed for various term transformations. As a motivating
-- -- example, let's implement substitution, term-subst, even though it's not
-- -- needed for evaluation.

-- -- We need lots of utilities first; in particular, we
-- -- need to compare variables. If two variables match, we need to deduce that
-- -- they have the same STLC type (through lemma-var-≅→types), so that
-- -- substitution preserves STLC typing.

-- -- Let's first implement *decision procedures* for equality.

-- open import Relation.Nullary

-- -- Let's start from equality on numbers.
-- exercise-nat-≟ : (a b : ℕ) → Dec (a ≡ b)
-- exercise-nat-≟ zero zero = yes refl
-- exercise-nat-≟ zero (suc b) = no (λ ())
-- exercise-nat-≟ (suc a) zero = no (λ ())
-- exercise-nat-≟ (suc a) (suc b) with exercise-nat-≟ a b
-- exercise-nat-≟ (suc a) (suc .a) | yes refl = yes refl
-- exercise-nat-≟ (suc a) (suc b)  | no ¬p = no (λ suc-a≡suc-b → ¬p (P.cong pred suc-a≡suc-b))

-- -- This lemma witnesses that the data constructor `that` is injective.
-- exercise-lemma-that-injective-≡ : ∀ {Γ σ τ} {x₁ : Var Γ τ} {x₂ : Var Γ τ} → that {σ} x₁ ≡ that {σ} x₂ → x₁ ≡ x₂
-- exercise-lemma-that-injective-≡ refl = refl

-- -- A decision procedure for heterogeneous variable equality. This is designed
-- -- for what we need in substitution, so doesn't compare variables across
-- -- contexts --- that would not be a well-defined operation anyway.
-- exercise-var-≟ : ∀ {Γ τ} → (x₁ : Var τ Γ) → (x₂ : Var τ Γ) → Dec (x₁ ≡ x₂)
-- exercise-var-≟ this this = yes refl
-- exercise-var-≟ this (that x₂) = no (λ ())
-- exercise-var-≟ (that x₁) this = no (λ ())
-- exercise-var-≟ (that x₁) (that x₂) with exercise-var-≟ x₁ x₂
-- exercise-var-≟ (that x₁) (that x₂) | yes x₁≡x₂ = yes (P.cong that x₁≡x₂)
-- exercise-var-≟ (that x₁) (that x₂) | no ¬x₁≡x₂ = no (λ that-x₁≡that-x₂ → ¬x₁≡x₂ (exercise-lemma-that-injective-≡ that-x₁≡that-x₂))

-- open import Relation.Binary.HeterogeneousEquality as H

-- -- Inspired from answers to http://stackoverflow.com/q/24139810/53974. The
-- -- standard H.cong is not flexible enough. This probably belongs in the standard
-- -- library.
-- hcong : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
--       {ax ay} {x : B ax} {y : B ay} (f : ∀ {z} (x : B z) → C x) →
--       ax ≡ ay →
--       x ≅ y → f x ≅ f y
-- hcong f refl refl = refl

-- -- Only works if τ is an index of Var, not a parameter O_O.
-- lemma-that-injective-≅ : ∀ {Γ σ₀ σ τ} {x₁ : Var Γ σ} {x₂ : Var Γ τ} → that {σ₀} x₁ ≅ that {σ₀} x₂ → x₁ ≅ x₂
-- lemma-that-injective-≅ refl = refl

-- -- Prove that the *type constructor* Var Γ is injective: if x₁ ≅ x₂, they're in
-- -- the same type, so Var Γ σ ≡ Var Γ τ. Hence, σ ≡ τ.
-- lemma-var-≅→types : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → x₁ ≅ x₂ → σ ≡ τ
-- lemma-var-≅→types this this x₁≅x₂ = refl
-- lemma-var-≅→types (that x₁) (that .x₁) refl = refl
-- lemma-var-≅→types this (that x₂) ()
-- lemma-var-≅→types (that x₁) this ()

-- var-≅ : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Dec (x₁ ≅ x₂)
-- var-≅ this this = yes refl
-- var-≅ this (that x₂) = no (λ ())
-- var-≅ (that x₁) this = no (λ ())
-- var-≅ (that x₁) (that x₂) with var-≅ x₁ x₂
-- var-≅ (that x₁) (that x₂) | yes x₁≅x₂ = yes (hcong that (lemma-var-≅→types x₁ x₂ x₁≅x₂) x₁≅x₂)
-- var-≅ (that x₁) (that x₂) | no ¬x₁≅x₂ = no (λ that-x₁≅that-x₂ → ¬x₁≅x₂ (lemma-that-injective-≅ that-x₁≅that-x₂))

-- term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var Γ₂ σ → Term Γ₁ σ → Term Γ₂ τ → Term Γ₂ τ
-- term-subst Γ₁≼Γ₂ x to-subst (lit v) = lit v
-- term-subst Γ₁≼Γ₂ x to-subst (app s t) = app (term-subst Γ₁≼Γ₂ x to-subst s) (term-subst Γ₁≼Γ₂ x to-subst t)
-- term-subst Γ₁≼Γ₂ x to-subst (lam t) = lam (term-subst (drop _ Γ₁≼Γ₂) (that x) to-subst t)
-- term-subst Γ₁≼Γ₂ x to-subst (var x₁) with var-≅ x x₁
-- term-subst Γ₁≼Γ₂ x to-subst (var x₁) | yes p = weaken-term Γ₁≼Γ₂ (P.subst (Term _) (lemma-var-≅→types _ _ p) to-subst)
-- term-subst Γ₁≼Γ₂ x to-subst (var x₁) | no ¬p = var x₁
