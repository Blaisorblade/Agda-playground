open import Level using (Level) renaming (zero to lzero; suc to lsuc)

module ReusableDeBrujin (Type : Set) {ℓ : Level} (⟦_⟧Type : Type → Set ℓ) where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P

open import Data.Product

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (lift; _+_)
open import Data.Vec hiding (drop)

open import Data.List hiding (drop; all)
open import Data.List.All renaming (All to HList) hiding (all)

Context : Set
Context = List Type

-- The semantics of a typing context is an environment
⟦_⟧Context : Context → Set ℓ
⟦_⟧Context = HList ⟦_⟧Type

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

-- Let's generalize weakening, so that we can weaken a term to any bigger context.
-- So first let's define "bigger context".

infix 4 _≼_
data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅ : [] ≼ []
  keep : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         (τ ∷ Γ₁) ≼ (τ ∷ Γ₂)
  drop : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         Γ₁ ≼ (τ ∷ Γ₂)
