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

open import ReusableDeBrujinSyntax Type public
  hiding (_≼_; keep; drop; this; that; var-≅; lemma-var-≅→types)

open import ReusableDeBrujinSyntax
  using (keep; drop; ∅; this; that)

-- The semantics of a typing context is an environment
⟦_⟧Context : Context → Set ℓ
⟦_⟧Context = HList ⟦_⟧Type

-- ⟦ x ⟧Var is a function that takes an environment ρ and looks x up in it.
⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ this ⟧Var   (v ∷ ρ) = v
⟦ that x ⟧Var (v ∷ ρ) = ⟦ x ⟧Var ρ
