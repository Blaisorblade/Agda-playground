-- This file contains my attempts at following McBride's paper "Outrageous but
-- Meaningful Coincidences ─ Dependent type-safe syntax and evaluation".

module Kypling where

data Bot : Set where

record One : Set where
  constructor void

data Two : Set where
  tt ff : Two

data U : Set where
  oBot oOne oTwo : U

record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

open Σ

El : U → Set
El oBot = Bot
El oOne = One
El oTwo = Two

mutual
  data Cx : Set where
    oε : Cx
    _,_ : (Γ : Cx) → (⟦ Γ ⟧C → U) → Cx

  ⟦_⟧C : Cx → Set

  ⟦ oε ⟧C = One
  ⟦ Γ , S ⟧C = Σ ⟦ Γ ⟧C (λ γ → El (S γ))

open import Function using (_∘_)

infixl 0 _∋_

data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧C → U) → Set where
  top : ∀ {Γ T}            → Γ , T ∋ T ∘ fst
  pop : ∀ {Γ S T} → Γ ∋ T → Γ , S ∋ T ∘ fst

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → El (T γ)
⟦ top ⟧∋   (γ , t) = t
⟦ pop x ⟧∋ (γ , s) = ⟦ x ⟧∋ γ
