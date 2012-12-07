module OrnamentalAlgebras where

open import Level

data [ze,su] : Set where
  ze su : [ze,su]

ze↦_su↦_ : ∀ {a} → {P : [ze,su] → Set a} → P ze → P su → (c : [ze,su]) → P c
(ze↦ z su↦ s) ze = z
(ze↦ z su↦ s) su = s

data Desc : Set1 where
  end    :                          Desc
  σ      : (S : Set) → (S → Desc) → Desc
  node×_ : Desc →                   Desc

NatP : Desc
NatP = σ [ze,su] (ze↦ end  su↦ node× end)

open import Data.Unit     -- The unit type.

{-
⟦_⟧ : Desc → Set → Set
⟦ end     ⟧ X = ⊤
⟦ σ S D   ⟧ X = \Sigma S (λ s → ⟦ D s ⟧ X)
⟦ node× D ⟧ X = X × ⟦ D ⟧ X
-}