module UniverseExample where

open import Data.String
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Product

-- import Universe

data Column : Set where
  TEXT : Column
  NAT : Column

⟦_⟧ : Column → Set
⟦ TEXT ⟧ = String
⟦ NAT ⟧ = ℕ

showCol : {c : Column} → ⟦ c ⟧ → String
showCol {TEXT} s = s
showCol {NAT} n = {!showℕ!}

-- showRow :

Schema : Set
Schema = List (String × Column)

ScoreSchema : Schema
ScoreSchema = {!!}
{-
⟦_⟧ₛ :

DB : Schema → Set₁
DB = List ∘ ⟦_⟧ₛ

showDatabase : {s : Schema} → DB s → String
showDatabase = ?
-}
