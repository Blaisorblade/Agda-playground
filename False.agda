open import Relation.Binary

module False where

open import Data.Product
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

x : (⊤ × ℕ) × (⊤ × ⊤)
x = (_ , 1) , (_ , _)

y : (⊤ × ℕ) × (⊤ × ⊤)
y = (_ , 0) , (_ , _)

foo : ⊤
foo = let (_ , (b , _)) = x in b

bar : ⊤
bar = let (_ , (b , _)) = y in b


-- eq : foo ≡ bar → ⊥
-- eq ()

-- all-eq : ∀ {x y : ⊤} → x ≡ y
-- all-eq = refl

-- false : ⊥
-- false = eq all-eq
