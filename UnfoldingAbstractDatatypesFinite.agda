module UnfoldingAbstractDatatypesFinite where

open import UnfoldingAbstractDatatypesUtils

open import Data.Nat hiding (fold)

open import Data.List
open import Coinduction renaming (unfold to unroll; fold to roll)
open import Level hiding (suc)

unfoldrn : ∀ {a b} → (b → Maybe₂ a b) → b → (b → a) → (n : ℕ) → List a
unfoldrn _ y default 0 = [ default y ]
unfoldrn f y default (suc n) with f y
... | Just₂ x y' = x ∷ (unfoldrn f y' default n)
... | Nothing₂ = []

{-
--Doesn't pass the termination checker for some unclear reason.
TreeN : ∀ {l} → (f : Set l → Set l) → Set l
TreeN f = ⊤ ⊎ Rec (♯ (f (TreeN f)))
-}
{-
--This definition is equivalent, but here the message is more helpful: this is rejected because non-positive.
data TreeN₂ {l} (f : Set l → Set l) : (n : ℕ) → Set l where
  Empty : TreeN₂ f 0
  Wrap₂ : ∀ {n} → Rec (♯ (f (TreeN₂ f n))) → TreeN₂ f (suc n)
-}


TreeN : ∀ {l} → (f : Set l → Set l) → ℕ → Set l
TreeN f 0 = ⊤
TreeN f (suc n) = Rec (♯ (f (TreeN f n)))

unT = unroll

open import LawfulFunctor
unfoldTn : ∀ {l} → {a : Set l} → ∀ {f} → Functor f → (a → f a) → {n : ℕ} → a → TreeN f n

tree : ∀ {f} → Functor f → ADT f → (n : ℕ) → TreeN f n
tree f (D h s) n = unfoldTn f h {n} s

unfoldTn rf f {0} x = tt --x is discarded here!! Bad!! Possibly the proofs still extend to the infinite case, but that's not so clear since equality is always on structures where some data was thrown out. Better use something like the "default" parameter of unfoldrn
unfoldTn rf f {suc n} x = let open Functor rf in (roll ((λ y → unfoldTn rf f {n} y) <$> (f x)))

open import Relation.Binary.PropositionalEquality
open import Function

postulate
  universalUnfoldT : ∀ {l} → {A : Set l} → ∀ {F f n} → ∀ {h : ∀ {n} → A → TreeN F n} → (rf : Functor F) →
    let open Functor rf in h {n} ≡ unfoldTn {a = A} rf f {n} → unT ∘ (h {suc n}) ≡ _<$>_ h ∘ f

  universalUnfoldTRev : ∀ {l} → {A : Set l} → ∀ {F f n} → ∀ {h : ∀ {n} → A → TreeN F n} → (rf : Functor F) →
    let open Functor rf in unT ∘ (h {suc n}) ≡ _<$>_ h ∘ f → h {suc n} ≡ unfoldTn {a = A} rf f {suc n}

lemma : ∀ {l} → {A : Set l} → ∀ {F n} → (rf : Functor F) →
    let open Functor rf in ∀ {f g f'} → f ∘ g ≡ (_<$>_ g) ∘ f' → (unfoldTn {a = A} rf f {suc n}) ∘ g ≡ unfoldTn {a = A} rf f' {suc n}
lemma {l} {A} {F} {n} rf {f} {g} {f'} eq = universalUnfoldTRev {h = λ {n} -> (unfoldTn {a = A} rf f {n}) ∘ g} rf combinesteps
    --(y _ {-(suc n)-}) -- cong {!!} {!!}
 where
  -- we need to apply fusion to the RHS of y!
  y : ∀ n → let open Functor rf in fmap (unfoldTn {a = A} rf f {n}) ∘ f ∘ g ≡ fmap (unfoldTn {a = A} rf f {n}) ∘ (fmap g) ∘ f'
  y n = let open Functor rf in cong (_∘_ (fmap (unfoldTn {a = A} rf f {n}))) eq
  -- here it is!
  fusion_step : let open Functor rf in fmap (unfoldTn {a = A} rf f {n}) ∘ (fmap g) ∘ f' ≡ fmap (unfoldTn {a = A} rf f {n} ∘ g) ∘ f'
  fusion_step = let open Functor rf in cong (λ f₁ → f₁ ∘ f') fusion
  
  combinesteps : let open Functor rf in fmap (unfoldTn {a = A} rf f {n}) ∘ f ∘ g ≡ fmap (unfoldTn {a = A} rf f {n} ∘ g) ∘ f'
  combinesteps = trans (y n) fusion_step
  --combinesteps : {!!}
  --combinesteps with fusion_step | y n
  --... | a | b = {!b!}

--cong {!!} {!!} where
{-
Hp is eq : f ∘ g ≡ (_<$>_ g) ∘ f' (or f ∘ g ≡ fmap g ∘ f')
{Apply fmap (unfold f) ∘ on both sides to get}
fmap (unfold f) ∘ f ∘ g ≡ fmap (unfold f) ∘ fmap g ∘ f'
Fusion on the RHS (not available yet) gives:
fmap (unfold f) ∘ f ∘ g ≡ fmap (unfold f ∘ g) ∘ f'
The LHS, per definition of unfold, is equal to unT ∘ unfold f ∘ g (does Agda know? Probably).
unT ∘ unfold f ∘ g ≡ fmap (unfold f ∘ g) ∘ f'
Applying universalUnfoldTRev with h = unfold f ∘ g gives the result, right?
-}