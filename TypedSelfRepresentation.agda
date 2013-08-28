open import Data.Nat
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H
open import Level

-- A typed self representation in language L would (not so obviously) provide a
-- function `decode` which can produce, in its image, all possible ℕ → ℕ
-- functions. However, below we create (in Agda) function newFun (which can be
-- expressed without advanced features, hence presumably also in L), and prove
-- that (just newFun) can't appear in the image of `decode`.

-- The proof assumes implicitly that the language is strongly normalizing: the
-- assumption happens because decode is assumed to produce Agda values. It is
-- also necessary, because if decode n produce a function diverging on n, newFun
-- will diverge on n as well.

-- XXX: rephrase the above to state the theorem at once.
-- And remove experiments from below.

-- Future work: argue that TSR actually provides `decode`. This is much harder,
-- as the concept ofTSR is much more ill-defined.

module TypedSelfRepresentation where
  module Proof (decode : ℕ → Maybe (ℕ → ℕ)) where
{-
    newFun : ℕ → ℕ
    newFun n with decode n
    ... | just decodedF = decodedF n + 1
    ... | nothing       = 0
-}
    -- Desugar with by hand, to ease equational reasoning.

    newFunHelp : ℕ → Maybe (ℕ → ℕ) → ℕ
    -- Writing (1 + ...) instead of (... + 1) simplified the proof.
    newFunHelp n (just decodedF) = 1 + decodedF n
    newFunHelp n nothing         = 0

    newFun : ℕ → ℕ
    newFun n = newFunHelp n (decode n)

{-
    forwardstep : ∀ n decodedF → decode n ≡ just decodedF → newFun n ≡ decodedF n + 1
    forwardstep n decodedF ≡₀ = {! subst  !}
-}

    absurd : ∀ x → ¬ (x ≡ 1 + x)
    absurd n ()

    invertMaybe : ∀ {ℓ} {A : Set ℓ} {a b : A} → _≡_ {ℓ} {Maybe A} (just a) (just b) → a ≡ b
    invertMaybe refl = refl

    step₁ : ∀ {f} x → f ≡ newFun → f x ≡ newFun x
    step₁ x ≡ = cong (λ g → g x) ≡

    step₂ : ∀ {n decodedF} → decode n ≡ just decodedF → decodedF n ≡ newFun n → ⊥
    step₂ {n} {decodedF} ≡₀ ≡₁ = absurd _ (subst (λ x → decodedF n ≡ newFunHelp n x) ≡₀ ≡₁)

    -- Main theorem: just newFun is not in the image of decode.
    newFunIsNotDecoded : ¬ (Σ[ n ∈ ℕ ] decode n ≡ just newFun)
    -- newFunIsNotDecoded : ¬ {!Σ[ n ∈ ℕ ] (∀ x → maybe′  (decode n) x ≡ newFun x)!}

    --newFunIsNotDecoded : ¬ Σ ℕ (λ n → decode n ≡ just newFun)
    --newFunIsNotDecoded : ¬ (Σ[ n ∈ ℕ ] (_≅_ (decode n) {B = Maybe (ℕ → ℕ)} (just newFun)))
    newFunIsNotDecoded (n , ≡₁) with decode n | inspect decode n
    --newFunIsNotDecoded (n , refl) | just .(λ n₁ → newFun decode n₁ | decode n₁) = ?
    newFunIsNotDecoded (n , ()) | nothing | _
    newFunIsNotDecoded (n , ≡₁) | just decodedF | [ eq ] = step₂ eq (step₁ n (invertMaybe ≡₁))
