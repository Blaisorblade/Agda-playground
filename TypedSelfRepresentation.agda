{-

Encode in Agda (most of) the standard recursion-theoretic proof that a total
language cannot contain its own self-interpreter. The only difference is that I
use the Maybe type to indicate failure. The usual recursion-theoretic proof
allows indicating failure, but in a more contorted and less elegant way. If we
want to extend the proof to cover languages where Maybe and first-class
functions might not be definable, switching back to the recursion-theoretic
presentation might help.

Moreover, the comments explain a bit how this extends to TSR. But I don't claim
they actually do it well - the rest appears in my head after I re-study this.
I'll add text.

-- For reference, we need the standard recursion-theoretic argument. See for
-- instance this email from Conor McBride if you need a refresher.
-- http://www.haskell.org/pipermail/haskell-cafe/2003-May/004343.html

-}

open import Data.Nat
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H
open import Level

-- A typed self representation in language L would (not so obviously) provide a
-- function `decode` which can produce, in its image, all possible ℕ → ℕ
-- functions. However, below we create (in Agda) function newFun (which can be
-- expressed without advanced features, hence presumably also in L), and prove
-- that (just newFun) can't appear in the image of `decode`.

-- The proof assumes *implicitly* that the language is strongly normalizing: the
-- assumption happens because decode is assumed to produce Agda values, instead
-- of being in some partiality monad.
--
-- XXX: rephrase the above to state the theorem at once.

-- Concretely, if there were an n such that decode n = just newFun, then you
-- could see that newFun n = 1 + newFun n:
--
-- newFun n = newFunHelp n (decode n) = newFunHelp n (just newFun) = 1 + newFun n.
--
-- If the language is total, that's an equality of naturals, which is absurd.
-- Otherwise, if newFun n loops, newFun n = 1 + newFun n becomes simply ⊥ = ⊥,
-- which is true. That uses denotational semantics (which is not appropriate
-- here), but in recursion-theoretic terms, newFun n will simply keep looping,
-- much as f x = 1 + f x loops.
--
-- Relation to soundness
------------------------
--
-- Does the proof relate to soundness? I'm somewhat confused on this, but below
-- there's some discussion on the issue.
--
-- Well, it uses a typed self interpreter (∀
-- τ → Expr τ → τ), and we've argued forever this is a proof of soundness for
-- the object language in the metalanguage: if you have a (proof) term of type τ
-- in the object language / typed self-representation, then you also have an
-- inhabitant for τ. Under Curry-Howard, this becomes indeed a proof of semantic consistency.
--
-- But what does such a proof mean when the metalanguage and the object language
-- coincide? The assumption seems related to Gӧdel's theorems.
--
-- I think this corresponds in particular to semantic consistency: the proof
-- theory (Expr T) has a model (T). Instead, Gӧdel's theorem seem to use
-- syntactic consistency. According to Wikipedia
-- (http://en.wikipedia.org/wiki/Consistency), these consistencies are not the
-- same thing for incomplete logics, and anything beyond first-order logic is
-- incomplete. This would be an interesting difference between what I do and
-- using Gӧdel's theorem. In fact, what I do seems closer to Tarski's
-- undefinability theorem
-- (http://en.wikipedia.org/wiki/Tarski's_undefinability_theorem), which is
-- well-known to be simpler to prove than Gӧdel's.
--
-- Quoting Wikipedia:
--   An interpreted language is strongly-semantically-self-representational
--   exactly when the language contains predicates and function symbols defining
--   all the semantic concepts specific to the language. Hence the required
--   functions include the "semantic valuation function" mapping a formula A to
--   its truth value ||A||, and the "semantic denotation function" mapping a
--   term t to the object it denotes. Tarski's theorem then generalizes as
--   follows: No sufficiently powerful language is
--   strongly-semantically-self-representational.
--
-- Strong semantical self-representation is simpler than the non-existing
-- "perfect TSR" (TSR for a strongly normalizing and consistent language)
-- because propositions are simply true or false, unlike types -- proofs are
-- irrelevant.
--
-- The "total self-interpreting language" of recursion-theory theorem, instead,
-- is simpler than what we do because the language has values but does not have
-- types.
--
-- From a Curry-Howard point-of-view, what we do is simply combine both things
-- to discuss a proof-relevant version of Tarski's theorem, where formulas are
-- replaced by *quoted proof terms* and truth values are represented by values
-- inhabiting a term.

module TypedSelfRepresentation where

  --open import Data.Maybe using (just; nothing; Maybe)
  data Maybe {a} (A : Set a) : Set a where
    just    : (x : A) → Maybe A
    nothing : Maybe A

  module Proof (decode : ℕ → Maybe (ℕ → ℕ)) where
    -- What's below avoid using 'with' to ease equational reasoning.

    newFunHelp : ℕ → Maybe (ℕ → ℕ) → ℕ
    -- Writing (1 + ...) instead of (... + 1) simplified the proof.
    newFunHelp n (just decodedF) = 1 + decodedF n
    newFunHelp n nothing         = 0

    -- With the help of decode, we can write a function which cannot be in the
    -- language.
    newFun : ℕ → ℕ
    newFun n = newFunHelp n (decode n)

    absurd : ∀ {x} → ¬ (x ≡ 1 + x)
    absurd ()

    invertMaybe : ∀ {ℓ} {A : Set ℓ} {a b : A} → just a ≡ just b → a ≡ b
    invertMaybe refl = refl

    step₁ : ∀ {f} x → f ≡ newFun → f x ≡ newFun x
    step₁ x refl = refl

    step₂ : ∀ {n decodedF} → decode n ≡ just decodedF → decodedF n ≡ newFun n → ⊥
    step₂ {n} {decodedF} ≡₀ ≡₁ = absurd (subst (λ x → decodedF n ≡ newFunHelp n x) ≡₀ ≡₁)

    -- Main theorem: just newFun is not in the image of decode.
    --
    -- So, a decode always producing "Nothing" is fine, but a decode which is
    -- surjective on programs in the language and is part of the language itself
    -- is not possible.
    newFunIsNotDecoded : ¬ (Σ[ n ∈ ℕ ] decode n ≡ just newFun)
    newFunIsNotDecoded (n , ≡₁) with decode n | inspect decode n
    newFunIsNotDecoded (n , ()) | nothing | _
    newFunIsNotDecoded (n , ≡₁) | just decodedF | [ eq ] = step₂ eq (step₁ n (invertMaybe ≡₁))

    -- Summary of the above:
    --
    --   Strongly normalizing language => newFun is not in the image of decode.
    --
    -- We also have the contrapositive:
    --
    --   newFun is in the image of decode => NOT (Strongly normalizing language)
    --
    -- Just to remind us that contrapositives hold also intuistionistically:
    contrapositive : ∀ {ℓ} {A B : Set ℓ} → (A → ¬ B) → (B → ¬ A)
    contrapositive f = λ b a → f a b

  -- What's below argues that (forms of) TSR actually provides `decode`. This is
  -- much harder, as the concept of TSR is less well-defined. It's easy to build
  -- decode from a self-typechecker, but the TSR paper does not provide that─but
  -- it would be natural for TSR in Agda.

  --
  -- Let's extend this to TSR. It turns out that giving an abstraction of a
  -- language is rather easy, and this allows seeing how much crazy stuff one
  -- needs to assemble a self-typechecker and a self-interpreter together into a
  -- decode function.

  module ProofTSR
                            -- Hypotheses/assumptions:
    (Type : Set)            -- a datatype of codes for types of the object language
    (⟦_⟧ : Type → Set)      -- with some interpretation function.
    (′ℕ→ℕ : Type)           -- Assume there's a code for the type ℕ → ℕ
    (⟦′ℕ→ℕ⟧≡ℕ→ℕ :
      ⟦ ′ℕ→ℕ ⟧ ≡ (ℕ → ℕ))
                            -- Assume that codes have decidable equality (must be finite).
    (_≟T_ : Decidable (_≡_ {A = Type}))

                            -- A type of expressions.
    (Expr : Type → Set)
                            -- Self-typechecker and interpreter.
    (self-typechecker : ℕ → Maybe (Σ[ τ ∈ Type ] Expr τ))
    (self-interp : ∀ {τ} → Expr τ → ⟦ τ ⟧) where

    -- Important note: the theorem is only interesting *if decode can be
    -- constructed in the language.*
    --
    -- So the proof depends on `decode` and its components being expressible in
    -- the object language.
    --
    -- And since we prove that there's no Gödel number for `decode`, the proof
    -- is only interesting if we expect to encode the full language. People have
    -- built typed-almost-self-representations where `self-interp` was an
    -- additional primitive, to be able to escape these problems.
    --
    -- In particular, if you can encode the object-language version
    -- `self-typechecker`, and your encoding is "natural" enough, you'll need to
    -- encode the object type of `self-typechecker`, so the *code* for
    -- *object-language Type* must be a member of object-language Type.
    --
    -- Thanks to Tom Jack on the #IRC dependent channel for pointing that out,
    -- and to other participants (in particular mietek and augur) for helpful
    -- discussions.

    -- After running the self-typechecker, we need to compare the type of the
    -- result with ℕ → ℕ. The bit I had missed is that in Agda, normal types
    -- cannot be compared directly, so we need to postulate (a piece of) a
    -- universe construction.
    decode : ℕ → Maybe (ℕ → ℕ)
    decode n with self-typechecker n
    decode n | nothing = nothing
    decode n | just (τ , decoded) with (τ ≟T ′ℕ→ℕ)
    decode n | just (τ , decoded) | no ¬p = nothing
    decode n | just (.′ℕ→ℕ , decoded) | yes refl =
        just (subst (λ x → x) ⟦′ℕ→ℕ⟧≡ℕ→ℕ (self-interp decoded))

    module M = Proof decode

    mainTheorem : ¬ (Σ[ n ∈ ℕ ] (decode n ≡ just M.newFun))
    mainTheorem = M.newFunIsNotDecoded

  {-
  -- For other languages, it's not possible to write a self-typechecker.
  -- However, I conjecture that's not enough. It must be impossible to give a
  -- conservative extension of the language allowing for such a typechecker,
  -- otherwise the theorem still applies.
  --
  -- For instance, suppose we can somehow mutilate a language with a
  -- self-typechecker, so that the self-t.c. is not expressible anymore in the
  -- base language, but the full language is a conservative extension of the
  -- base language. Can the base language have a self-interpreter? No. Since the
  -- full language is a conservative extension, the self-interpreter would still
  -- be a program in the full language (that's a direct consequence of
  -- "conservative extension" - actually, conservative extension is even too
  -- strong for that), and in the full language, with a self-typechecker, you
  -- could apply the theorem. The only thing which is possible is that the
  -- extension breaks some other hypothesis of the theorem - for instance, it
  -- introduces nontermination.

  -- Here's an attempt at the diagonal lemma. But it is apparent that I do not
  -- understand the normal proof in enough detail to actually formalize it. I
  -- can follow most of it and be convinced, but that's misleading, because I
  -- am not sure what's the typing of encoding and decoding.
  --
  -- The correct typing of encoding is probably a corrected version of (M1) in
  -- Lev's draft, that is, a quoting *metafunction* (not necessarily one in the
  -- system):
  --
  -- if T ⊢ t: τ, then ∃ t' . T ⊢ t' : Expr τ.
  --
  -- That's what the first proof of Lӧb's theorem uses, and that might be enough
  -- for the proof below.
  --
  -- TODO: formalize this.

  module StandardDiagonalLemma
         (Expr : Set)

         -- XXX : this is a hack, since this is a HOAS interface which one
         -- certainly can't implement in Agda.
         (abs : (Expr → Expr) → Expr)
         (ap  : Expr → Expr → Expr)
         -- We need a proof that abs and ap are inverses of each other, at least in one direction.
         (hoas-inv : ∀ f → abs (ap f) ≡ f)
         (hoas-inv-b : ∀ f → ap (abs f) ≡ f)

         (decode : ℕ → Maybe Expr)
         (encode : Expr → ℕ)

         (decodeExpr : Expr) -- ℕ → Expr (how?? it's a relation?)
         (encodeExpr : Expr) -- Expr → ℕ

         (decode-encode : ∀ x → decode (encode x) ≡ just x)
         (decodeExpr-encodeExpr : ∀ x → ap decodeExpr (ap encodeExpr x) ≡ x)

         -- The function we construct a fixpoint of:
         -- (B : ℕ → Set) -- Called ψ on the Wikipedia proof.
         -- (ψ : ℕ → Set)
         -- In fact, we only need the quoted version:
         (exprB : Expr)
         (quoteNat : ℕ → Expr)
         where
    -- Based on proof from
    --https://proofwiki.org/wiki/Diagonal_Lemma
    diag : ℕ → ℕ
    diag n with decode n
    diag n | just decodedN = encode (ap decodedN (quoteNat n))
    diag n | nothing = 0

    diagExprBody : Expr → Expr
    diagExprBody = (λ n → ap encodeExpr (ap (ap decodeExpr n) n))
    -- Encode diag (minus pattern matching).
    diagExpr : Expr
    diagExpr = abs diagExprBody --(λ n → ap encodeExpr (ap (ap decodeExpr n) n))

    {-
    lemma-diag-encode : ∀ f → diag (encode f) ≡ encode (ap f (quoteNat (encode f)))
    lemma-diag-encode f rewrite (decode-encode f) = refl
    -}

    {- XXX quoteNat seems to be somehow missing from this statement, see where I expect it to appear: -}
    lemma-diag-encode-expr : ∀ f → ap diagExpr (ap encodeExpr f) ≡ ap encodeExpr (ap f {- (quoteNat XXX -} (ap encodeExpr f))
    lemma-diag-encode-expr f =
      begin
        ap diagExpr (ap encodeExpr f)
      ≡⟨⟩
        ap (abs (λ n → ap encodeExpr (ap (ap decodeExpr n) n))) (ap encodeExpr f)
      ≡⟨ cong (λ □ → □ (ap encodeExpr f))
         (hoas-inv-b diagExprBody) ⟩
        ap encodeExpr (ap (ap decodeExpr (ap encodeExpr f)) (ap encodeExpr f))
      ≡⟨ cong (λ □ → ap encodeExpr (ap □ (ap encodeExpr f)))
         (decodeExpr-encodeExpr f) ⟩
        ap encodeExpr (ap f {- (quoteNat XXX -} (ap encodeExpr f))
      ∎ where
        open ≡-Reasoning

    {- Also, it seems that the above proof would be simpler in Coq, especially
    since we are using no fancy Agda feature. Same for the proofs below. -}

    {-
    -- Typechecks (also below), but that's wrong.
    A = abs (λ x → ap exprB (quoteNat (diag (encode x))))

    -- Original, correct A:
    A x = ∃ y (Diag(x, y) ∧ B(y)) where Diag(x, y) is a formula encoding diag x = y.
    A has type Expr.
    -- So we should use diagExpr instead:
    -}
    A : Expr
    A = abs (λ x → ap exprB (ap diagExpr x)) -- Yes!

    G : Expr
    G = ap A (quoteNat (encode A)) -- Yes!

    -- This is just what G is equivalent to.
    G-equiv : ap diagExpr (quoteNat (encode A)) ≡ G
    G-equiv = {!!}

    -- And this is the statement of the diagonal lemma, though in this context I
    -- expect we can use propositional equality instead of logical equivalence.
    diagonal-lemma : ap exprB (quoteNat (encode G)) ≡ G
    diagonal-lemma = {!!}

  {- First attempt at formalizing the diagonal lemma in our context.
  -- Next step: recheck that the definitions are correct.
  -}
  module DiagonalLemma
         (Expr : ∀ {ℓ} → (Set ℓ) → Set)
         (decode : ℕ → Maybe (Expr (ℕ → ℕ))) (encode : ∀ {ℓ t} → Expr {ℓ} t → ℕ)
         (decode-encode : ∀ (x : Expr (ℕ → ℕ)) → decode (encode x) ≡ just x)
         -- XXX : this is a hack, since this is a HOAS interface which one
         -- certainly can't implement in Agda.
         (abs : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (Expr a → Expr b) → Expr (a → b))
         (ap : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → Expr (a → b) → Expr a → Expr b)
         -- We need a proof that abs and ap are inverses of each other, at least in one direction.
         (hoas-inv : ∀  {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (f : Expr (a → b)) → abs (ap f) ≡ f)
         -- The function we construct a fixpoint of:
         -- (B : ℕ → Set) -- Called ψ on the Wikipedia proof.
         -- (ψ : ℕ → Set)
         -- In fact, we only need the quoted version:
         (exprB : Expr (ℕ → Set))
         (quoteNat : ℕ → Expr ℕ)
         where
    -- Based on proof from
    --https://proofwiki.org/wiki/Diagonal_Lemma
    diag : ℕ → ℕ
    diag n with decode n
    diag n | just decodedN = encode (ap decodedN (quoteNat n))
    diag n | nothing = 0

    foo : ∀ {ℓ} {t : Set ℓ} (x : Expr (ℕ → t)) → ℕ
    foo x = encode (ap x (quoteNat (encode x)))

    --lemma : ∀ {ℓ t} (f : Expr {ℓ} (ℕ → t)) → diag (encode f) ≡ encode (ap f (quoteNat (encode f)))
    lemma : ∀ (f : Expr (ℕ → ℕ)) → diag (encode f) ≡ encode (ap f (quoteNat (encode f)))
    lemma f rewrite (decode-encode f) = refl

    -- A : ℕ → Set
    -- A x = B (diag x)
    A : Expr (ℕ → Set)
    --A = abs (λ x → ap exprB x) -- ARGH! That's just the eta-expansion of G.
    -- XXX Is it sensible to do substitution this way?
    A = abs (λ x → ap exprB (quoteNat (diag (encode x))))
    --A = abs (λ x → ap exprB (quoteNat (encode (ap x (quoteNat (encode x))))))

    -- We can't use the lemma above.
    {-
    lemma-2 : A ≡ abs (λ x → ap exprB (quoteNat (encode (ap x (quoteNat (encode x))))))
    lemma-2 = ?
    -}

    G : Expr Set
    G = ap A (quoteNat (encode A))

    {-
    G-equiv : G ≡ ap exprB (quoteNat (encode exprB))
    G-equiv =
      begin
        G
      ≡⟨⟩
        ap (abs (ap exprB)) (quoteNat (encode (abs (ap exprB))))
      ≡⟨ cong (λ □ → ap □ (quoteNat (encode (abs (ap exprB))))) (hoas-inv exprB) ⟩
        ap exprB (quoteNat (encode (abs (ap exprB))))
      ≡⟨ cong ((λ □ → ap exprB (quoteNat (encode □)))) (hoas-inv exprB) ⟩
        ap exprB (quoteNat (encode exprB))
      ∎
      where
        open ≡-Reasoning
    -}
{-
    -- I'm using the crazy notation from Wikipedia:
    -- http://en.wikipedia.org/wiki/Diagonal_lemma
    -- also because I'm trying to understand their proof.

    genδ : (f : ℕ → ℕ) → ∀ n y → Set
    genδ f n y = y ≡ f n

    {- For now, let's use an identity encoding.
    encode : ∀ {ℓ} {t : Set ℓ} → t → t
    encode x = x -}

    f' : ℕ → Maybe (Expr (ℕ → ℕ)) → ℕ
    f' n (just decodedF) = encode (ap decodedF (quoteNat n))
    f' n nothing         = 0

    f : ℕ → ℕ
    f n = f' n (decode n)

    δ = genδ f

    proof : δ ≡ λ n y → y ≡ f' n (decode n)
    proof = refl

    β : ℕ → Set
    β z = ∀ y → δ z y → ψ y

    --lemma₁ : (φ : Expr (ℕ → Set)) → Set
    --lemma₁ = {! λ φ → β (encode {t = ℕ → Set} φ) !}
    β-lemma₁ : ∀ φ → β (encode {t = ℕ → Set} φ) ≡ ((y : ℕ) → (y ≡ f' (encode {t = ℕ → Set} φ) (decode (encode φ))) → ψ y)
    β-lemma₁ φ = refl

    {-
    β-lemma₂ : ∀ φ → ((y : ℕ) → (y ≡ f' (encode {t = ℕ → Set} φ) (decode (encode φ))) → ψ y) ≡ ((y : ℕ) → (y ≡ f' (encode {t = ℕ → Set} φ) (just {!!})) → ψ y)
    β-lemma₂ = {!!}
    -}

    postulate
      encβ : ℕ

    -- Aah, now I do need an interesting encode, to write β (encode β). But
    -- that's a form of reification, isn't it? Isn't that too hard?
    φ = β encβ -- We need to encode β somehow.
-}

{-
  module DiagonalLemma2
         (Expr : ∀ {ℓ} → (Set ℓ) → Set)
         (decode : ℕ → Maybe (ℕ → ℕ))
         (encode : ∀ {ℓ t} → Expr {ℓ} t → ℕ)
         where
-- = encode ((decode n) n)
-}
-}
