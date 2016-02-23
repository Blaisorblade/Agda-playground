{- Sketch syntax of AltArtemov reflective lambda calculus λ∞.

DISCLAIMER: VERY incomplete, no warranty.
Acknowledgments to the guys who explained me this stuff omitted.

Current main goal: sketch a bit how to stratify terms and types correctly, by showing
the level annotations needed for Term, Type and Var.

However, the handling of contexts might be rather heavily broken -- for that,
I'd need to think more; here I'm just adapting code I have around for STLC.
(Actual contexts might be encodable in this syntax, but it does not seem a good
idea).

Note: before studying declarations here, you might want to check how I do the
same things for STLC in this formalization:
https://github.com/Blaisorblade/Agda/blob/master/CaiSeminar/TypedDeBrujin.agda

==
Notation for typing: I (try to) reserve : for Agda's typing, and use -:- for λ∞
typing. I'm using σ and τ for object-level types.
==

Yes, that's ugly, but IMHO better than, say ∶ (unless I'm sure all of you have a
font where the difference is clearly visible), or ∷ (where I need to trust
Agda's overload resolution).
 -}

-- Typechecked with Agda 2.4.0.2. I tried not to be *too* fancy, so hopefully
-- works with later versions.
module AltArtemov where

open import Data.Nat
open import Data.List hiding (drop)
open import Data.List.All renaming (All to HList)

-- Type and Term are mutually recursive, so use Agda forward declaration.

-- If τ : Type n, then if x -:- τ, x lives at level (suc n).

-- Types themselves always live at level 0; however,
-- to represent xn -:- xn-1 -:- ... -:- x2 -:- x1 -:- τ,
-- I want τ to be at level 0, x1 at level 1, and x1 -:- τ also at level 1,
-- so x2 and x2 -:- (x1 -:- τ) should be at level 2, and so on.
data Type : ℕ → Set

-- That's not really the kind of contexts we want. One should start from
-- contexts for dependent type theories, not from STLC as I did.

-- Well, in fact their formalization is even less standard weirder. Their
-- contexts contain type assertions t : F where t must be a variable. I'm not
-- even remotely trying to get *that* right.

-- Shapes of context, marking the level of each variable.
TContext : Set
TContext = List ℕ

-- List of types, indexed by contexts.
-- I imagine each type should be in scope of the previous types.
-- And using a HList (rather than a list of lists) doesn't allow enforcing structures like
-- x1 -:- x2 -:- x3 -:- ... xn -:- τ; we'd have to flatten that to
-- xn -:- T, xn-1 -:- (xn -:- τ), and so on.
Context : TContext → Set
Context = HList Type

-- If τ : Type n, then t : Term Δ Γ (suc n) τ is a term of type τ, at level (suc
-- n), in typing context Γ (where levels for Γ are described by Δ).

-- If τ has level n and t -:- τ, t has level (suc n).
-- I'm not sure how to express that, so I just say that if t has level n and t
-- -:- τ, then τ has level (pred n).
-- This applies both to terms and to variables.
data Term : (Δ : TContext) → Context Δ → (n : ℕ) → Type (pred n) → Set

-- To avoid calling (pred 0) (which is 0), all constructs of Term should have level (suc n) (for some n).
-- To enforce that, I always call Term′ and Var′ in the datatype declaration for Term and Var.
Term′ : (Δ : TContext) → Context Δ → (n : ℕ) → Type n → Set
Term′ Δ Γ n τ = Term Δ Γ (suc n) τ

-- So if I write t : Term′ Δ Γ n τ, τ lives at level n, but t lives at level (suc n).
-- Declare variables. Parameters are like

-- The basic technique (as for my STLC formalization) is typed de Brujin indexes.
-- `this` is the leftmost variable in the context,
-- `that this` the second, and so on. You can read values as natural numbers,
-- but they carry more information -- a Var Δ Γ τ is both a variable and a proof
-- that it is valid in the given context.
data Var : (Δ : TContext) → Context Δ → (n : ℕ) → Type (pred n) → Set
Var′ : (Δ : TContext) → Context Δ → (n : ℕ) → Type n → Set
Var′ Δ Γ n τ = Var Δ Γ (suc n) τ

data Var where
  this : ∀ {n Δ Γ τ} → Var′ (n ∷ Δ) (τ ∷ Γ) n τ
  that : ∀ {n m Δ Γ σ τ} → Var′ Δ Γ n τ → Var′ (m ∷ Δ) (σ ∷ Γ) n τ

------------------------------------------------------
------------------------------------------------------

-- Actually define types.
infixr 6 _⇒_
data Type where
  -- Silly base type.
  Nat : Type 0
  _⇒_ : ∀ {n} → (σ : Type n) → (τ : Type n) → Type n
  _/\_ : ∀ {n} → Type n → Type n → Type n
  -- This takes the arguments in the opposite of the order we'd want.
  typed : ∀ {n Δ Γ} → (τ : Type n) → Term Δ Γ (suc n) τ → Type (suc n)

-- Declare sugar in the right order.
-- I considered using ∶, that is \:, but I don't trust your font.
-- XXX I can't declare this as right-associative ?!?
syntax typed τ t = t -:- τ

-- Actually define λ∞ terms.
--
-- Note that a value of type Term encodes a complete Agda-level derivation of
-- λ∞. If this is confusing, note I do the same for STLC. This makes sense for
-- syntax-directed judgements - there's an inference rule (a constructor of the
-- metalevel type of typing derivations) per constructor, so term constructors
-- double as inference rules take the premise of their typing rule as arguments.
data Term where
  -- Usual lambda calculus terms. Nothing going on with levels.
  var : ∀ {n Δ Γ τ} → Var′ Δ Γ n τ → Term′ Δ Γ n τ
  app : ∀ {n Δ Γ σ τ} → Term′ Δ Γ n (σ ⇒ τ) → Term′ Δ Γ n σ → Term′ Δ Γ n τ
  lam : ∀ {n Δ Γ σ τ} → Term′ (n ∷ Δ) (σ ∷ Γ) n τ → Term′ Δ Γ n (σ ⇒ τ)

  -- Silly base term for integer literals.
  lit : ∀ {Δ Γ} → (v : ℕ) → Term′ Δ Γ 0 Nat

  -- The confusing term constructors. Note they are just term constructors,
  -- moving stuff across levels, not much more.

  -- Here, I encode the premise t -:- u -:- A as u -: A and t -:- u. I didn't try making t itself a vector.
  -- Since u is implicit, you can use this constructor via ⇓ t, and this will be a Term of type τ:
  ⇓ : ∀ {n Δ Γ} {τ : Type n}
      {u : Term′ Δ Γ n τ} →
      -- t -:- (u -:- τ)
      (t : Term′ Δ Γ (suc n) (u -:- τ)) →
      ----------------------------------------------------------
      -- ⇓ t -:- τ
      Term′ Δ Γ n τ

  -- We can only use this constructor for !u, and we get:
  -- !u -:- (u -:- τ)
  -- However, that should actually only be used through the ⇑ rule (see below).
  --
  -- If you want, this is only intended to be a formation rule for terms, not an
  -- introduction rule, but with this construction technique there's no way to
  -- distinguish them.
  ! : ∀ {n Δ Γ} {τ : Type n}
      (u : Term′ Δ Γ n τ) →
      -----------------------------
      (Term′ Δ Γ (suc n) (u -:- τ))

  ⇑ : ∀ {n Δ Γ} {τ : Type n}
      {u : Term′ Δ Γ n τ} →
      -- t -:- (u -:- τ)
      (t : Term′ Δ Γ (suc n) (u -:- τ)) →
      ----------------------------------------------------------
      -- ⇑ t -:- (u -:- τ)
      Term′ Δ Γ (suc (suc n)) ((! u) -:- (u -:- τ))

-- Recommended exercise (that I didn't do): try encoding in the above syntax
-- some examples.

-- Just an identity function:
ex0 : ∀ {n} {τ : Type n} → Term′ [] [] n (τ ⇒ τ)
ex0 = lam (var this)
