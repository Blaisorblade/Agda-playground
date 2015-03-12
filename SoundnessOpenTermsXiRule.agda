-- Here I relate problem with unrealizable contexts in μDOT with known problems
-- in dependent type theory. I use Agda for illustration.
--
-- I also discuss the viewpoint given by denotational semantics.

module SoundnessOpenTermsXiRule where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool

-- The so called ξ-rule (xi-rule) allows reducing open terms during
-- normalization.
--
-- This is also called reducing *under binders*. In this gist, we explain why
-- this is tricky. I took the example from
-- http://dl.acm.org/citation.cfm?id=2500575, though the concept is much older.
--
-- In a call-by-value lambda-calculus, we only reduce a term when all its free
-- variables are mapped to values by an environment.
--
-- However, if we reduce under binders, we might reduce open terms which would
-- never be reduced in a usual semantics. For instance, we might reduce
-- functions bodies which cannot be called! Hence, ensuring we get no type
-- errors can become harder.
--
-- One common case is when a free variable has a type without inhabitants.
-- Below, we see an example in absurdTerm, taking an argument of type ℕ ≡ Bool.
--
-- If a system has some form of dependent typing, this can be a problem for
-- different reasons (ultimately, because types can depend on values). Examples
-- below.

cast : ∀ {a b : Set} → a ≡ b → a → b

-- Suppose this definition was accepted (it is not):
{-
cast eq x = x
-}
-- This means that cast simply returns its second argument, of type a, as the
-- return value (of type b). This seems safe because we also got a proof that a
-- ≡ b. Or did we?

-- Observe this term:
absurdTerm = λ (prf : ℕ ≡ Bool) → cast prf 3 ∨ false

-- How do we reduce the open term `cast prf 3` to a value of type Bool? We
-- shouldn't! Not only is prf not known, it will never have a value! Instead,
-- `cast prf 3` should not reduce. To ensure that, we can pattern match on the
-- first argument:

cast refl x = x

{-

This version of cast will only reduce when the first argument is known, avoiding
the hypotethical problem with absurdTerm. As a consequence, Agda only accepts
this definition of cast, not the previous one.

You can check that `absurdTerm` will indeed not reduce and is in normal form:
Normalizing it (with C-c C-n) reveals it normalizes to `λ prf → cast prf 3 ∨
false`.

==

Now, I believe what we learn from "Foundations of Path-Dependent Types" (OOPSLA
2014) is that Scala faces a similar difficulty: we have problems when we have a
type which later turns out to be unrealizable. The paper does talk about
"lattice collapse", but I either don't get or don't like this concept as
presented.

In particular, I don't think the problem should be either with subtyping
transitivity or environment narrowing, because "semantically" (in a denotational
semantics) they must both be true.

Below I recover a different presentation.

If we give a semantics (a "model theory") for all judgements (the "proof
theory") and then require the proof theory to be sound, you automatically get
both subtyping transitivity and environment narrowing. Note that this approach
assumes a simple denotational semantics; we can luckily ignore all sorts of side
effects and nontermination.

The paper says:

> "If we have an Animal, and later find out it is a Cow, this should not
invalidate any findings we made about the Animal – that is anything we prove
assuming `a: Animal` should still hold assuming `a: Cow`."

This just implies that we need be careful deducing stuff given `a: Animal` to
keep the theory sound. Above, we forbid reducing `cast prf` unless `prf` is
realized. Here, we forbid "reducing" type selections such as `a.T`: we can't
learn that `L <: a.T` or `a.T <: U`, unless we can guarantee this is going to be
true.

IOW, we should (try to) restrict <:-TSEL and TSEL-<:.

However, I did not specify the model theory - what does subtyping mean? It seems
in fact possible to accomodate semantically a "lattice collapse".

Let's first restrict to S <: T with S and T closed.

The most obvious definition of semantic subtyping (which I'll write as <:s) is
that S <:s T if at runtime, every value of type S has also type T. For this to
make more sense, we better assume a semantics without any type erasure - also
type members should be kept.

I've ignored the context, so the above is restricted to the case that S and T
are closed and the context is empty.

Let's take contexts into account. Then we can give a semantics, mapping an
object judgement to a proposition in the metalevel logic:

  ⟦ Γ ⊢ S <: T ⟧ = ∀ (ρ : ⟦ Γ ⟧). ⟦ S ⟧ ρ <:s ⟦ T ⟧ ρ.

(I'm assuming semantics from from types to semantic domains (sets, CPOs, what
you prefer... we don't model nontermination) and from contexts to types of
environments (products of semantic domains), and overloading semantic brackets
on them).

Note that the ∀ might well be vacuously true because there's no environment for
the context. In such a context, arbitrary propositions can be true: this seems a
semantically nicer concept of "lattice collapse", because we don't conclude that
⊤ <: ⊥, only that ∀ x ∈ ∅. ⟦⊤⟧ <:s ⟦⊥⟧.

It becomes important, then, that we reject strengthening, that is dropping
unused variables from the context: here this is unsound, unless we know the type
is non-empty. (The same applies to dependent types). While the formalism does
not have a strenghtening rule, the paper writes often S <: T without a context,
which can be misleading without strengthening.

Semantic subtyping probably parallels "dynamic subtyping", and my requirement
for soundness with respect to it probably parallels the fact that static
subtyping implies dynamic subtyping, as explained in this quote from the paper:

> In such a setting, we mechanically proved that the calculus is type-safe as long
as the static strict semantics imply the dynamic lenient semantics.

But to me it's not clear yet, semantically, why dynamic subtyping gives up
nominality.

-}
