{-# OPTIONS --allow-unsolved-metas #-}
{-
Try formalizing chapter 6 (by Karl Crary) of Pierce's ATTAPL.

This needs a formalization of weakening and substitution.
I've tried using the one from the paper on hereditary substitution, and failed.
-}

module Main where

open import Term
open import Subst2
open import EquivSubst2
