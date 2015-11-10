module 02hw where

-- Homework: basic features --

open import Data.Nat
open import Data.Bool

-- We will use lists and vectors in the standard library,
-- instead of the homemade versions in the script.
open import Data.List
open import Data.Vec

-- We will use the even/odd data structures in this homework.
-- Typecheck this file in the folder containing the script
-- `BasicFeatures.agda`.
open import BasicFeatures using
  ( Even ; ezero ; esuc ; half
  ; Odd ; oone ; osuc
  ; EvenOrOdd ; isEven ; isOdd ; evenOrOdd
  )

-- Problem 1: Sorting.
-- Write a series of functions that help to sort a list
-- of natural numbers.

-- Problem 1.1:
-- Given 2 natural numbers x, y, decide whether x ≤ y.
leNat : ℕ → ℕ → Bool
leNat zero y = true
leNat (suc x) zero = false
leNat (suc x) (suc y) = leNat x y

-- Problem 1.2:
-- Given a number y and a list xs, insert y into xs before
-- the first number in xs bigger than or equal to y.
insert : ℕ → List ℕ → List ℕ
insert y [] = y ∷ []
insert y (x ∷ xs) with leNat y x
... | true = y ∷ x ∷ xs
... | false = x ∷ insert y xs

-- Problem 1.3:
-- Implement insertion sort.
-- (Optional: implement a sorting algorithm that is not
-- insertion sort.)
sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

-- Problem 2: Hailstorm numbers (oeis.org/A006577)
-- Compute the next natural number in the 3x+1 problem:
-- If x is even, divide x by 2.
-- If x is odd, the result is 3x+1.
-- (Optional: write a function `hailstorm` such that
-- `hailstorm i` is the ith number in A006577. You may
-- need to disable the termination checker.)
open import Data.Nat.DivMod
nextHail : ℕ → ℕ
nextHail n with evenOrOdd n
nextHail n | isEven x = n div 2
nextHail n | isOdd x = suc (3 * n)

-- Problem 3: Matrix transposition.
-- Write a series of functions leading up to matrix
-- transposition.

-- Matrices are represented as a sequence of rows.
Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vec (Vec A n) m

-- Problem 3.1:
-- Define a polymorphic function mapVec that applies
-- a function on all elements of a vector.
--
-- mapVec suc (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) =
--   (2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
--
mapVec : ∀ {A B : Set} {n} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

-- Problem 3.2:
-- Fill a size-n vector with x.
fill : ∀ {A : Set} → (n : ℕ) → A → Vec A n
fill zero x = []
fill (suc n) x = x ∷ fill n x

-- Problem 3.3:
-- Given a vector of functions and vector of arguments,
-- compute the vector of results.
pointwiseApp : ∀ {A B : Set} {n} → Vec (A → B) n → Vec A n → Vec B n
pointwiseApp [] [] = []
pointwiseApp (f ∷ fs) (x ∷ xs) = f x ∷ pointwiseApp fs xs

-- Problem 3.4:
-- Implement matrix transposition.
--
-- Hints:
--
-- 1. The transpose of a 0-by-2 matrix is a 2-by-0 matrix.
--    In our representation, 2-by-2 matrices and 2-by-0
--    matrices are different.
--
-- 2. The easiest way to define matrix transposition is
--    obtained by thinking about how the transpose of a
--    matrix is obtained from the transpose of its submatrix
--    without the first row.
--
-- (Optional: Implement matrix transposition in a different
-- way, e. g., through the function obtaining the ith column
--
--   getColumn : ∀ {A m n} → Fin n → Matrix A m n → Vec A m
--
-- You may need to read the library Data.Fin.

-- Matrix transposition turns m-by-n matrices into
-- n-by-m matrices. Rows become columns and columns
-- become rows. Here is its signature; we will implement
-- it later.
transpose : ∀ {A m n} → Matrix A m n → Matrix A n m
transpose [] = fill _ []
transpose (xs ∷ xss) = pointwiseApp (mapVec _∷_ xs) (transpose xss)

open import Data.Fin
open import Function
getColumn : ∀ {A m n} → Fin n → Matrix A m n → Vec A m
getColumn k [] = []
getColumn k (xs ∷ xss) = (lookup k xs) ∷ (getColumn k xss)

fillN : ∀ {A : Set} → (n : ℕ) → (f : (Fin n) → A) → Vec A n
fillN zero f = []
fillN (suc n) f = f (fromℕ n) ∷ fillN n (f ∘ inject₁)

transpose2 : ∀ {A m n} → Matrix A m n → Matrix A n m
transpose2 {n = n} xss = fillN n $ flip getColumn xss
