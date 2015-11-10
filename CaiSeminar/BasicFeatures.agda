-- BASIC FEATURES --


-- CONTENTS
--
-- datatypes
-- pattern matching
-- user-defined operators
-- polymorphism and dependent functions
-- types depending on values (parameters and indices)
-- dot patterns
-- absurd patterns
-- with patterns
-- records


-- Every Agda file begins with a module declaration that
-- coincides with its filename.
module BasicFeatures where

-- Modules are loaded by the "import" keyword.
-- Definitions in the module are brought into scope by
-- the "open" keyword. It's possible to do both at the
-- same time.
open import Data.Nat

-- Emacs key combinations:
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.EmacsModeKeyCombinations

-- Frequently used commands:
-- C-c C-l      typecheck
-- C-c C-n      evaluate
-- C-c C-d      what's the type of this expression?
-- C-u C-x =    how to I type this unicode character?
-- M-.          jump to definition
-- C-c C-c      case split
-- C-c C-,      goal type and typing context

-- Modules can nest within each other. Nested modules create
-- nested namespaces.
module Bool where
  -- The scope of the module Bool begins.
  -- Members of a scope are nested deeper than its first
  -- line. Comments do not count.

-- DATATYPES --

  -- Datatypes are declared like GADTs in Haskell.
  data Bool : Set where
    true  : Bool
    false : Bool

-- PATTERN MATCHING --

  not : Bool → Bool
  not true  = false
  not false = true

  -- The scope of the module Bool ends.

module List0 where

  -- Like Haskell, datatypes can have type parameters.
  data List0 (A : Set) : Set where
    nil  : List0 A
    cons : A → List0 A → List0 A

  sum0 : List0 ℕ → ℕ
  sum0 nil = 0
  sum0 (cons x xs) = x + sum0 xs

  xs0 : List0 ℕ
  xs0 = cons 1 (cons 2 (cons 3 (cons 4 nil)))


-- USER-DEFINED OPERATORS --
-- (not in idris)         --

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_
-- It is possible to define arbitrary operators.
-- The underscore _ is the special placeholder
-- for operands.

xs : List ℕ
xs = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

-- POLYMORPHISM AND DEPENDENT FUNCTIONS --

-- in Haskell:
-- id :: a -> a
-- id x = x
id0 : (A : Set) → A → A
id0 A x = x

-- in Haskell:
-- const :: a -> b -> a
-- const x y = x
const0 : (A : Set) → (B : Set) → A → B → A
const0 A B x y = x

-- in Haskell:
-- constId :: b -> a -> a
-- constId = const id
constId0 : (A : Set) → (B : Set) → B → A → A
constId0 A B = const0 (A → A) B (id0 A)

-- in Haskell:
-- length : [a] -> a
length0 : (A : Set) → List A → ℕ
length0 A [] = 0
length0 A (x ∷ xs) = 1 + length0 A xs

-- IMPLICIT PARAMETERS --

-- Parameters surrounded by braces { } are to be inferred
-- by compiler. Those are "implicit" parameters.
-- Make a parameter implicit only if it is a part of the
-- type of an explicit parameter.

id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x y = x

-- ∀ tells Agda to try to infer the type of A.
length : ∀ {A} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

-- TYPES DEPENDING ON VALUES           --
-- PARAMETERS AND INDICES OF DATATYPES --

-- Datatypes may also be declared as a function
-- between types.
--
-- in Idris: data List : Type -> Type where ...
--
-- Exercise: explore the consequence of
-- never using datatype parameters
data List1 : Set → Set₁ where
  [] : ∀ {A} → List1 A
  _∷_ : ∀ {A} → A → List1 A → List1 A

-- does not work:
-- data Vec (A : Set) (n : ℕ) : Set where
--   [] : Vec A 0

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vlength : ∀ {A n} → Vec A n → ℕ
vlength {n = n} xs = n

head : ∀ {A n} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {A n} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

vsum vsum' : ∀ n → Vec ℕ n → ℕ
vsum zero xs = 0
vsum (suc n) xs = head xs + vsum n (tail xs)

-- DOT PATTERNS --

-- One argument restricts the form of another argument.
-- A dot pattern holds an _expression_ determined just
-- by looking at other constructors. Sometimes the
-- expression is not complete; the underscore represents
-- the unknown parts. A dot pattern may not hold any
-- free variable.
vsum' .0 [] = 0
vsum' .(suc _) (x ∷ xs) = x + vsum' _ xs
-- the underscore _ tells Agda to infer the argument.
-- in this case, inference is mandatory.

-- it's possible to make a function unnecessarily difficult to write
-- by case-expanding the wrong argument.
vlength' vlength'' : ∀ {A} n → Vec A n → ℕ
vlength' .0 [] = 0
vlength' .(suc _) (x ∷ xs) = suc 1997
-- replace 1997 by _ to see error message

-- resolve the issue by expanding n before xs.
vlength'' zero [] = 0
vlength'' (suc n) (x ∷ xs) = suc n

-- ABSURD PATTERNS --

data Even : ℕ → Set where
  ezero : Even 0
  esuc  : ∀ {n} → Even n → Even (suc (suc n))

-- () is the absurd pattern. It means that there is
-- no constructor for this argument given the constructor
-- for other arguments.
half half' : (n : ℕ) → Even n → ℕ
half zero e = 0
half (suc zero) () -- one is not an even number
half (suc (suc n)) (esuc e) = suc (half n e)

-- whether we run into absurd patterns or dot patterns
-- depends on the order of case split.
half' .0 ezero = 0
half' ._ (esuc e) = suc (half' _ e)

-- WITH PATTERNS --

data Odd : ℕ → Set where
  oone : Odd 1
  osuc : ∀ {n} → Odd n → Odd (suc (suc n))

data EvenOrOdd (n : ℕ) : Set where
  isEven : Even n → EvenOrOdd n
  isOdd  : Odd  n → EvenOrOdd n

-- There is no case expression in Agda,
-- because the result of one pattern matching
-- affects the form of other arguments.
-- To pattern-match an arbitrary expression,
-- use the "with" keyword. Unchanged arguments
-- can be replaced by the "..." keyword.

evenOrOdd : (n : ℕ) → EvenOrOdd n
evenOrOdd 0 = isEven ezero
evenOrOdd 1 = isOdd oone
evenOrOdd (suc (suc n)) with evenOrOdd n
evenOrOdd (suc (suc n)) | isEven e = isEven (esuc e)
...                     | isOdd  o = isOdd  (osuc o)

-- RECORDS (FOR REFERENCE ONLY) --

-- We won't use records this week.
-- However, records occur frequently in the standard
-- library. It's important to understand their syntax.

-- Record type declaration

open import Data.String

-- This is a record with 3 fields.
-- Records may not be recursive.
record Student : Set where
  constructor
    mkStudent
  field
    name : String
    address : String
    idNumber : ℕ

-- The constructor mkStudent is in global scope.
-- C-c C-d mkStudent results in:
--
-- mkStudent :
--   (name address : String) (idNumber : ℕ) → Student

-- The field accessors name, address, idNumber
-- are inside the namespace Student and not visible
-- in the global scope.
--
-- Student.name : Student → String

-- Records can be defined using the constructor.
student1 student2 : Student
student1 = mkStudent "Max Mustermann" "Musterstraße 1997" 314159

-- Records can be defined using the record keyword.
student2 = record
  { name = "Max Mustermann"
  ; address = "Musterstraße 1997"
  ; idNumber = 314159
  }

-- Record fields can be extracted by pattern matching.
name1 name2 name3 : String
name1 = let mkStudent name _ _ = student1 in name

-- Record fields can be extracted by field names.
name2 = Student.name student1

-- Record extractors are brought into scope by "opening"
-- the record.
name3 = name student1
  where
  open Student

-- Records may be recursive. Here's the syntax.
-- actually using them the are more complicated.
record Stream (A : Set) : Set where
  coinductive -- streams may be infinite
  constructor _∷_
  field
    shead : A
    stail : Stream A

open import Data.Maybe

record NonemptyList (A : Set) : Set where
  inductive -- nonempty lists should be finite
  field
    lhead : A
    ltail : Maybe (NonemptyList A)
