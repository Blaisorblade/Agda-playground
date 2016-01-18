-- Typechecking for simply typed lambda calculus
-- as an inductive relation, sugared with syntax
-- overloading described in:
--
-- Brady and Hammond.
-- Resource-safe systems programming with
-- embedded domain-specific languages.
--
-- Typechecked with Idris 0.9.20.

module STLC
import Prolog
%default total

-- lambda terms with type annotations
data Term : Type where
  Val : a -> Term
  App : Term -> Term -> Term

  Var : Nat -> Term

  -- TTName is reflected variable name
  Abs : TTName -> Term -> Term

  -- argument type annotation
  (#) : Type -> Term -> Term

infix 0 #

dsl lc
  lambda      = Abs
  variable    = Var
  index_first = 0
  index_next  = succ

uid : Term
uid = lc (\x => x)

ufst : Term
ufst = lc (\x, y => x)

ufive : Term
ufive = Val 5

-- embedding applications by "idiom brackets":
-- [| f a b c |]  is desugared into
-- pure f <*> a <*> b <*> c

pure : Term -> Term
pure = id

(<*>) : Term -> Term -> Term
f <*> x = App f x

omega : Term
omega = lc [| (\x => [|x x|]) (\x => [|x x|]) |]

-- reuse Idris types for embedded STLC
Context : Type
Context = List Type

-- typing judgement:
-- Jdg g t a   means   g ⊢ t : a
data Jdg : Context -> Term -> Type -> Type where
  Ax : Jdg g (Val {a = a} v) a
  St : Jdg (a :: g) (Var 0) a

  -- only do weakening on variables
  -- to make rules syntax directed
  Wk : Jdg g (Var n) a -> Jdg (b :: g) (Var (S n)) a

  Ab : Jdg (a :: g) t b -> Jdg g (Abs x (a # t)) (a -> b)
  Ap : Jdg g s (a -> b) -> Jdg g t a -> Jdg g (App s t) b

idNat : Term
idNat = lc (\x => Nat # x)

-- given a context and a term, what is the type?
typecheck : {default [] g : Context} ->
            (t : Term) ->
            {auto j : Jdg g t a} -> Type
typecheck t {a = a} = a


eight : Term
eight = Val (+) <*> Val 3 <*> Val 5

-- well-typed STLC programs don't go wrong
-- (assuming well-typed Idris programs don't go wrong)
-- (show eval first)
data Env : List Type -> Type where
  Nil : Env [] -- [] is sugar for Nil
  (::) : a -> Env g -> Env (a :: g)

evalWithEnv : (t : Term) -> Jdg g t a -> Env g -> a
evalWithEnv (Val v) Ax env = v
evalWithEnv (Var Z) St (v :: env) = v

evalWithEnv (Var (S n)) (Wk j) (u :: env) =
  evalWithEnv (Var n) j env

evalWithEnv (Abs x (a # t)) (Ab j) env =
  \v => evalWithEnv t j (v :: env)

evalWithEnv (App s t) (Ap j k) env =
  evalWithEnv s j env $ evalWithEnv t k env

eval : (t : Term) -> {auto j : Jdg [] t a} -> a
eval t {j = j} = evalWithEnv t j []

-- The datatype Term doesn't put enough constraints.
-- Constants must be type-annotated.
foldr' : Term
foldr' = Val {a = (Integer -> Integer -> Integer) ->
                  Integer -> List Integer -> Integer}
             foldr

program : Term
program =
  lc [| (\x => Integer # [| (Val (+)) x (Val 5) |])
     [| foldr' (Val (*)) (Val 1)
               (Val {a = List Integer} [1,2,3,4,5]) |] |]

-- typechecks.
test2 : Integer
test2 = eval program

-- does not typecheck. why?
--
-- test : eval program = 125
-- test = Refl
