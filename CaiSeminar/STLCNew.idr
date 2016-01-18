module STLCNew
import Prolog

%default total

data Term : Type where
  Var : Nat -> Term
  Val : a -> Term
  App : Term -> Term -> Term
  Abs : TTName -> Term -> Term
  -- Argument type
  (#) : Type -> Term -> Term
  -- \x => Nat # x
  -- \x : Nat => x

infix 0 #

{-
TTName is a builtin type of the reflection interface, is part of the syntax
overloading interface, and is just an annotation (for pretty-printing) with the
name of the variable used by the user.
-}

dsl lc
  lambda = Abs
  variable = Var
  index_first = 0
  index_next = succ

uid : Term
uid = lc (\x => x)

uconst : Term
uconst = lc (\x, y => x)

pure : Term -> Term
pure = id

(<*>) : Term -> Term -> Term
(<*>) = App

uapp : Term
uapp = lc (\f, x => [| f x |])

uapp1 : Term
uapp1 = lc (\f, x, y => [| f x y |])

s : Term
s = lc (\x, y, z => [|x z [|y z|]|])

Context : Type
Context = List Type

-- Typing judgement
data Jdg : Context -> Term -> Type -> Type where
  Ax : Jdg ctx (Val {a = a} v) a

  -- Start rule, for variables
  St : Jdg (a :: c) (Var 0) a
  -- Weakening, as a constructor, restricted to variables
  Wk : Jdg c (Var n) a -> Jdg (b :: c) (Var (S n)) a

  Ap : Jdg c s (a -> b) ->
       Jdg c t a ->
       Jdg c (App s t) b

  Ab : Jdg (a :: c) t b ->
       Jdg c (Abs x (a # t)) (a -> b)

typecheck : (t : Term) -> {auto j : Jdg [] t a} -> Type
typecheck t {a = a} = a

-- Example for abstraction:
-- typecheck (lc (\x => Nat # x))

data Env : Context -> Type where
  Nil  : Env [] -- [] desugars to Nil
  (::) : a -> Env ctx -> Env (a :: ctx)

evalWithEnv : (t : Term) -> (j : Jdg ctx t a) -> (env : Env ctx) -> a
evalWithEnv (Val v) Ax env = v
evalWithEnv (Var Z) St (v :: env) = v
evalWithEnv (Var (S n)) (Wk j) (_ :: env) = evalWithEnv (Var n) j env
evalWithEnv (App s t) (Ap j k) env = evalWithEnv s j env $ evalWithEnv t k env
evalWithEnv (Abs _ (_ # body)) (Ab bodyProof) env =
  \v => evalWithEnv body bodyProof (v :: env)

eval : (t : Term) -> {auto j : Jdg [] t a} -> a
eval t {j = j} = evalWithEnv t j []

idNat : Term
idNat = lc (\x => Integer # x)

four : Term
four = [| idNat (Val 4) |]

double : Term
double = lc (\x => Integer # [| (Val (+)) x x |])


eight : Term
eight = [| double (Val 4) |]

result : Integer
result = eval eight
