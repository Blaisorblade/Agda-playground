-- Logic programming in Idris
--
-- From Idris documentation:
-- http://docs.idris-lang.org/en/v0.9.20/tutorial/miscellany.html
--
--     The auto annotation on the implicit argument means
--     that Idris will attempt to fill in the implicit
--     argument by searching for a value of the appropriate
--     type. It will try... the constructors of the required
--     type. If they have arguments, it will search recursively
--     up to a maximum depth of 100.
--
-- based on:
-- Learn Prolog Now!
-- by Patrick Blackburn, Johan Bos, Kristina Striegnitz
-- http://www.learnprolognow.org/
--
-- Typechecked with Idris 0.9.20.

module Prolog
%default total

-- Anthropomorphic silliness

data Name : Type where
  Mia       : Name
  Jody      : Name
  Yolanda   : Name
  Vincent   : Name
  Butch     : Name
  Marsellus : Name
  Pumpkin   : Name

data Woman : Name -> Type where
  WomanMia : Woman Mia
  WomanJody : Woman Jody
  WomanYolanda : Woman Yolanda

verify1 : (P : a -> Type) -> (x : a) -> {auto p : P x} -> P x
verify1 P x {p = p} = p

query1 : (P : a -> Type) -> (x : a) ->
         --
         {auto p : Either (P x) Unit} ->
         Bool
query1 P x {p = Left _} = True
query1 P x {p = Right ()} = False

search2 : (P : a -> Type) ->
          {auto x : a} ->
          {auto p: P x} ->
          a
search2 P {x = x} = x


search3 : (P : a -> Type) ->
          {auto x : a} ->
          {p: P x} ->
          a
search3 P {x = x} = x

searchBoth : (P1 : a -> Type) -> (P2 : a -> Type) -> {x : a} -> {auto p1 : P1 x} -> {auto p2 : P2 x} -> a
searchBoth _ _ {x = x} = x

mutual
  data PlaysAirGuitar : Name -> Type where
    GuitarJody : PlaysAirGuitar Jody

    -- mia and yolanda play air guitar only if they listen to music
    GuitarMia : Listens2Music Mia -> PlaysAirGuitar Mia
    GuitarYolanda : Listens2Music Yolanda -> PlaysAirGuitar Yolanda

    -- sad vincent doesn't play air guitar
    GuitarVincent : Listens2Music Vincent -> Happy Vincent -> PlaysAirGuitar Vincent

    GuitarButch1 : Happy Butch -> PlaysAirGuitar Butch
    GuitarButch2 : Listens2Music Butch -> PlaysAirGuitar Butch

  data Listens2Music : Name -> Type where
    MusicMia : Listens2Music Mia
    MusicButch : Listens2Music Butch

    -- conditional: yolanda listens to music only if she's happy
    MusicYolanda : Happy Yolanda -> Listens2Music Yolanda

  data Happy : Name -> Type where
    HappyYolanda : Happy Yolanda
    HappyVincent : Happy Vincent

data Tatooed : Name -> Type where

data Loves : Name -> Name -> Type where
  VincentLovesMia : Loves Vincent Mia
  MarsellusLovesMia : Loves Marsellus Mia

  MarcellusLovesVincent : Loves Marsellus Vincent
  MiaLovesPumpkin : Loves Mia Pumpkin

-- instance parameter does the querying
-- answer is "yes" if and only if resulting expression is well-typed
verify : (P : a -> Type) -> (x : a) -> {auto ans : P x} -> P x
verify _ _ {ans} = ans

-- querying with negation-as-failure
query : (P : a -> Type) -> (x : a) -> {auto ans : Either (P x) Unit} -> Bool
query _ _ {ans} =
  case ans of
    Left ans => True
    Right () => False

womanMia : Bool
womanMia = query Woman Mia

womanVincent : Bool
womanVincent = query Woman Vincent

tatooedJody : Bool
tatooedJody = query Tatooed Jody

-- mia plays air guitar because she listens to music
guitarMia : PlaysAirGuitar Mia
guitarMia = verify PlaysAirGuitar Mia

-- yolanda plays air guitar because she listens to music,
-- which happens because she is happy
guitarYolanda : PlaysAirGuitar Yolanda
guitarYolanda = verify PlaysAirGuitar Yolanda

-- vincent isn't playing air guitar because he isn't listening to music
-- (unfortunately, error message isn't too informative.)
--
-- guitarVincent : PlaysAirGuitar Vincent
-- guitarVincent = verify PlaysAirGuitar Vincent

-- butch plays air guitar because he's listening to music,
-- not because he's happy
guitarButch : PlaysAirGuitar Butch
guitarButch = verify PlaysAirGuitar Butch

-- search for an object satisfying a predicate
search1 : (P : a -> Type) -> {auto ans : P x} -> a
search1 P {x = x} = x

-- who is a random woman?
-- only returns first result.
woman : Name
woman = search1 Woman

-- who is the female beloved of marsellus?
mfb : Name
mfb = search1 (\x => (Loves Marsellus x, Woman x))

-- who is the happy beloved of marsellus?
-- (does not work. Idris 0.9.20 doesn't do enough backtracking.)
mhb : Name
-- mhb = search1 (\x => (Loves Marsellus x, Happy x))
mhb = search1 (\x => (Loves Marsellus x, Happy x)) {x = Vincent}

-- x is jealous of y if they both love z
data Jealous : Name -> Name -> Type where
  Jelly : Loves x z -> Loves y z -> Jealous x y

-- Marsellus is jealous of Vincent because they both love Mia.
mj : Name
mj = search1 (Jealous Marsellus)

mjReason : Jealous Marsellus Vincent
mjReason = verify (Jealous Marsellus) Vincent

-- Vincent is jealous of Vincent because both Vincent and Vincent love Mia... wait...
vj : Name
vj = search1 (Jealous Vincent)

vjReason : Jealous Vincent Vincent
vjReason = verify (Jealous Vincent) Vincent
