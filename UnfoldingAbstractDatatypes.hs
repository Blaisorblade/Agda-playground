{-# LANGUAGE DeriveFunctor, ExistentialQuantification #-}
data Maybe2 a b = Nothing2 | Just2 a b deriving Functor

--data Functor f => ADT f = forall s. D (s -> f s) s
data ADT f = forall s. D (s -> f s) s

data Tree f = T { unt :: f (Tree f) }

tree :: Functor f => ADT f -> Tree f
tree (D h s) = unfold h s

unfold :: Functor f => (a -> f a) -> a -> Tree f
unfold f x = T (fmap (unfold f) (f x))

