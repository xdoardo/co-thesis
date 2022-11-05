{-# LANGUAGE GADTs #-}

module Monad.Delay (Delay(Now, Later), force) where

data Delay a = Now a | Later (Delay a) deriving( Show )

-- Strong bisimilarity
instance Eq a =>  Eq (Delay a) where 
  d1 == d2 = case (d1, d2) of
    (Now x, Now y) -> x == y
    (Later _, Now _) -> False
    (Now _, Later _)  -> False
    (Later x, Later y)  -> x == y

force :: Delay a -> a
force d = case d of Now x -> x
                    Later x -> force x

instance Functor Delay where
  fmap f d = case d of Now x -> Now (f x)
                       Later x -> fmap f x

instance Applicative Delay where
  pure = Now
  Now f   <*> Now x   = Now (f x)
  Later f <*> Now x   = Later (f <*> Now x)
  Now f   <*> Later x = Later (Now f <*> x)
  Later f <*> Later x = Later (f <*> x)


instance Monad Delay where
  d >>= f = case d of Now x -> f x
                      Later x -> f (force x)
