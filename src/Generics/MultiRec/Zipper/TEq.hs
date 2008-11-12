{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Generics.MultiRec.Zipper.TEq where

infix 4 :=:

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

cast :: a :=: b -> a -> b
cast Refl x = x
