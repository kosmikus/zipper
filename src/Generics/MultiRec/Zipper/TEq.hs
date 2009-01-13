{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Zipper.TEq
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level equality. This is an internal module used by the
-- zipper. The zipper cannot currently use GADTs combined with
-- data families because GHC does not yet support this combination.
--
-----------------------------------------------------------------------------
module Generics.MultiRec.Zipper.TEq where

infix 4 :=:

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

cast :: a :=: b -> a -> b
cast Refl x = x
