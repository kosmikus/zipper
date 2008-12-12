{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Zipper
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
--
-- The generic zipper.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Zipper
  (-- * Locations
   Loc(),
   -- * Context frames
   Ctx(),
   -- * Generic zipper class
   Zipper(..),
   -- * Interface
   enter, down, down', up, right, left, leave, on, update, foldZipper
  ) where

import Prelude hiding (last)

import Control.Monad
import Data.Maybe

import Generics.MultiRec.Base
import Generics.MultiRec.Fold
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Zipper.TEq

-- * Locations and context stacks

-- | Abstract type of locations. A location contains the current focus
-- and its context. A location is parameterized over the system of
-- datatypes and over the type of the complete value.

data Loc :: (* -> *) -> (* -> *) -> * -> * where
  Loc :: (Ix s ix, Zipper (PF s)) => r ix -> Ctxs s r a ix -> Loc s r a

data Ctxs :: (* -> *) -> (* -> *) -> * -> * -> * where
  Empty :: Ctxs s r a a
  Push  :: Ix s ix => Ctx (PF s) s r ix b -> Ctxs s r a ix -> Ctxs s r a b

-- * Context frames

-- | Abstract type of context frames. Not required for the high-level
-- navigation functions.

data family Ctx f :: (* -> *) -> (* -> *) -> * -> * -> *

data instance Ctx (K a) s r ix b
data instance Ctx (f :+: g) s r ix b  = CL (Ctx f s r ix b)
                                      | CR (Ctx g s r ix b)
data instance Ctx (f :*: g) s r ix b  = C1 (Ctx f s r ix b) (g s r ix)
                                      | C2 (f s r ix) (Ctx g s r ix b)

-- The equality constraints simulate GADTs. GHC currently
-- does not allow us to use GADTs as data family instances.

data instance Ctx (I xi) s r ix b     = CId (b :=: xi)
data instance Ctx (f :>: xi) s r ix b = CTag (ix :=: xi) (Ctx f s r ix b)
data instance Ctx (C c f) s r ix b    = CC (Ctx f s r ix b)

-- * Generic navigation functions

-- | It is in general not necessary to use the generic navigation
-- functions directly. The functions listed in the ``Interface'' section
-- below are more user-friendly.
--

class HFunctor f => Zipper f where
  cmap        :: (forall b. Ix s b => s b -> r b -> r' b) ->
                 Ctx f s r ix b -> Ctx f s r' ix b
  fill        :: Ix s b => Ctx f s r ix b -> r b -> f s r ix
  first, last :: (forall b. Ix s b => r b -> Ctx f s r ix b -> a)
              -> f s r ix -> Maybe a
  next, prev  :: (forall b. Ix s b => r b -> Ctx f s r ix b -> a)
              -> Ix s b => Ctx f s r ix b -> r b -> Maybe a

instance Zipper (I xi) where
  cmap  f (CId prf)   = CId prf
  fill    (CId prf) x = castId prf I x
  first f (I x)  = return (f x (CId Refl))
  last  f (I x)  = return (f x (CId Refl))
  next  f (CId prf) x = Nothing 
  prev  f (CId prf) x = Nothing 

instance Zipper (K a) where
  cmap  f void   = impossible void
  fill    void x = impossible void
  first f (K a)  = Nothing
  last  f (K a)  = Nothing
  next  f void x = impossible void
  prev  f void x = impossible void

instance (Zipper f, Zipper g) => Zipper (f :+: g) where
  cmap  f (CL c)   = CL (cmap f c)
  cmap  f (CR c)   = CR (cmap f c)
  fill    (CL c) x = L (fill c x)
  fill    (CR c) y = R (fill c y)
  first f (L x)    = first (\z -> f z . CL) x
  first f (R y)    = first (\z -> f z . CR) y
  last  f (L x)    = last  (\z -> f z . CL) x
  last  f (R y)    = last  (\z -> f z . CR) y
  next  f (CL c) x = next  (\z -> f z . CL) c x
  next  f (CR c) y = next  (\z -> f z . CR) c y
  prev  f (CL c) x = prev  (\z -> f z . CL) c x
  prev  f (CR c) y = prev  (\z -> f z . CR) c y

instance (Zipper f, Zipper g) => Zipper (f :*: g) where
  cmap  f (C1 c y)   = C1 (cmap f c) (hmap f y)
  cmap  f (C2 x c)   = C2 (hmap f x) (cmap f c)
  fill    (C1 c y) x = fill c x :*: y
  fill    (C2 x c) y = x :*: fill c y
  first f (x :*: y)                =
                first (\z c  -> f z (C1 c          y ))   x `mplus`
                first (\z c  -> f z (C2 x          c ))   y
  last  f (x :*: y)                 =
                last  (\z c  -> f z (C2 x          c ))   y `mplus`
                last  (\z c  -> f z (C1 c          y ))   x
  next  f (C1 c y) x =
                next  (\z c' -> f z (C1 c'         y )) c x `mplus`
                first (\z c' -> f z (C2 (fill c x) c'))   y
  next  f (C2 x c) y =
                next  (\z c' -> f z (C2 x          c')) c y
  prev  f (C1 c y) x =
                prev  (\z c' -> f z (C1 c'         y )) c x

  prev  f (C2 x c) y =
                prev  (\z c' -> f z (C2 x          c')) c y `mplus`
                last  (\z c' -> f z (C1 c' (fill c y)))   x

instance Zipper f => Zipper (f :>: xi) where
  cmap  f (CTag prf c)   = CTag prf (cmap f c)
  fill    (CTag prf c) x = castTag prf Tag (fill c x)
  first f (Tag x)        = first (\z -> f z . CTag Refl)   x
  last  f (Tag x)        = last  (\z -> f z . CTag Refl)   x
  next  f (CTag prf c) x = next  (\z -> f z . CTag prf)  c x
  prev  f (CTag prf c) x = prev  (\z -> f z . CTag prf)  c x

instance (Constructor c, Zipper f) => Zipper (C c f) where
  cmap  f (CC c)   = CC (cmap f c)
  fill    (CC c) x = C (fill c x)
  first f (C x)    = first (\z -> f z . CC) x
  last  f (C x)    = last  (\z -> f z . CC) x
  next  f (CC c) x = next  (\z -> f z . CC) c x
  prev  f (CC c) x = prev  (\z -> f z . CC) c x

-- * Interface

-- ** Introduction

-- | Start navigating a datastructure. Returns a location that
-- focuses the entire value and has an empty context.
enter :: (Ix s ix, Zipper (PF s)) => s ix -> ix -> Loc s I0 ix
enter _ x = Loc (I0 x) Empty

-- ** Navigation

-- | Move down to the leftmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down            :: Loc s I0 ix -> Maybe (Loc s I0 ix)

-- | Move down to the rightmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down'           :: Loc s I0 ix -> Maybe (Loc s I0 ix)

-- | Move up to the parent. Returns 'Nothing' if the current
-- focus is the root.
up              :: Loc s I0 ix -> Maybe (Loc s I0 ix)

-- | Move to the right sibling. Returns 'Nothing' if the current
-- focus is the rightmost sibling.
right           :: Loc s r ix -> Maybe (Loc s r ix)

-- | Move to the left sibling. Returns 'Nothing' if the current
-- focus is the leftmost sibling.
left            :: Loc s r ix -> Maybe (Loc s r ix)

down     (Loc (I0 x) s         ) = first (\z c  -> Loc z (Push c  s))   (from x)
down'    (Loc (I0 x) s         ) = last  (\z c  -> Loc z (Push c  s))   (from x)
up       (Loc x Empty     ) = Nothing
up       (Loc x (Push c s)) = return (Loc (I0 $ to (fill c x)) s)
right    (Loc x Empty     ) = Nothing
right    (Loc x (Push c s)) = next  (\z c' -> Loc z (Push c' s)) c x
left     (Loc x Empty     ) = Nothing
left     (Loc x (Push c s)) = prev  (\z c' -> Loc z (Push c' s)) c x

-- ** Elimination

-- | Return the entire value, independent of the current focus.
leave :: Loc s I0 ix -> ix
leave (Loc (I0 x) Empty) = x
leave loc                = leave (fromJust (up loc))

-- | Operate on the current focus. This function can be used to
-- extract the current point of focus.
on :: (forall xi. s xi -> r xi -> a)  -> Loc s r ix -> a
on f (Loc x _) = f index x

-- | Update the current focus without changing its type.
update          :: (forall xi. s xi -> xi -> xi) -> Loc s I0 ix -> Loc s I0 ix
update f (Loc (I0 x) s) = Loc (I0 $ f index x) s

-- | Most general eliminator. Both 'on' and 'update' can be defined
-- in terms of 'foldZipper'.
foldZipper :: (forall ix. Ix s ix => s ix -> ix -> r ix) -> Algebra s r -> Loc s I0 ix -> r ix
foldZipper f alg (Loc (I0 x) c) = cfold alg c (f index x)
 where
  cfold :: (Ix s b, Zipper (PF s)) => Algebra s r -> Ctxs s I0 a b -> r b -> r a
  cfold alg Empty      x = x
  cfold alg (Push c s) x = cfold alg s (alg index (fill (cmap (\ _ (I0 x) -> fold alg x) c) x))

-- * Internal functions

impossible :: a -> b
impossible x = error "impossible"

-- Helping the typechecker to apply equality proofs correctly ...

castId  :: (b :=: xi)
        -> (Ix s xi => r xi -> I xi s r ix)
        -> (Ix s b  => r b  -> I xi s r ix)

castTag :: (ix :=: xi)
        -> (f s r ix -> (f :>: ix) s r ix)
        -> (f s r ix -> (f :>: xi) s r ix)

castId  Refl f = f
castTag Refl f = f
