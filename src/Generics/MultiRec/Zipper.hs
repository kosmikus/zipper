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
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
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
   enter,
   down, down', up, right, left,
   dfnext, dfprev,
   leave, on, update, foldZipper
  ) where

import Prelude hiding (last)

import Control.Monad
import Control.Applicative
import Data.Maybe

import Generics.MultiRec.Base
import Generics.MultiRec.Fold
import Generics.MultiRec.HFunctor

-- * Locations and context stacks

-- | Abstract type of locations. A location contains the current focus
-- and its context. A location is parameterized over the family of
-- datatypes and over the type of the complete value.

data Loc :: (* -> *) -> (* -> *) -> * -> * where
  Loc :: (Fam phi, Zipper phi (PF phi)) => phi ix -> r ix -> Ctxs phi ix r a -> Loc phi r a

data Ctxs :: (* -> *) -> * -> (* -> *) -> * -> * where
  Empty :: Ctxs phi a r a
  Push  :: phi ix -> Ctx (PF phi) b r ix -> Ctxs phi ix r a -> Ctxs phi b r a

-- * Context frames

-- | Abstract type of context frames. Not required for the high-level
-- navigation functions.

data family Ctx f :: * -> (* -> *) -> * -> *

data instance Ctx (K a) b r ix
data instance Ctx U b r ix
data instance Ctx (f :+: g) b r ix  = CL (Ctx f b r ix)
                                    | CR (Ctx g b r ix)
data instance Ctx (f :*: g) b r ix  = C1 (Ctx f b r ix) (g r ix)
                                    | C2 (f r ix) (Ctx g b r ix)

-- The equality constraints simulate GADTs. GHC currently
-- does not allow us to use GADTs as data family instances.

data instance Ctx (I xi) b r ix     = CId (b :=: xi)
data instance Ctx (f :>: xi) b r ix = CTag (ix :=: xi) (Ctx f b r ix)
data instance Ctx (C c f) b r ix    = CC (Ctx f b r ix)

-- * Contexts and locations are functors

instance Zipper phi f => HFunctor phi (Ctx f b) where
  hmapA = cmapA

instance Zipper phi (PF phi) => HFunctor phi (Ctxs phi b) where
  hmapA f Empty        = pure Empty
  hmapA f (Push p c s) = liftA2 (Push p) (hmapA f c) (hmapA f s)

instance HFunctor phi (Loc phi) where
  hmapA f (Loc p x s) = liftA2 (Loc p) (f p x) (hmapA f s)

-- * Generic navigation functions

-- | It is in general not necessary to use the generic navigation
-- functions directly. The functions listed in the ``Interface'' section
-- below are more user-friendly.
--

class HFunctor phi f => Zipper phi f where
  cmapA       :: Applicative a => (forall ix. phi ix -> r ix -> a (r' ix)) ->
                 Ctx f b r ix -> a (Ctx f b r' ix)
  fill        :: phi b -> Ctx f b r ix -> r b -> f r ix
  first, last :: (forall b. phi b -> r b -> Ctx f b r ix -> a)
              -> f r ix -> Maybe a
  next, prev  :: (forall b. phi b -> r b -> Ctx f b r ix -> a)
              -> phi b -> Ctx f b r ix -> r b -> Maybe a

instance El phi xi => Zipper phi (I xi) where
  cmapA f   (CId prf)   = pure (CId prf)
  fill    p (CId prf) x = castId prf I x
  first f (I x)  = return (f proof x (CId Refl))
  last  f (I x)  = return (f proof x (CId Refl))
  next  f p (CId prf) x = Nothing
  prev  f p (CId prf) x = Nothing

instance Zipper phi (K a) where
  cmapA f   void   = impossible void
  fill    p void x = impossible void
  first f (K a)    = Nothing
  last  f (K a)    = Nothing
  next  f p void x = impossible void
  prev  f p void x = impossible void

instance Zipper phi U where
  cmapA f   void   = impossible void
  fill    p void x = impossible void
  first f U        = Nothing
  last  f U        = Nothing
  next  f p void x = impossible void
  prev  f p void x = impossible void

instance (Zipper phi f, Zipper phi g) => Zipper phi (f :+: g) where
  cmapA f   (CL c)   = liftA CL (cmapA f c)
  cmapA f   (CR c)   = liftA CR (cmapA f c)
  fill    p (CL c) x = L (fill p c x)
  fill    p (CR c) y = R (fill p c y)
  first f (L x)      = first (\p z -> f p z . CL) x
  first f (R y)      = first (\p z -> f p z . CR) y
  last  f (L x)      = last  (\p z -> f p z . CL) x
  last  f (R y)      = last  (\p z -> f p z . CR) y
  next  f p (CL c) x = next  (\p z -> f p z . CL) p c x
  next  f p (CR c) y = next  (\p z -> f p z . CR) p c y
  prev  f p (CL c) x = prev  (\p z -> f p z . CL) p c x
  prev  f p (CR c) y = prev  (\p z -> f p z . CR) p c y

instance (Zipper phi f, Zipper phi g) => Zipper phi (f :*: g) where
  cmapA f   (C1 c y)   = liftA2 C1 (cmapA f c) (hmapA f y)
  cmapA f   (C2 x c)   = liftA2 C2 (hmapA f x) (cmapA f c)
  fill    p (C1 c y) x = fill p c x :*: y
  fill    p (C2 x c) y = x :*: fill p c y
  first f (x :*: y)                =
                first (\p z c  -> f p z (C1 c          y ))   x `mplus`
                first (\p z c  -> f p z (C2 x          c ))   y
  last  f (x :*: y)                 =
                last  (\p z c  -> f p z (C2 x          c ))   y `mplus`
                last  (\p z c  -> f p z (C1 c          y ))   x
  next  f p (C1 c y) x =
                next  (\p' z c' -> f p' z (C1 c'           y )) p c x `mplus`
                first (\p' z c' -> f p' z (C2 (fill p c x) c'))     y
  next  f p (C2 x c) y =
                next  (\p' z c' -> f p' z (C2 x            c')) p c y
  prev  f p (C1 c y) x =
                prev  (\p' z c' -> f p' z (C1 c'           y )) p c x
  prev  f p (C2 x c) y =
                prev  (\p' z c' -> f p' z (C2 x            c')) p c y `mplus`
                last  (\p' z c' -> f p' z (C1 c' (fill p c y)))     x

instance Zipper phi f => Zipper phi (f :>: xi) where
  cmapA f   (CTag prf c)   = liftA (CTag prf) (cmapA f c)
  fill    p (CTag prf c) x = castTag prf Tag (fill p c x)
  first f (Tag x)          = first (\p z -> f p z . CTag Refl)     x
  last  f (Tag x)          = last  (\p z -> f p z . CTag Refl)     x
  next  f p (CTag prf c) x = next  (\p z -> f p z . CTag prf)  p c x
  prev  f p (CTag prf c) x = prev  (\p z -> f p z . CTag prf)  p c x

instance (Constructor c, Zipper phi f) => Zipper phi (C c f) where
  cmapA f   (CC c)   = liftA CC (cmapA f c)
  fill    p (CC c) x = C (fill p c x)
  first f (C x)      = first (\p z -> f p z . CC)     x
  last  f (C x)      = last  (\p z -> f p z . CC)     x
  next  f p (CC c) x = next  (\p z -> f p z . CC) p c x
  prev  f p (CC c) x = prev  (\p z -> f p z . CC) p c x

-- * Interface

-- ** Introduction

-- | Start navigating a datastructure. Returns a location that
-- focuses the entire value and has an empty context.
enter :: (Fam phi, Zipper phi (PF phi)) => phi ix -> ix -> Loc phi I0 ix
enter p x = Loc p (I0 x) Empty

-- ** Navigation

-- | Move down to the leftmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down            :: Loc phi I0 ix -> Maybe (Loc phi I0 ix)

-- | Move down to the rightmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down'           :: Loc phi I0 ix -> Maybe (Loc phi I0 ix)

-- | Move up to the parent. Returns 'Nothing' if the current
-- focus is the root.
up              :: Loc phi I0 ix -> Maybe (Loc phi I0 ix)

-- | Move to the right sibling. Returns 'Nothing' if the current
-- focus is the rightmost sibling.
right           :: Loc phi r ix -> Maybe (Loc phi r ix)

-- | Move to the left sibling. Returns 'Nothing' if the current
-- focus is the leftmost sibling.
left            :: Loc phi r ix -> Maybe (Loc phi r ix)

down     (Loc p (I0 x) s         ) = first (\p' z c  -> Loc p' z (Push p c  s))   (from p x)
down'    (Loc p (I0 x) s         ) = last  (\p' z c  -> Loc p' z (Push p c  s))   (from p x)
up       (Loc p x Empty        ) = Nothing
up       (Loc p x (Push p' c s)) = return (Loc p' (I0 $ to p' (fill p c x)) s)
right    (Loc p x Empty        ) = Nothing
right    (Loc p x (Push p' c s)) = next  (\p z c' -> Loc p z (Push p' c' s)) p c x
left     (Loc p x Empty        ) = Nothing
left     (Loc p x (Push p' c s)) = prev  (\p z c' -> Loc p z (Push p' c' s)) p c x

-- ** Derived navigation.

df :: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
df d u lr l =
  case d l of
    Nothing -> df' l
    r       -> r
 where
  df' l =
    case lr l of
      Nothing -> case u l of
                   Nothing -> Nothing
                   Just l' -> df' l'
      r       -> r

-- | Move through all positions in depth-first left-to-right order.
dfnext :: Loc phi I0 ix -> Maybe (Loc phi I0 ix)
dfnext = df down up right

-- | Move through all positions in depth-first right-to-left order.
dfprev :: Loc phi I0 ix -> Maybe (Loc phi I0 ix)
dfprev = df down' up left

-- ** Elimination

-- | Return the entire value, independent of the current focus.
leave :: Loc phi I0 ix -> ix
leave (Loc p (I0 x) Empty) = x
leave loc                  = leave (fromJust (up loc))

-- | Operate on the current focus. This function can be used to
-- extract the current point of focus.
on :: (forall xi. phi xi -> r xi -> a) -> Loc phi r ix -> a
on f (Loc p x _) = f p x

-- | Update the current focus without changing its type.
update :: (forall xi. phi xi -> xi -> xi) -> Loc phi I0 ix -> Loc phi I0 ix
update f (Loc p (I0 x) s) = Loc p (I0 $ f p x) s

-- | Most general eliminator. Both 'on' and 'update' can be defined
-- in terms of 'foldZipper'.
foldZipper :: (forall xi. phi xi -> xi -> r xi) -> Algebra phi r -> Loc phi I0 ix -> r ix
foldZipper f alg (Loc p (I0 x) c) = cfold alg p c (f p x)
 where
  cfold :: (Fam phi, Zipper phi (PF phi)) => Algebra phi r -> phi b -> Ctxs phi b I0 a -> r b -> r a
  cfold alg p' Empty        x = x
  cfold alg p' (Push p c s) x = cfold alg p s (alg p (fill p' (hmap (\ p (I0 x) -> fold alg p x) c) x))

-- * Internal functions

impossible :: a -> b
impossible x = error "impossible"

-- Helping the typechecker to apply equality proofs correctly ...

castId  :: (b :=: xi)
        -> (r xi -> I xi r ix)
        -> (r b  -> I xi r ix)

castTag :: (ix :=: xi)
        -> (f r ix -> (f :>: ix) r ix)
        -> (f r ix -> (f :>: xi) r ix)

castId  Refl f = f
castTag Refl f = f
