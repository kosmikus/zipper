{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Generics.MultiRec.Zipper where

import Prelude hiding (last)

import Control.Monad
import Data.Maybe
import Generics.MultiRec.Base
-- import TEq

-- * Locations and context stacks

data Loc :: (* -> *) -> * -> * where
  Loc :: (Ix s ix, Zipper (PF s)) => ix -> Ctxs s a ix -> Loc s a

data Ctxs :: (* -> *) -> * -> * -> * where
  Empty :: Ctxs s a a
  Push  :: Ix s ix => Ctx (PF s) s ix b -> Ctxs s a ix -> Ctxs s a b

-- * Context frames

data family Ctx f :: (* -> *) -> * -> * -> *

data instance Ctx (K a) s ix b
data instance Ctx (f :+: g) s ix b  = CL (Ctx f s ix b) 
                                    | CR (Ctx g s ix b)
data instance Ctx (f :*: g) s ix b  = C1 (Ctx f s ix b) (g s I0 ix) 
                                    | C2 (f s I0 ix) (Ctx g s ix b)

-- The equality constraints simulate GADTs. GHC currently
-- does not allow us to use GADTs as data family instances.

data instance Ctx (I xi) s ix b     = CId (b :=: xi)
data instance Ctx (f :>: xi) s ix b = CTag (ix :=: xi) (Ctx f s ix b)

-- * Internal stuff

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

impossible x = error "impossible"

-- * Generic navigation functions

class Zipper f where
  fill        :: Ix s b => Ctx f s ix b -> b -> f s I0 ix
  first, last :: (forall b. Ix s b => b -> Ctx f s ix b -> a)
              -> f s I0 ix -> Maybe a
  next, prev  :: (forall b. Ix s b => b -> Ctx f s ix b -> a)
              -> Ix s b => Ctx f s ix b -> b -> Maybe a

instance Zipper (I xi) where
  fill    (CId prf) x = castId prf (I . I0) x
  first f (I (I0 x))  = return (f x (CId Refl))
  last  f (I (I0 x))  = return (f x (CId Refl))
  next  f (CId prf) x = Nothing 
  prev  f (CId prf) x = Nothing 

instance Zipper (K a) where
  fill    void x = impossible void
  first f (K a)  = Nothing
  last  f (K a)  = Nothing
  next  f void x = impossible void
  prev  f void x = impossible void

instance (Zipper f, Zipper g) => Zipper (f :+: g) where
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
  fill    (CTag prf c) x = castTag prf Tag (fill c x)
  first f (Tag x)        = first (\z -> f z . CTag Refl)   x
  last  f (Tag x)        = last  (\z -> f z . CTag Refl)   x
  next  f (CTag prf c) x = next  (\z -> f z . CTag prf)  c x
  prev  f (CTag prf c) x = prev  (\z -> f z . CTag prf)  c x

-- Helping the typechecker to apply equality proofs correctly ...

castId  :: (b :=: xi)
        -> (Ix s xi => xi -> I xi s I0 ix)
        -> (Ix s b  => b  -> I xi s I0 ix)

castTag :: (ix :=: xi)
        -> (f s I0 ix -> (f :>: ix) s I0 ix)
        -> (f s I0 ix -> (f :>: xi) s I0 ix)

castId  Refl f = f
castTag Refl f = f

-- * Interface

enter           :: (Ix s ix, Zipper (PF s)) => s ix -> ix -> Loc s ix
down, down', up :: Loc s ix -> Maybe (Loc s ix)
right, left     :: Loc s ix -> Maybe (Loc s ix)
leave           :: Loc s ix -> ix
on              :: (forall xi. s xi -> xi -> a)  -> Loc s ix -> a
update          :: (forall xi. s xi -> xi -> xi) -> Loc s ix -> Loc s ix

enter _ x                   = Loc x Empty
down     (Loc x s         ) = first (\z c  -> Loc z (Push c  s))   (from x)
down'    (Loc x s         ) = last  (\z c  -> Loc z (Push c  s))   (from x)
up       (Loc x Empty     ) = Nothing
up       (Loc x (Push c s)) = return (Loc (to (fill c x)) s)
right    (Loc x Empty     ) = Nothing
right    (Loc x (Push c s)) = next  (\z c' -> Loc z (Push c' s)) c x
left     (Loc x Empty     ) = Nothing
left     (Loc x (Push c s)) = prev  (\z c' -> Loc z (Push c' s)) c x
leave    (Loc x Empty)      = x
leave    loc                = leave (fromJust (up loc))
on f     (Loc x _         ) =      f index x
update f (Loc x s         ) = Loc (f index x) s
