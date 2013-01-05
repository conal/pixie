{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

-- For Transformable instance. Maybe move elsewhere
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

----------------------------------------------------------------------
-- |
-- Module      :  Pixie.TSFunTF
-- Copyright   :  (c) 2012 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Type-structured collections via type families
----------------------------------------------------------------------

module Pixie.TSFunTF where

-- TODO: explicit exports

import Prelude hiding (id,(.),fst,snd)

import Control.Category
import Control.Arrow

-- import Control.Newtype

import FunctorCombo.Functor (Const,Id,(:*:),(:+:),(:.))

import TypeUnary.Vec (Vec)

-- Maybe move elsewhere
import Diagrams.Prelude (Transformable(..),V)

import CatSynth.Has
import CatSynth.Decode

#include "CatSynth/Has-inc.hs"

type a :* b = (a,b)
type a :+ b = Either a b

type family   TS u t

type instance TS ()        t = ()
type instance TS (a :* b)  t = TS a t :* TS b t
type instance TS (a :+ b)  t = TS a t :+ TS b t     -- Really?? Maybe product.

type instance TS [a]       t = [TS a t]
type instance TS (Vec n a) t = Vec n (TS a t)

type instance TS Bool     t = t         -- TODO: add more

type    TSFunX x (~>) a b = TS a x ~> TS b x
newtype TSFun  x (~>) a b = TF { runTSFun :: TSFunX x (~>) a b }

-- instance Newtype (TSFun  x (~>) a b) (TS a x ~> TS b x) where
--   pack   = TF
--   unpack = runTSFun
--
--    Illegal type synonym family application in instance:

instance Category (~>) => Category (TSFun x (~>)) where
  id  = TF id
  TF g . TF f = TF (g . f)

instance HasPair (~>) => Arrow (TSFun x (~>)) where
  arr _ = error "arr: not defined for TSFun"
  TF f *** TF g = TF (f *** g)
  f &&& g  = (f *** g) . dup
  first  f = f *** id
  second g = id *** g

instance (Arrow (~>), HasPair (~>)) => HasPair (TSFun x (~>)) where
  fst       = TF fst
  snd       = TF snd
  dup       = TF dup
  ldistribP = TF ldistribP
  rdistribP = TF rdistribP

-- I don't think TSFun x can be an arrow transformer, since lift would have to
-- convert a ~> b to TS a ~> TS b.

instance (HasPair (~>), HasEither (~>), ArrowChoice (~>)) 
      => ArrowChoice (TSFun x (~>)) where
  TF f +++ TF g = TF (f +++ g)
  f ||| g  = jam . (f +++ g)
  left  f = f +++ id
  right g = id +++ g

instance (HasPair (~>), HasEither (~>)) => HasEither (TSFun x (~>)) where
  lft       = TF lft
  rht       = TF rht
  jam       = TF jam
  ldistribS = TF ldistribS
  rdistribS = TF rdistribS

-- instance (HasPair (~>), HasConst (~>)) => HasConst (TSFun x (~>)) where
--   lconst a = TF 

-- class HasPair (~>) => HasConst (~>) where
--   type HasConstConstraint (~>) t :: Constraint
--   type HasConstConstraint (~>) t = HasConstConstraint0 (~>) t -- () -- NullC
--   lconst :: HasConstConstraint (~>) a => a -> (b ~> (a,b))
--   rconst :: HasConstConstraint (~>) b => b -> (a ~> (a,b))
--   const  :: HasConstConstraint (~>) b => b -> (a ~> b)
--   const b = snd . rconst b

type instance TS (Id a) x = Id (TS a x)

instance HasId (~>) => HasId (TSFun x (~>)) where
  toId = TF toId
  unId = TF unId

type instance TS ((f :*: g) a) t = (f :*: g) (TS a t)  -- etc

-- class Arrow (~>) => HasProd (~>) where
--   toProd :: (f a :* g a) ~> (f :*: g) a
--   unProd :: (f :*: g) a ~> (f a :* g a)

{-

instance (HasPair (~>), HasProd (~>)) =>
         HasProd (TSFun x (~>)) where
  toProd = TF toProd
--  unProd = TF unProd

-- type    TSFunX x (~>) a b = TS a x ~> TS b x
-- newtype TSFun  x (~>) a b = TF { runTSFun :: TSFunX x (~>) a b }

-- type instance TS (a :* b)  t = TS a t :* TS b t

toProd :: (f a :* g a) ~> (f :*: g) a

want :: TS (f a :* g a) x ~> TS ((f :*: g) a) x
     :: (TS (f a) x :* TS (g a) x) ~> (f :*: g) (TS a x)

-}

{--------------------------------------------------------------------
    Maybe move elsewhere. Here to avoid orphans.
--------------------------------------------------------------------}

instance Transformable (TS a x ~> TS b x) =>
         Transformable (TSFun x (~>) a b) where
  transform tr = TF . transform tr  . runTSFun

-- Needed for Transformable TSFun instance
type instance V (TSFun x (~>) a b) = V (TS a x ~> TS b x)

{--------------------------------------------------------------------
    Dubious attempt at TSFun instances
--------------------------------------------------------------------}

{-

type instance TS (Const b a) t = Const (TS b t) a
type instance TS (Id a) t = Id (TS a t)
type instance TS ((f :*: g) a) t = (f :*: g) (TS a t)

-- TransInstances(TF,TSFun x,HasPair (~>))

TransInstance(HasConstF,toConst,unConst,TF,TSFun x,()~())
TransInstance(HasId,toId,unId,TF,TSFun x, ()~())

instance (HasPair(~>), Arrow (~>), HasProd (~>)) => HasProd (TSFun x (~>)) where
  { toProd = TF toProd ; unProd = TF unProd }

--     Could not deduce (TS (g a) x ~ g (TS a x))
--     from the context (HasPair (~>), Arrow (~>), HasProd (~>))

-- class Arrow (~>) => HasProd (~>) where
--   toProd :: (f a :* g a) ~> (f :*: g) a
--   unProd :: (f :*: g) a ~> (f a :* g a)


-- TransInstance(HasProd,toProd,unProd,TF,TSFun x, HasPair (~>))
-- TransInstance(HasSum,toSum,unSum,TF,TSFun x, ()~())
-- TransInstance(HasComp,toO,unO,TF,TSFun x, ()~())

-}


-- type    TSFunX x (~>) a b = TS a x ~> TS b x
-- newtype TSFun  x (~>) a b = TF { runTSFun :: TSFunX x (~>) a b }

-- class Category ar => Decode ar a where
--   decode :: a `ar` Decoding a
--   encode :: Decoding a `ar` a

-- instance Decode (TSFun x (->)) a where
--   -- decode :: TSFun x (->) a (Decoding a)
--   decode = TF (tsMap decode)
--   -- decode = TF (tsMap undefined)

--     Couldn't match type `TS (Decoding a) x' with `TS (Decoding a0) x0'
--     NB: `TS' is a type function, and may not be injective
--     Expected type: TSFunX x (->) a (Decoding a)
--       Actual type: TS a0 x0 -> TS (Decoding a0) x0

-- tsMap :: (a -> b) -> TS a x -> TS b x
-- tsMap = undefined

-- tsDecode :: TS a x -> TS (Decoding a) x
-- tsDecode = tsMap undefined
