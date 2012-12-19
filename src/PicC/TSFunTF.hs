{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

-- For Transformable instance. Maybe move elsewhere
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

----------------------------------------------------------------------
-- |
-- Module      :  PicC.TSFunTF
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- TS functions via type families
----------------------------------------------------------------------

module PicC.TSFunTF where

-- TODO: explicit exports

import Prelude hiding (id,(.))

import Control.Category
import Control.Arrow

-- import Control.Compose ((<~))

-- import Control.Newtype

-- Maybe move elsewhere
import Diagrams.Prelude (Transformable(..),V)

type a :* b = (a,b)

type family   TS u t

type instance TS ()       t = ()
type instance TS (a :* b) t = TS a t :* TS b t
type instance TS Bool     t = t

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

instance Arrow (~>) => Arrow (TSFun x (~>)) where
  arr _ = error "arr: not defined for TSFun"
  TF f *** TF g = TF (f *** g)
  f &&& g  = (f *** g) . dup
  first  f = f *** id
  second g = id *** g

dup :: Arrow (~>) => TSFun x (~>) a (a :* a)
dup = TF (arr (\ d -> (d,d)))
-- dup = error "dup on TSFun temporary suspended"

-- I'll have to use something other than arr here. Probably replace Arrow with
-- CategoryProduct

-- I don't think I can define lift, as it would have to convert a ~> b to TS a ~> TS b.

{--------------------------------------------------------------------
    Maybe move elsewhere. Here to avoid orphans
--------------------------------------------------------------------}

instance Transformable (TS a x ~> TS b x) =>
         Transformable (TSFun x (~>) a b) where
  transform tr = TF . transform tr  . runTSFun

-- Needed for Transformable TSFun instance
type instance V (TSFun x (~>) a b) = V (TS a x ~> TS b x)

-- Had to specialize to functions, since transform tr is one.

-- Alternatively, spell out requirements explicitly:
-- 
--   instance ( HasTrie (Basis (V (TS b x))), HasBasis (V (TS b x))
--            , Transformable (TS a x), Transformable (TS b x)
--            , V (TS a x) ~ V (TS b x)) =>
--            Transformable (TSFun x (->) a b) where
--     transform tr (TF f) = TF (transform tr f)
