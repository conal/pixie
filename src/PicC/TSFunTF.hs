{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-- {-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

import Control.Arrow.Transformer
import Control.Arrow.Operations
import Control.Arrow.Transformer.Writer

type a :* b = (a,b)

type family TS u a
type instance TS ()       t = ()
type instance TS (a :* b) t = TS a t :* TS b t
type instance TS Bool     t = t

newtype TSFun x (~>) a b = TF { runTSFun :: TS a x ~> TS b x }

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

-- instance Arrow (~>) => ArrowTransformer (TSFun x) (~>)
--   lift f = 

{-

instance ArrowWriter w (~>) => ArrowWriter w (TSFun x (~>)) where
  write = TF undefined

write :: TSFun x (~>) w ()

TS w x 

  newWriter = undefined

-- class (Monoid w, Arrow a) => ArrowWriter w a | a -> w where
--   write     :: a w ()
--   newWriter :: a e b -> a e (b,w)

-- newtype TSFun x (~>) a b = TF { runTSFun :: TS a x ~> TS b x }

--     Illegal instance declaration for `ArrowWriter w (TSFun x (~>))'
--       (the Coverage Condition fails for one of the functional dependencies;
--        Use -XUndecidableInstances to permit this)
--     In the instance declaration for `ArrowWriter w (TSFun x ~>)'

-}
