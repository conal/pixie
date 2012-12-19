{-# LANGUAGE TypeOperators, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  PicC.TSFunGadt
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- TS structure as GADT
----------------------------------------------------------------------

module PicC.TSFunGadt where

-- TODO: explicit exports

import Prelude hiding (id,(.))

import Data.Monoid (mappend)
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))

import Control.Category
import Control.Arrow

type a :* b = (a,b)

-- | Type-structured container
data TS :: * -> * -> * where
  TVal  :: t -> TS a t
  (::*) :: TS a t -> TS b t -> TS (a :* b) t

pair :: TS a t :* TS b t -> TS (a :* b) t
pair = uncurry (::*)

unpair :: TS (a :* b) t -> TS a t :* TS b t
unpair (TVal t)  = (TVal t, TVal t)
unpair (u ::* v) = (u, v)

instance Functor (TS a) where
  fmap f (TVal t)  = TVal (f t)
  fmap f (u ::* v) = fmap f u ::* fmap f v

instance Applicative (TS a) where
  pure = TVal
  TVal f <*> TVal x = TVal (f x)
  (f ::* g)  <*>  v = (f <*> x) ::* (g <*> y) where (x,y) = unpair v
  h  <*>  (x ::* y) = (f <*> x) ::* (g <*> y) where (f,g) = unpair h

-- inTS :: TS t -> TS (Set T) -> Bool
-- inTS = liftA2 member

instance Foldable (TS a) where
  foldMap f (TVal t) = f t
  foldMap f (us ::* vs) = foldMap f us `mappend` foldMap f vs

instance Traversable (TS a) where
  traverse f (TVal t)    = TVal <$> f t
  traverse f (us ::* vs) = liftA2 (::*) (traverse f us) (traverse f vs)

type    TSFunX (~>) v a b = TS a v ~> TS b v
newtype TSFun  (~>) v a b = TF { unTF :: TSFunX (~>) v a b }

instance Category (~>) => Category (TSFun (~>) v) where
  id  = TF id
  TF g . TF f = TF (g . f)

instance Arrow (~>) => Arrow (TSFun (~>) v) where
  arr _ = error "arr: not defined for TSFun"
  TF f *** TF g = TF (arr pair . (f *** g) . arr unpair)
  f &&& g  = (f *** g) . dup
  first  f = f *** id
  second g = id *** g

dup :: Arrow (~>) => TSFun (~>) v a (a :* a)
dup = TF (arr (\ d -> d ::* d))

-- Hm! I can't simultaneously reject arr and use it for *** & dup.

-- Alternatively, replace the GADT with a type family. Simpler Arrow but no
-- Functor, Applicative, Foldable, Traversable instance.
