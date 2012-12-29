{-# LANGUAGE TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-} -- for V type instance
{-# LANGUAGE FlexibleContexts #-} -- for HasTS Vec
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Pixie.TSFunGadt
-- Copyright   :  (c) 2012 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Type-structured collections as GADT
----------------------------------------------------------------------

module Pixie.TSFunGadt where

-- TODO: explicit exports

import Prelude hiding (id,(.))

import Data.Monoid (Monoid(..))
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))

import Control.Category
import Control.Arrow

import Control.Newtype

import TypeUnary.Vec

-- Maybe move elsewhere
import Diagrams.Prelude (Transformable(..),V)

infixl 7 :*
infixl 6 :+

type a :* b = (a,b)
type a :+ b = Either a b

-- | Type-structured container
data TS :: * -> * -> * where
  TUnit :: TS () t
  TVal  :: t -> TS a t
  (::*) :: TS a t -> TS b t -> TS (a :* b) t
  TIso  :: Newtype n o => TS o t -> TS n t

prod :: TS a t :* TS b t -> TS (a :* b) t
prod = uncurry (::*)

unprod :: TS (a :* b) t -> TS a t :* TS b t
unprod (TVal t)  = (TVal t, TVal t)
unprod (u ::* v) = (u, v)
unprod (TIso _)  = error "unprod: TIso"  -- a :* b is not Packed

instance Functor (TS a) where
  fmap _ TUnit     = TUnit
  fmap f (TVal t)  = TVal (f t)
  fmap f (u ::* v) = fmap f u ::* fmap f v
  fmap f (TIso u)  = TIso (fmap f u)

instance Applicative (TS a) where
  pure = TVal
  TVal f <*> TVal x = TVal (f x)
  (f ::* g)  <*>  v = (f <*> x) ::* (g <*> y) where (x,y) = unprod v
  h  <*>  (x ::* y) = (f <*> x) ::* (g <*> y) where (f,g) = unprod h
  -- TIso fs <*> TIso xs = TIso (fs <*> xs)   -- Could not deduce (o1 ~ o)
  _ <*> _ = error "(<*>) on TIso: oops! Non-injective."

-- inTS :: TS t -> TS (Set T) -> Bool
-- inTS = liftA2 member

instance Foldable (TS a) where
  foldMap _ TUnit       = mempty
  foldMap f (TVal t)    = f t
  foldMap f (us ::* vs) = foldMap f us `mappend` foldMap f vs
  foldMap f (TIso us)   = foldMap f us

instance Traversable (TS a) where
  traverse _ TUnit       = pure TUnit
  traverse f (TVal t)    = TVal <$> f t
  traverse f (us ::* vs) = liftA2 (::*) (traverse f us) (traverse f vs)
  traverse f (TIso us)   = TIso <$> traverse f us

type    TSFunX (~>) v a b = TS a v ~> TS b v
newtype TSFun  (~>) v a b = TF { unTF :: TSFunX (~>) v a b }

instance Category (~>) => Category (TSFun (~>) v) where
  id  = TF id
  TF g . TF f = TF (g . f)

instance Arrow (~>) => Arrow (TSFun (~>) v) where
  arr _ = error "arr: not defined for TSFun"
  TF f *** TF g = TF (arr prod . (f *** g) . arr unprod)
  f &&& g  = (f *** g) . dup
  first  f = f *** id
  second g = id *** g

dup :: Arrow (~>) => TSFun (~>) v a (a :* a)
dup = TF (arr (\ d -> d ::* d))

-- Alternatively, replace the GADT with a type family. Simpler Arrow but no
-- Functor, Applicative, Foldable, Traversable instance. See TSFunTF.

{--------------------------------------------------------------------
    Conversion to & from TS
--------------------------------------------------------------------}

class HasTS v a t where
  toTS :: v -> TS a t
  unTS :: TS a t -> v

instance HasTS t Bool t where
  toTS b = TVal b
  unTS (TVal b) = b
  unTS (TIso _) = error "unTS: TIso"
instance (HasTS u a t, HasTS v b t) => HasTS (u :* v) (a :* b) t where
  toTS (u,v) = toTS u ::* toTS v
  unTS r = (unTS p, unTS q) where (p,q) = unprod r

instance HasTS (Vec Z t) () t where
  toTS ZVec = TUnit
  unTS TUnit = ZVec
  unTS _ = error "unTS on Vec Z: not TUnit"
instance (HasTS u a t, HasTS (Vec n u) as t) => 
         HasTS (Vec (S n) u) (a :* as) t where
  toTS (a :< as) = toTS a ::* toTS as
  unTS (u ::* v) = unTS u :< unTS v
  unTS _ = error "unTS on Vec (S n): not ::*"

{--------------------------------------------------------------------
    Diagrams support
--------------------------------------------------------------------}

-- Needed for Transformable instance
type instance V (TS a t) = V t

instance Transformable t => Transformable (TS a t) where
  transform xf = fmap (transform xf)
