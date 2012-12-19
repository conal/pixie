{-# LANGUAGE Arrows, GADTs, TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  PicC.PicC
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit pictures via the diagrams library
----------------------------------------------------------------------

module PicC.PicC where

-- TODO: explicit exports

import Prelude hiding (id,(.))
import Diagrams.Prelude
import Diagrams.Backend.SVG
import Diagrams.Backend.SVG.CmdLine

import Control.Category
import Control.Arrow
import Control.Arrow.Operations (write)
import Control.Arrow.Transformer.Writer

import Data.AffineSpace.Point

import Data.MemoTrie (HasTrie)
import Data.Basis (HasBasis(..))

import PicC.TSFunTF -- or TSFunGadt

newtype Pins v a = Pins (TS a (Point v))

-- type PicC' e v m a b = Pins v a -> (Pins b v, QDiagram e v m)

type TPFun v = TSFun (Point v)

type PicC' e v m = TPFun v (WriterArrow (QDiagram e v m) (->))

runPicC :: ( Semigroup m, Floating (Scalar v), Ord (Scalar v)
           , InnerSpace v, HasBasis v, HasTrie (Basis v)) =>
           PicC' e v m a b -> TS a (Point v) -> (TS b (Point v), QDiagram e v m)
runPicC q a = runWriter (runTSFun q) a

type PicC e = PicC' e R2 Any

type Diag = forall e. Renderable (Path R2) e => QDiagram e R2 Any

type a :> b = forall e. Renderable (Path R2) e => PicC e a b

type Ports a = TS a P2

test :: a :> b -> Ports a -> IO (Ports b)
test q a = defaultMain (d # pad 1.1) >> return b
 where
   (b,d) = runPicC q a

draw :: ( Semigroup m, InnerSpace v, HasBasis v, HasTrie (Basis v)
        , s ~ Scalar v, Floating s, Fractional s, Ord s) =>
        QDiagram e v m -> PicC' e v m () ()
draw d = TF $ write . arr (const d)

-- draw d = TF $ arr (\ () -> d) >>> write
-- draw d = TF $ proc () -> do write -< d

-- I didn't move the diagram into the TSFun arrow domain, because it's a single
-- diagram, not a TS full of them.

box1 :: (a -> b) -> a :> b
box1 f = proc a -> do
  draw unitSquare -< ()
  returnA -< f a

-- R2 & Any (PicC) in box1 come from unitSquare

-- Oops -- box1 desugars via arr, which bombs.

box2 :: () :> ()
box2 = proc () ->
         draw unitSquare -< ()

-- box2 also bombs. I think it desugars to arr (\ () -> ()) >>> draw unitSquare.

-- t1 :: IO P2
-- t1 = test (box2 (id :: Bool -> Bool)) (p2 (-1,0))

t2 :: IO ()
t2 = test box2 ()

t3 :: IO ()
t3 = test (draw unitSquare) ()

-- test :: a :> b -> Ports a -> IO (Ports b)

port :: Colour Double -> P2 -> Diag
port c p = circle 0.02 # fc c # translate (unPoint p)

iPort, oPort :: P2 -> Diag
iPort = port white
oPort = port black

-- p2 :: (Double,Double) -> P2
-- p2 = P . r2

box4 :: Bool :> Bool
box4 = TF $
  proc src -> do
    let ip = p2 (-0.5,0)
        op = p2 ( 0.5,0)
    write -< (src ~~> ip) <> iPort ip <> oPort op <> unitSquare
    returnA -< op

t4 :: IO P2
t4 = test box4 (p2 (-0.5,0))

-- Arrow from source to sink
(~~>) :: P2 -> P2 -> Diag
src ~~> snk = src ~~ snk <> h
 where
   h =   eqTriangle (sqrt 3 / 2)        -- circum-diameter 1
       # fc black
       # rotate (30 :: Deg)             -- point right
       # translate (r2 (-0.5, 0))       -- tip at origin
       # scale 0.075
       # scaleY 0.75                    -- narrower
       # rotate (angle (snk .-. src))
       # translate (unPoint snk)

-- angle :: (AffineSpace p, Diff p ~ R2) => p -> p -> Rad
-- angle src snk = Rad (uncurry atan2 (unr2 (snk .-. src)))

angle :: R2 -> Rad
angle v = Rad (uncurry (flip atan2) (unr2 v))


-- (~~>) = (~~)
