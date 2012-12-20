{-# LANGUAGE Arrows, GADTs, TypeOperators, TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall #-}

-- Experiment
{-# LANGUAGE ImpredicativeTypes #-}

-- For Transformable WriterArrow instance
{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Pixie.Pixie
-- Copyright   :  (c) 2012 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Circuit pictures via the diagrams library
----------------------------------------------------------------------

module Pixie.Pixie where

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

import Pixie.TSFunTF -- or TSFunGadt

-- type Pins v a = TS a (Point v)
--
-- type Pixie' e v m a b = Pins v a -> (Pins b v, QDiagram e v m)

-- | Circuit picture arrow in its most general form. See also 'Pixie'.
type Pixie e v m = TSFun (Point v) (WriterArrow (QDiagram e v m) (->))

runPixie :: ( Semigroup m, Floating (Scalar v), Ord (Scalar v)
           , InnerSpace v, HasLinearMap v) =>
           Pixie e v m a b -> TS a (Point v) -> (TS b (Point v), QDiagram e v m)
runPixie q a = runWriter (runTSFun q) a

-- | Diagrams containing paths (renderable wherever paths are).
type Diag = forall e. Renderable (Path R2) e => QDiagram e R2 Any

-- | Diagram writer
type DWriter a b = 
  forall e. Renderable (Path R2) e => WriterArrow (QDiagram e R2 Any) (->) a b

-- Alternative. Requires ImpredicativeTypes. Is that forall type a Monoid?
type DWriter' = 
  WriterArrow (forall e. Renderable (Path R2) e => QDiagram e R2 Any) (->)

-- | Circuit picture with typed inputs & outputs
type a :> b = forall e. Renderable (Path R2) e => Pixie e R2 Any a b

-- Alternative
type (:>:) = TSFun (Point R2) DWriter'

-- | Input or output port collection. Currently just a position per component.
type Ports a = TS a P2

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}

-- | Composition with transformation.
comp :: (Category (~>), Transformable (b ~> c), V (b ~> c) ~ v) =>
        Transformation v -> a ~> b -> b ~> c -> a ~> c
comp xf a b = a >>> transform xf b

-- | Composition with translation.
compTranslate :: (Category (~>), Transformable (b ~> c), V (b ~> c) ~ v) =>
                 v -> a ~> b -> b ~> c -> a ~> c
compTranslate = comp . translation

-- Some specialized operators. The right-associativity is critical here for
-- cumulative transformation, since 'comp' transforms its right argument.
infixr 3 -|-, -|/, -|\, -|*, -|&
(-|-),(-|/),(-|\),(-|*),(-|&) :: 
   (Category (~>), Transformable (b ~> c), V (b ~> c) ~ R2) =>
   a ~> b -> b ~> c -> a ~> c
(-|-) = compTranslate (r2 (1, 0))
(-|/) = compTranslate (r2 (1, 1))
(-|\) = compTranslate (r2 (1,-1))
(-|*) = comp (translation (r2 (0.75,0)) <> scaling 0.6)
(-|&) = comp (rotation (1/15 :: CircleFrac) <> translation (r2 (1,0)) <> scaling 0.7)

port :: Colour Double -> P2 -> Diag
port c p = circle 0.02 # fc c # translate (unPoint p)

iPort, oPort :: P2 -> Diag
iPort = port white
oPort = port black

-- p2 :: (Double,Double) -> P2
-- p2 = P . r2

-- | Arrow from source to sink
(~~>) :: P2 -> P2 -> Diag
src ~~> snk = seg <> h
 where
   -- Line segment
   seg = src ~~ snk
   -- Arrow head
   h =   eqTriangle (sqrt 3 / 2)        -- circum-diameter 1
       # fc black
       # rotate (30 :: Deg)             -- point right
       # translate (r2 (-0.5, 0))       -- tip at origin
       # scale 0.075
       # scaleY 0.75                    -- narrower
       # rotate (angle (snk .-. src))
       # translate (unPoint snk)
   angle v = Rad (uncurry (flip atan2) (unr2 v))

-- | Generate output picture
class OutDiag a where
  outDiag :: a -> Diag

instance OutDiag P2 where outDiag = oPort
instance (OutDiag a, OutDiag b) => OutDiag (a,b) where
  outDiag (a,b) = outDiag a <> outDiag b

-- | Render and return output
output :: OutDiag a => DWriter a a
output = proc o -> do write   -< freeze (outDiag o)
                      returnA -< o

-- The 'freeze' causes line widths to scale under transformation. I like that it
-- maintains visual balance within boxes & arrows. Doubting, though. And where
-- to put the freeze, so that it's simple & dependable?

-- Do I really want bc to generate the arrow? I'll also need it elsewhere.
-- Could instead move into a composition operation. Probably not into (.), since
-- id must be an identity. Perhaps add arrows in (.) but customize for
-- separation, degenerating smoothly to no arrow when source & sink points
-- coincide (as in id). Need more noodling and experimentation.
-- 
-- If I move the arrow generation into a composition step, then I guess I'd want
-- to change the data type from an input->output function to an input,output
-- pair. Inversion becomes simply a swap, and transformation wouldn't need
-- conjugation. The pictures wouldn't need artificial dangling inputs.
-- 
-- Oh, hm. *Where* would the identity circuit be? Wherever I put it, if I
-- compose it with a circuit somewhere else, I'll get an arrow drawn, which
-- breaks identity laws.

-- | Generate input picture from source and sink, including arrow.
class InDiag a where
  (~*>) :: a -> a -> Diag

instance InDiag P2 where
  src ~*> snk = src ~~> snk <> iPort snk

instance (InDiag a, InDiag b) => InDiag (a,b) where
  (a,b) ~*> (a',b') = (a ~*> a') <> (b ~*> b')

-- | Primitive circuit component with inputs & outputs
prim :: (InDiag (Ports a), OutDiag (Ports b)) =>
        Diag -> Ports a -> Ports b -> a :> b
prim d a b = TF $
  proc src -> do
    write  -< freeze (d <> (src ~*> a))
    output -< b


{--------------------------------------------------------------------
    Belongs elsewhere (orphans)
--------------------------------------------------------------------}

-- Needed for Transformable instance
type instance V (WriterArrow w (~>) a b) = V (a ~> (b,w))

instance (Arrow (~>), Monoid w, Transformable (a ~> (b,w))) =>
         Transformable (WriterArrow w (~>) a b) where
  transform tr = WriterArrow . transform tr  . runWriter

--     Constraint is no smaller than the instance head
--       in the constraint: Transformable ((~>) a (b, w))
--     (Use -XUndecidableInstances to permit this)
--     In the instance declaration for `Transformable (WriterArrow w ~> a b)'

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- | Draw circuit, given input positions
draw :: Ports a -> a :> b -> IO (Ports b)
draw a q = defaultMain (d # pad 1.1) >> return b
 where
   (b,d) = runPixie q a

-- | @Bool -> Bool@ circuit
type BB = Bool :> Bool

-- Draw with input from (-0.5,0)
drawBB :: BB -> IO P2
drawBB = draw (p2 (-0.5,0))

-- 'BB' with input on the left and output on the right and given width and
-- height.
bb :: Double -> Double -> BB
bb w h = prim (rect w h) (p2 (-w/2,0)) (p2 (w/2,0))

t4 :: IO P2
t4 = draw (p2 (-0.75,0.5)) (bb 0.5 1)

t5from :: R2 -> IO P2
t5from v = draw (p2 (-0.75,0.5)) (translate v (bb 0.5 1))

t5a, t5b :: IO P2
t5a = t5from (r2 ( 0.5,0))
t5b = t5from (r2 (-1.0,0))

-- Use drawBB with the following examples.

bb1, bb2 :: BB
bb1 = bb 0.5 0.75
bb2 = bb 0.75 0.5

bbs1 :: BB
bbs1 = bb1 -|- bb2 -|- bb1 -|- bb2 -|- bb1

bbs2 :: BB
bbs2 = bb1 -|/ bb2 -|\ bb1 -|\ bb2 -|/ bb1 -|- bb2

bbs3 :: BB
bbs3 = b -|* b -|* b -|* b -|* b -|* b
 where
   b = bb 0.75 0.75

bbs4 :: BB
bbs4 = b -|& b -|& b -|& b -|& b -|& b
 where
   b = bb 0.75 0.75

{--------------------------------------------------------------------
    One-bit full adder
--------------------------------------------------------------------}

-- | Take a a carry-in from the left and pair of addend bits from above, and
-- yield a sum bit below and a carry-out bit on the right.
addB :: (Bool,(Bool,Bool)) :> (Bool,Bool)
addB = prim unitSquare
         (p2 (-1/2, 0), (p2 (-1/6, 1/2), p2 ( 1/6, 1/2)))
         (p2 (0,-1/2), p2 (1/2, 0))

drawAddB :: (Bool,(Bool,Bool)) :> (Bool,Bool) -> IO (P2,P2)
drawAddB = draw (p2 (-1,0),(p2 (-1/6,1), p2 ( 1/6,1)))
