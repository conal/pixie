{-# LANGUAGE Arrows, GADTs, TypeOperators, TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall #-}

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

-- | Circuit picture with typed inputs & outputs
type a :> b = forall e. Renderable (Path R2) e => Pixie e R2 Any a b

-- | Input or output port collection. Currently just a position per component.
type Ports a = TS a P2

-- | Draw circuit, given input positions
draw :: a :> b -> Ports a -> IO (Ports b)
draw q a = defaultMain (d # pad 1.1) >> return b
 where
   (b,d) = runPixie q a

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

-- | @Bool -> Bool@ circuit
type BC = Bool :> Bool

-- 'BC' with input on the left and output on the right and given width and
-- height.
bc :: Double -> Double -> BC
bc w h = TF $
  proc src -> do
    let -- input & output ports
        ip = p2 (-0.5*w,0)
        op = p2 ( 0.5*w,0)
    write -< freeze $ (src ~~> ip) <> iPort ip <> oPort op <> rect w h
    returnA -< op

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

t4 :: IO P2
t4 = draw (bc 0.5 1) (p2 (-0.75,0.5))

t5from :: R2 -> IO P2
t5from v = draw (translate v (bc 0.5 1)) (p2 (-0.75,0.5))

t5a, t5b :: IO P2
t5a = t5from (r2 ( 0.5,0))
t5b = t5from (r2 (-1.0,0))

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

-- Draw with input from (-0.5,0)
drawA :: TS a P2 ~ P2 => (a :> b) -> IO (TS b P2)
drawA c = draw c (p2 (-0.5,0))

-- Use drawA with the following examples.

bc1, bc2 :: BC
bc1 = bc 0.5 0.75
bc2 = bc 0.75 0.5

bcs1 :: BC
bcs1 = bc1 -|- bc2 -|- bc1 -|- bc2 -|- bc1

bcs2 :: BC
bcs2 = bc1 -|/ bc2 -|\ bc1 -|\ bc2 -|/ bc1 -|- bc2

bcs3 :: BC
bcs3 = b -|* b -|* b -|* b -|* b -|* b
 where
   b = bc 0.75 0.75

bcs4 :: BC
bcs4 = b -|& b -|& b -|& b -|& b -|& b
 where
   b = bc 0.75 0.75
