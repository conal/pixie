{-# LANGUAGE Arrows, GADTs, TypeOperators, TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
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

import Prelude hiding (id,(.),fst,snd,const)

import Control.Monad (void)
import Control.Category
import Control.Arrow
import Control.Arrow.Operations (ArrowWriter(..)) -- ,ArrowState(..)
import Control.Arrow.Transformer (lift)
import Control.Arrow.Transformer.Writer
-- import Control.Arrow.Transformer.State
import System.Process (system)

import TypeUnary.Vec

import Data.AffineSpace.Point

import Diagrams.Prelude
import Diagrams.Backend.SVG
import Diagrams.Backend.SVG.CmdLine

import CatSynth.Misc (Unop)
import CatSynth.Decode (EncodingF,EncodeF(..),Decoding,Decode(..))
import CatSynth.Traversable
import CatSynth.Has
import CatSynth.StripTypes
import CatSynth.Control.Arrow.Transformer.State

import Pixie.TSFunTF -- or TSFunGadt

-- For now, but remove the WriterArrow orphan later
#include "CatSynth/Has-inc.hs"
#include "CatSynth/Decode-inc.hs"

-- type Pins v a = TS a (Point v)
--
-- type Pixie' e v m a b = Pins v a -> (Pins b v, QDiagram e v m)

-- | Circuit picture arrow in its most general form. See also 'Pixie'.
type Pixie e v m = Strip (TSFun (Point v) (WriterArrow (QDiagram e v m) (->)))

-- TODO: Move e to after v & m for convenient partial application.

type DecodeP v c = ( Decode (TS c (Point v))
                   , Decoding (TS c (Point v)) ~ TS (Decoding c) (Point v) )
type DecodePP v a b = (DecodeP v a, DecodeP v b)

runPixie :: ( Semigroup m, Floating (Scalar v), Ord (Scalar v)
            , InnerSpace v, HasLinearMap v ) =>
            DecodePP v a b =>
            Pixie e v m a b -> TS a (Point v) -> (TS b (Point v), QDiagram e v m)
runPixie q a = first encode $ (runWriter.runTSFun.unA) q (decode a)

-- | Diagrams containing paths (renderable wherever paths are).
type Diag' v m = forall e. Renderable (Path v) e => QDiagram e v m

-- | Specialization of 'Diag''
type Diag = Diag' R2 Any

-- type Diag = forall e. Renderable (Path R2) e => QDiagram e R2 Any

-- | Diagram writer
type DWriter a b = 
  forall e. Renderable (Path R2) e => WriterArrow (QDiagram e R2 Any) (->) a b

-- -- Alternative. Requires ImpredicativeTypes. Is that forall type a Monoid?
-- type DWriter' = 
--   WriterArrow (forall e. Renderable (Path R2) e => QDiagram e R2 Any) (->)

-- | Circuit picture with typed inputs & outputs
type a :> b = forall e. Renderable (Path R2) e => Pixie e R2 Any a b

-- Inside a '(:>)'
type a :>: b = DWriter (Decoding (Ports a)) (Decoding (Ports b))

-- -- Alternative
-- type (:>:) = TSFun P2 DWriter'

-- | Input or output port collection. Currently just a position per component.
type Ports a = TS a P2

-- | Ports of decoding
type DPorts a = Ports (Decoding a)

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

-- (~+>) :: (AdditiveGroup a, InDiag a) => a -> a -> Diag
-- src ~+> snk = src ~*> (src ^+^ snk)

type Diags a b = (DecodePP R2 a b, InDiag (DPorts a), OutDiag (DPorts b))

-- | Generalized 'prim' with ports computed from source.
primF :: Diags a b =>
         (Ports a -> (Diag, Ports a, Ports b)) -> a :> b
primF f = A $ TF $
  proc src -> do
    let (d,a,b) = f (encode src)
    write  -< freeze (d <> (src ~*> decode a))
    output -< decode b

-- | Primitive circuit component with inputs & outputs
prim :: Diags a b =>
        Diag -> Ports a -> Ports b -> a :> b
prim d a b = primF (const (d,a,b))

type Transfo c = (Transformable (Ports c), V (Ports c) ~ R2)
type Transfos a b = (Transfo a, Transfo b)

primDel :: forall a b. (Diags a b, Transfos a b) =>
           (Ports a -> R2) -> Diag -> Ports a -> Ports b -> a :> b
primDel del diag a b =
  primF (\ w -> let f :: forall t. (Transformable t, V t ~ R2) => Unop t
                    f = translate (del w) in 
                  (f diag, f a, f b))
 
{--------------------------------------------------------------------
    Belongs elsewhere (orphans)
--------------------------------------------------------------------}

-- Needed for Transformable instance
type instance V (WriterArrow w (~>) a b) = V (a ~> (b,w))

instance (Arrow (~>), Monoid w, Transformable (a ~> (b,w))) =>
         Transformable (WriterArrow w (~>) a b) where
  transform tr = WriterArrow . transform tr  . runWriter
  -- SEC-style:
  -- transform = inWriter . transform

--     Constraint is no smaller than the instance head
--       in the constraint: Transformable ((~>) a (b, w))
--     (Use -XUndecidableInstances to permit this)
--     In the instance declaration for `Transformable (WriterArrow w ~> a b)'

type instance V (Vec n t) = V t

instance Transformable t => Transformable (Vec n t) where
  transform xf = fmap (transform xf)
  -- transform = fmap . transform

type instance V (Strip (~>) a b) = V (StripX (~>) a b)

instance (HasLinearMap (V (StripX (~>) a b)), Transformable (StripX (~>) a b))
      => Transformable (Strip (~>) a b) where
  transform tr = inA (transform tr)
  -- transform = inA . transform

-- type instance Decoding (Point v) = Decoding v
-- instance Decode v => Decode (Point v) where
--   decode = decode . unPoint
--   encode = Point . encode

-- type instance Decoding R2 = (Double,Double)
-- instance Decode R2 where
--   encode = r2
--   decode = unr2

-- type instance Decoding (Point v) = Point v
-- instance Category ar => Decode ar (Point v) where
--   decode = id
--   encode = id

DecodePrim(Point v)

TransInstances(lift,WriterArrow w,(Arrow (~>), Monoid w))


{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- | Draw circuit, given input positions
draw :: DecodePP R2 a b =>
        Ports a -> a :> b -> IO ()
draw a q = do defaultMain (d # pad 1.1)
              void (system "convert output.svg output.pdf")
 where
   (_,d) = runPixie q a

-- | @Bool -> Bool@ circuit
type BB = Bool :> Bool

-- Draw with input from (-0.5,0)
drawBB :: BB -> IO ()
drawBB = draw (p2 (-0.5,0))

-- | 'BB' with input on the left and output on the right and given
-- width and height.
bb :: Double -> Double -> BB
bb w h = prim (rect w h) (p2 (-w/2,0)) (p2 (w/2,0))

t4 :: IO ()
t4 = draw (p2 (-0.75,0.5)) (bb 0.5 1)

t5from :: R2 -> IO ()
t5from v = draw (p2 (-0.75,0.5)) (translate v (bb 0.5 1))

t5a, t5b :: IO ()
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
addB :: ((Bool,Bool),Bool) :> (Bool,Bool)
addB = prim unitSquare
         ((p2 (-1/6, 1/2), p2 (1/6, 1/2)) , p2 (-1/2, 0))
         (p2 (0,-1/2)                     , p2 (1/2, 0))

drawAddB :: ((Bool,Bool),Bool) :> (Bool,Bool) -> IO ()
drawAddB = draw ((p2 (-1/6,1), p2 (1/6,1)), p2 (-1,0))

-- primDel :: forall a b. (Diags a b, Transfos a b) =>
--            (Ports a -> R2) -> Diag -> Ports a -> Ports b -> a :> b

addBDel :: ((Bool,Bool),Bool) :> (Bool,Bool)
addBDel = primDel
            (\ (_,P c) -> c + r2 (5/6,0))
            unitSquare
            ((p2 (-1/6, 1/2), p2 (1/6, 1/2)) , p2 (-1/2, 0))
            (p2 (0,-1/2)                     , p2 (1/2, 0))


{--------------------------------------------------------------------
    Carry ripple adder
--------------------------------------------------------------------}

addVIns :: IsNat n => Ports (Vec n (Bool,Bool),Bool)
addVIns = (src <$> iota, p2 (delta,0))
 where
   delta = 1/2 - addSep
   src :: Int -> (P2,P2)
   src i = translateX dx (p2 (-1/6,-delta), p2 (1/6,-delta))
     where
       dx = addSep * fromIntegral i

-- Spacing between adder boxes
addSep :: Double
addSep = 4/3

{-

type AddV n = (Vec n (Bool,Bool), Bool) :> (Vec n Bool,Bool)

consV :: (a, Vec n a) -> Vec (S n) a
consV = uncurry (:<)

unConsV :: Vec (S n) a -> (a, Vec n a)
unConsV (a :< as) = (a,as)

addV :: IsNat n => AddV n
addV = A $ TF (addV' nat)

addV' :: Nat n -> (Vec n (Bool,Bool),Bool) :>: (Vec n Bool,Bool)
addV' Zero = proc (_,ci) -> returnA -< (ZVec,ci)
addV' (Succ n) = proc (unConsV -> (p, ps'), ci) -> do
                    (s ,co ) <- runTSFun addB -< (p,ci)
                    (ss,co') <- translateX addSep (addV' n) -< (ps',co)
                    returnA -< (s :< ss, co')

-- View pattern to avoid
-- 
--     Proc patterns cannot use existential or GADT data constructors

drawAddV :: IsNat n => AddV n -> IO ()
drawAddV = draw addVIns

-- For instance,
-- 
--   drawAddV (addV :: AddV N6)

-- List version

addL :: ([(Bool,Bool)],Bool) :> ([Bool],Bool)
addL = TF addL'

addL' :: ([(Bool,Bool)],Bool) :>: ([Bool],Bool)
addL' = proc (ps,ci) -> do
          case ps of
            []      -> returnA -< ([],ci)
            (p:ps') -> do (s ,co ) <- runTSFun addB  -< (p,ci)
                          (ss,co') <- translateX addSep addL' -< (ps',co)
                          returnA -< (s:ss, co')

drawAddL :: Int -> (Bool,[(Bool,Bool)]) :> ([Bool],Bool) -> IO ()
drawAddL n = draw (p2 (delta,0), map src [0..n-1])
 where
   delta = 1/2 - addSep
   src :: Int -> (P2,P2)
   src i = translateX dx (p2 (-1/6,-delta), p2 (1/6,-delta))
     where
       dx = addSep * fromIntegral i

-- TODO: Try another version using take & iterate for summand positions.

-}

{--------------------------------------------------------------------
    Use StateArrow to hide carry-passing.
--------------------------------------------------------------------}

type PixieSt e v m s = StateArrow s (Pixie e v m)

runPixieSt :: ( Semigroup m, Floating (Scalar v), Ord (Scalar v)
              , InnerSpace v, HasLinearMap v ) =>
              (DecodePP v a b, DecodeP v s) =>
              PixieSt e v m s a b -> TS (a,s) (Point v) -> (TS (b,s) (Point v), QDiagram e v m)
runPixieSt (StateArrow q) a = runPixie q a

type (:#>) = PixieSt SVG R2 Any Bool

-- addBS :: ArrowState (~>) =>
--          (Bool,Bool) ~> Bool
-- addBS = error "addBS: not yet implemented"

addBS :: (Bool,Bool) :#> Bool
addBS = state addBDel

-- TODO: Add some constraints to addBS

-- addS :: (Traversable t (~>) (~>), ArrowState Bool (~>)) =>
--         t (Bool,Bool) ~> (t Bool)
-- addS = traverse addBS

addA :: Traversable t (:#>) => 
        t (Bool,Bool) :#> t Bool
addA = traverse addBS

-- TODO: Generalize from (:#>) to ArrowState

-- addSV :: ((~>) ~ StateArrow Bool (-->), t ~ Vec n) =>
--          (ArrowState Bool (~>), Traversable t (~>)) => 
--          t (Bool,Bool) ~> t Bool
-- addSV = addA

type AddSV n = Vec n (Bool,Bool) :#> Vec n Bool

addSV :: -- Traversable (Vec n) (:#>) => 
         -- Alternatively:
         (EncodeF (Vec n) (:#>), Traversable (EncodingF (Vec n)) (:#>)) =>
         AddSV n
addSV = addA

addS4 :: AddSV N4
addS4 = addA

psDiag :: DecodePP R2 a b => Ports (a,Bool) -> (a :#> b) -> Diagram SVG R2
psDiag a q = snd (runPixieSt q a)

drawAddSV :: (IsNat n, a ~ Vec n (Bool, Bool), DecodePP R2 a b) =>
             (a :#> b) -> IO ()
drawAddSV q = defaultMain (psDiag addVIns q # pad 1.1)

t :: IO ()
t = drawAddSV (addA :: AddSV N8)

