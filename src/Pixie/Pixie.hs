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
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

import Control.Compose ((<~)) -- TypeCompose

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

type PTS v c = TS c (Point v)

-- type Pixie' e v m a b = PTS v (Decoding a) -> (PTS v (Decoding b), QDiagram e v m)

-- | Circuit picture arrow in its most general form. See also 'Pixie'.
type Pixie e v m = Strip (TSFun (Point v) (WriterArrow (QDiagram e v m) (->)))

-- TODO: Maybe move e to after v & m for convenient partial application.

type DecodeP v c = (Decode (PTS v c), Decoding (PTS v c) ~ PTS v (Decoding c))
type DecodePP v a b = (DecodeP v a, DecodeP v b)

runPixie :: ( Semigroup m, Floating (Scalar v), Ord (Scalar v)
            , InnerSpace v, HasLinearMap v ) =>
            DecodePP v a b =>
            Pixie e v m a b -> PTS v a -> (PTS v b, QDiagram e v m)
runPixie q a = first encode $ (runWriter.runTSFun.unA) q (decode a)

-- | Diagrams containing paths (renderable wherever paths are).
type Diag' v m = forall e. Renderable (Path v) e => QDiagram e v m

-- | Specialization of 'Diag''
type Diag = Diag' R2 Any

-- type Diag = forall e. Renderable (Path R2) e => QDiagram e R2 Any

-- | Diagram writer
type DWriter a b = 
  forall e. Renderable (Path R2) e => WriterArrow (QDiagram e R2 Any) (->) a b

-- | Circuit picture with typed inputs & outputs
type a :> b = forall e. Renderable (Path R2) e => Pixie e R2 Any a b

-- | Input or output port collection. Currently just a position per component.
type Ports a = TS a P2

-- | Ports of decoding
type DPorts a = Ports (Decoding a)

-- Inside a '(:>)'
-- type a :>: b = DWriter (DPorts a) (DPorts b)

type a :>: b = DWriter (Decoding (Ports a)) (Decoding (Ports b))

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
class OutDiag a where outDiag :: a -> Diag

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
class InDiag a where (~*>) :: a -> a -> Diag

instance InDiag P2 where
  src ~*> snk = src ~~> snk <> iPort snk

instance (InDiag a, InDiag b) => InDiag (a,b) where
  (a,b) ~*> (a',b') = (a ~*> a') <> (b ~*> b')

type Diags a b = (DecodePP R2 a b, InDiag (DPorts a), OutDiag (DPorts b))

-- Add Strip and TSFun wrappers
stf :: TSFunX x (~>) (Decoding a) (Decoding b) -> Strip (TSFun x (~>)) a b
stf = A . TF

-- | Generalized 'prim' with ports computed from source.
primF :: Diags a b => (Ports a -> (Diag, Ports a, Ports b)) -> a :> b
primF f = stf $
  proc src -> do
    let (d,a,b) = f (encode src)
    write  -< freeze (d <> (src ~*> decode a))
    output -< decode b

-- Some constraint shorthands
type Transfo   x   = (Transformable x, V x ~ R2)
type PTransfo  c   = Transfo (Ports c)
type PTransfos a b = (PTransfo a, PTransfo b)

-- | 'prim' with delta computed from input ports
primDel :: forall a b. (Diags a b, PTransfos a b) =>
           (Ports a -> R2) -> Diag -> Ports a -> Ports b -> a :> b
primDel del diag a b =
  primF (\ w -> let f :: forall t. Transfo t => Unop t
                    f = translate (del w) in 
                  (f diag, f a, f b))

-- | Primitive circuit component with inputs & outputs
prim :: Diags a b => Diag -> Ports a -> Ports b -> a :> b
prim d a b = primF (const (d,a,b))

-- prim :: (Diags a b, PTransfos a b) => Diag -> Ports a -> Ports b -> a :> b
-- prim = primDel (const zeroV)

{--------------------------------------------------------------------
    Belongs elsewhere (orphans)
--------------------------------------------------------------------}

-- Needed for Transformable instance
type instance V (WriterArrow w (~>) a b) = V (a ~> (b,w))

instance (Arrow (~>), Monoid w, Transformable (a ~> (b,w))) =>
         Transformable (WriterArrow w (~>) a b) where
  transform = inWriter . transform

-- UndecidableInstances: Constraint is no smaller than the instance head

type instance V (Vec n t) = V t

instance Transformable t => Transformable (Vec n t) where
  transform = fmap . transform

type instance V (Strip (~>) a b) = V (StripX (~>) a b)

instance (HasLinearMap (V (StripX (~>) a b)), Transformable (StripX (~>) a b))
      => Transformable (Strip (~>) a b) where
  transform = inA . transform

DecodePrim(Point v)

TransInstances(lift,WriterArrow w,(Arrow (~>), Monoid w))

-- newtype WriterArrow w a b c = WriterArrow (a b (c, w))

inWriter :: (Arrow a, Monoid w) =>
            (a b (c, w) -> a' b' (c', w'))
         -> (WriterArrow w a b c -> WriterArrow w' a' b' c')
inWriter = WriterArrow <~ runWriter


{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- | Output a diagram in SVG, and convert to PDF. Assumes ImageMagick is
-- installed, including the @convert@ program.
out :: Diagram SVG R2 -> IO ()
out d = do defaultMain (d # pad 1.1)
           void (system "convert output.svg output.pdf")

-- | Draw circuit, given input positions
draw :: DecodePP R2 a b => Ports a -> a :> b -> IO ()
draw a q = out (snd (runPixie q a))

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

type A = Bool -- Addend bit
type C = Bool -- Carry bit
type R = Bool -- Sum (result) bit

type A2  = A  :* A                      -- Addends
type A2C = A2 :* C                      -- Addends and carry
type CS  = C  :* R                      -- Carry and sum

-- | Take a a carry-in from the left and pair of addend bits from above, and
-- yield a sum bit below and a carry-out bit on the right.
addB :: A2C :> CS
addB = prim unitSquare
         ((p2 (-1/6, 1/2), p2 (1/6, 1/2)) , p2 (-1/2, 0))
         (p2 (1/2, 0)                     , p2 (0,-1/2))

drawAddB :: A2C :> CS -> IO ()
drawAddB = draw ((p2 (-1/6,1), p2 (1/6,1)), p2 (-1,0))

addBDel :: A2C :> CS
addBDel = primDel
            (\ (_,P c) -> c + r2 (5/6,0))
            unitSquare
            ((p2 (-1/6, 1/2), p2 (1/6, 1/2)) , p2 (-1/2, 0))
            (p2 (1/2, 0)                     , p2 (0,-1/2))


{--------------------------------------------------------------------
    Carry ripple adder
--------------------------------------------------------------------}

type A2sC n = Vec n A2 :* C               -- Addends and carry
type CSs n  = C :* Vec n R                -- Carry and sums


addVIns :: IsNat n => Ports (A2sC n)
addVIns = (src <$> iota, p2 (delta,0))
 where
   delta = 1/2 - addSep
   src :: Int -> Ports A2
   src i = translateX dx (p2 (-1/6,-delta), p2 (1/6,-delta))
     where
       dx = addSep * fromIntegral i

-- Spacing between adder boxes
addSep :: Double
addSep = 4/3

type AddV n = A2sC n :> CSs n

-- consV :: (a, Vec n a) -> Vec (S n) a
-- consV = uncurry (:<)

-- unConsV :: Vec (S n) a -> (a, Vec n a)
-- unConsV (a :< as) = (a,as)

-- addV :: IsNat n => AddV n  -- , DecodeP R2 (Vec n B)
-- addV = stf (addV' nat)

-- addV' :: Nat n -> (Vec n B2,B) :>: (Vec n B,B)
-- addV' = undefined

-- addV' Zero = proc (_,ci) -> returnA -< (ZVec,ci)
-- addV' (Succ n) = proc (unConsV -> (p, ps'), ci) -> do
--                     (s ,co ) <- runTSFun addB -< (p,ci)
--                     (ss,co') <- addV' n       -< (ps',co)
--                     returnA -< (s :< ss, co')

-- View pattern to avoid
-- 
--     Proc patterns cannot use existential or GADT data constructors

-- addV :: IsNat n => AddV' n  -- , DecodeP R2 (Vec n B)
-- addV = addV' nat

-- addV' :: Nat n -> AddV n
-- addV' Zero     = proc (_,ci) -> returnA -< (ZVec,ci)
-- addV' (Succ n) = proc (unConsV -> (p, ps'), ci) -> do
--                     (s ,co ) <- addB    -< (p,ci)
--                     (ss,co') <- addV' n -< (ps',co)
--                     returnA -< (s :< ss, co')

-- type PTS v c = TS c (Point v)
-- type DecodeP v c = (Decode (PTS v c), Decoding (PTS v c) ~ PTS v (Decoding c))
-- type DecodePP v a b = (DecodeP v a, DecodeP v b)

drawAddV :: (IsNat n, DecodePP R2 (A2sC n) (CSs n)) =>
            AddV n -> IO ()
drawAddV = draw addVIns

-- For instance,
-- 
--   drawAddV (addV :: AddV N6)
-- 
--   *** Exception: arr: not defined on Strip (~>)
--
-- Sadly, arrow notation desugaring uses arr, which I cannot implement on Strip,
-- we can't use do notation with (:>). This problem isn't fundamental, since
-- the desugaring could use methods from HasPair and HasSum instead.

-- addV' :: Nat n -> AddV n
-- addV' Zero     = swapP . second (toVecZ . unVecZ)
-- addV' (Succ n) = 
--   undefined . first addB . lassocP . second unVecS

--  first toVecS . lassocP . second (addV' n) . rassocP . first addB . lassocP . second unVecS

--  first toVecS . lassocP . second (addV' n) . rassocP . first addB . lassocP . second unVecS

-- second unVecS    :: (B, Vec (S n) BB)   :> (B, (BB, Vec n BB))
-- lassocP          :: (B, (BB, Vec n BB)) :> ((B, BB), Vec n BB)
-- first addB       :: ((B, BB), Vec n BB) :> ((B, B), Vec n BB)
-- rassocP          :: ((B, B), Vec n BB)  :> (B, (B, Vec n BB))
-- second (addV' n) :: (B, (B, Vec n BB))  :> (B, (Vec n B, B))
-- lassocP          :: (B, (Vec n B, B))   :> ((B, Vec n B), B)
-- first toVecS     :: ((B, Vec n B), B)   :> (Vec (S n) B, B)

-- TODO: swap results in addB

-- addV' Zero     = proc (zvec,ci) -> returnA -< (ZVec,ci)
-- addV' (Succ n) = proc (unConsV -> (p, ps'), ci) -> do
--                     (co ,s ) <- addB    -< (p  ,ci)
--                     (co',ss) <- addV' n -< (ps',co)
--                     returnA -< (co', s :< ss)

{-

-- List version

addL :: ([B2],B) :> ([B],B)
addL = TF addL'

addL' :: ([B2],B) :>: ([B],B)
addL' = proc (ps,ci) -> do
          case ps of
            []      -> returnA -< ([],ci)
            (p:ps') -> do (s ,co ) <- runTSFun addB  -< (p,ci)
                          (ss,co') <- translateX addSep addL' -< (ps',co)
                          returnA -< (s:ss, co')

-}

{-
addL :: ([B2],B) :> ([B],B)
addL = proc (ps,ci) -> do
          case ps of
            []      -> returnA -< ([],ci)
            (p:ps') -> do (s ,co ) <- addB -< (p  ,ci)
                          (ss,co') <- addL -< (ps',co)
                          returnA -< (s:ss, co')

drawAddL :: Int -> (B,[B2]) :> ([B],B) -> IO ()
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
runPixieSt = runPixie . runState

-- runPixieSt (StateArrow q) a = runPixie q a

type (:#>) = PixieSt SVG R2 Any C

-- addBS :: ArrowState (~>) =>
--          B2 ~> B
-- addBS = error "addBS: not yet implemented"

addBS :: A2 :#> R
addBS = state (swapP . addBDel)

-- TODO: Add some constraints to addBS

-- addS :: (Traversable t (~>) (~>), ArrowState B (~>)) =>
--         t B2 ~> (t B)
-- addS = traverse addBS

addA :: Traversable t (:#>) => 
        t A2 :#> t R
addA = traverse addBS

-- TODO: Generalize from (:#>) to ArrowState

-- addSV :: ((~>) ~ StateArrow B (-->), t ~ Vec n) =>
--          (ArrowState B (~>), Traversable t (~>)) => 
--          t B2 ~> t B
-- addSV = addA

type AddSV n = Vec n A2 :#> Vec n R

addSV :: -- Traversable (Vec n) (:#>) => 
         -- Alternatively:
         (EncodeF (Vec n) (:#>), Traversable (EncodingF (Vec n)) (:#>)) =>
         AddSV n
addSV = addA

addS4 :: AddSV N4
addS4 = addA

psDiag :: DecodePP R2 a b => Ports (a,C) -> (a :#> b) -> Diagram SVG R2
psDiag a q = snd (runPixieSt q a)

drawAddSV :: (IsNat n, a ~ Vec n A2, DecodePP R2 a b) =>
             (a :#> b) -> IO ()
drawAddSV = out . psDiag addVIns

t :: IO ()
t = drawAddSV (addA :: AddSV N8)
