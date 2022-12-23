{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module RegExp.Capture.Capture where

import Control.Monad.State (StateT (..), mapStateT)
import Data.Bifunctor (first)
import Data.Foldable (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Semiring
  ( Semiring,
    one,
    plus,
    times,
    zero,
  )
import GenMonad.GenMonad
  ( GenMonad
      ( GenMonadConstraint,
        return
      ),
    fmap,
    liftM2,
    (<$>),
    (>=>),
    (>>),
    (>>=),
  )
import Semimodule.Semimodule (Semimodule, leftAction, rightAction)
import Prelude hiding (fmap, return, (<$>), (>>), (>>=))

get :: (GenMonad m, GenMonadConstraint m (s, s)) => StateT s m s
get = StateT $ \s -> return (s, s)

put :: (GenMonad m, GenMonadConstraint m ((), s)) => s -> StateT s m ()
put s = StateT $ \_ -> return ((), s)

modify :: (GenMonad m, GenMonadConstraint m ((), s)) => (s -> s) -> StateT s m ()
modify f = StateT $ \s -> return ((), f s)

-- It is for liftA2 what mapReaderT is for fmap
liftA2StateT ::
  ((s1 -> m1 (a1, s1)) -> (s2 -> m2 (a2, s2)) -> s3 -> m3 (a3, s3)) ->
  StateT s1 m1 a1 ->
  StateT s2 m2 a2 ->
  StateT s3 m3 a3
liftA2StateT f s1 s2 = StateT $ runStateT s1 `f` runStateT s2

data CaptureMonadicRegExp m c a
  = Sum (CaptureMonadicRegExp m c a) (CaptureMonadicRegExp m c a)
  | Conc (CaptureMonadicRegExp m c a) (CaptureMonadicRegExp m c a)
  | Star (CaptureMonadicRegExp m c a)
  | CaptureCurrent (c, Maybe [a]) (CaptureMonadicRegExp m c a)
  | Captured c
  | Atom a
  | Epsilon
  | Empty
  | LeftAction (m ()) (CaptureMonadicRegExp m c a)

deriving instance (Eq (m ()), Eq a, Eq c) => Eq (CaptureMonadicRegExp m c a)

deriving instance (Ord (m ()), Ord a, Ord c) => Ord (CaptureMonadicRegExp m c a)

plus' :: CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a
plus' Empty e = e
plus' e Empty = e
plus' e1 e2 = e1 `Sum` e2

conc' ::
  CaptureMonadicRegExp m c a ->
  CaptureMonadicRegExp m c a ->
  CaptureMonadicRegExp m c a
conc' Empty _ = Empty
conc' _ Empty = Empty
conc' Epsilon e = e
conc' e Epsilon = e
conc' e1 e2 = e1 `Conc` e2

instance Semigroup (CaptureMonadicRegExp m c a) where
  (<>) = plus'

instance Monoid (CaptureMonadicRegExp m c a) where
  mempty = Empty

instance Semiring (CaptureMonadicRegExp m c a) where
  plus = plus'
  times = conc'
  zero = Empty
  one = Epsilon

fromList :: [a] -> CaptureMonadicRegExp m c a
fromList = foldl' (\acc -> conc' acc . Atom) Epsilon

capture :: c -> CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a
capture c = CaptureCurrent (c, Nothing)

(<<+>>) :: CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a
(<<+>>) = Sum

(<<.>>) :: CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a -> CaptureMonadicRegExp m c a
(<<.>>) = Conc

parentheses :: (Show a, Show c, Show (m ())) => CaptureMonadicRegExp m c a -> String
parentheses e@(Atom _) = toString e
parentheses e@(Star _) = toString e
parentheses e = mconcat ["(", toString e, ")"]

toString :: (Show a, Show c, Show (m ())) => CaptureMonadicRegExp m c a -> String
toString Empty = "0"
toString Epsilon = "1"
toString (Atom at) = show at
toString (Captured c) = mconcat ["[", show c, "]"]
toString (CaptureCurrent (c, inv_xs) e) =
  mconcat ["[", show c, ": <", show (reverse <$> inv_xs), ">", toString e, "]"]
toString (Star e) = mconcat [parentheses e, "*"]
toString (Conc e1@(Conc _ _) e2) = mconcat [toString e1, parentheses e2]
toString (Conc e1 e2) = mconcat [parentheses e1, parentheses e2]
toString (Sum e1@(Sum _ _) e2) = mconcat [toString e1, "+", parentheses e2]
toString (Sum e1 e2) = mconcat [parentheses e1, "+", parentheses e2]
toString (LeftAction w e) = mconcat [show w, " *> ", parentheses e]

-- ajouter Bar (E) = E sans epsilon ?
-- pour le cas [1: a*b*].[1 + eps]* ?
-- ou alors considérer que [1: a*b*].[1 + eps]* n'est pas propre ?
nullableProper ::
  ( GenMonadConstraint m1 (m2 (), Map k [a]),
    GenMonadConstraint m2 (),
    GenMonadConstraint m1 (Map k [a], Map k [a]),
    GenMonadConstraint m1 ((), Map k [a]),
    GenMonad m1,
    GenMonad m2,
    Monoid (m2 ()),
    Semiring (m2 ()),
    Ord k,
    Eq a,
    Monoid (m1 (m2 (), Map k [a])),
    Semiring (m1 (m2 (), Map k [a]))
  ) =>
  CaptureMonadicRegExp m2 k a ->
  StateT (Map k [a]) m1 (m2 ())
nullableProper Epsilon = return $ return ()
nullableProper Empty = return mempty
nullableProper (Atom _) = return mempty
nullableProper (Sum e1 e2) =
  liftM2 (<>) (nullableProper e1) (nullableProper e2)
nullableProper (Conc e1 e2) =
  liftM2 times (nullableProper e1) (nullableProper e2)
nullableProper (Star _) = return $ return ()
nullableProper (CaptureCurrent (c, inv_xs) e) =
  modify (Map.insert c xs) >> nullableProper e
  where
    xs = maybe [] reverse inv_xs
nullableProper (Captured c) =
  get >>= \ctxt -> case Map.lookup c ctxt of
    Just [] -> return $ return ()
    _ -> return mempty
nullableProper (LeftAction w e) = (w `times`) <$> nullableProper e

deriveBySymbProper ::
  ( GenMonadConstraint m2 (CaptureMonadicRegExp m1 k a, Map k [a]),
    GenMonadConstraint m2 ((), Map k [a]),
    GenMonadConstraint m2 (Map k [a], Map k [a]),
    GenMonadConstraint m2 (m1 (), Map k [a]),
    GenMonadConstraint m1 (),
    Monoid (m2 (CaptureMonadicRegExp m1 k a, Map k [a])),
    Monoid (m2 (m1 (), Map k [a])),
    Semiring (m2 (m1 (), Map k [a])),
    Monoid (m1 ()),
    GenMonad m2,
    GenMonad m1,
    Ord k,
    Eq a,
    Semimodule (CaptureMonadicRegExp m1 k a) (m2 (CaptureMonadicRegExp m1 k a, Map k [a])),
    Semimodule (m1 ()) (m2 (CaptureMonadicRegExp m1 k a, Map k [a]))
  ) =>
  a ->
  CaptureMonadicRegExp m1 k a ->
  StateT (Map k [a]) m2 (CaptureMonadicRegExp m1 k a)
deriveBySymbProper _ Empty = StateT mempty
deriveBySymbProper _ Epsilon = StateT mempty
deriveBySymbProper a (Atom b)
  | a == b = return Epsilon
  | otherwise = StateT mempty
deriveBySymbProper a (Sum e1 e2) =
  liftA2StateT (<>) (deriveBySymbProper a e1) (deriveBySymbProper a e2)
deriveBySymbProper a (Conc e1 e2) =
  liftA2StateT
    (<>)
    (mapStateT (`rightAction` e2) (deriveBySymbProper a e1))
    ( nullableProper e1
        >>= \w -> mapStateT (w `leftAction`) (deriveBySymbProper a e2)
    )
deriveBySymbProper a estar@(Star e) =
  mapStateT (`rightAction` estar) (deriveBySymbProper a e)
deriveBySymbProper at (LeftAction w e) =
  mapStateT (w `leftAction`) $ deriveBySymbProper at e
deriveBySymbProper at (CaptureCurrent (c, inv_xs) e) =
  CaptureCurrent (c, inv_xs') <$> deriveBySymbProper at e
  where
    inv_xs' = case inv_xs of
      Nothing -> Just [at]
      Just xs -> Just (at : xs)
deriveBySymbProper at (Captured c) =
  get >>= \ctxt ->
    case c `Map.lookup` ctxt of
      Nothing -> StateT $ const mempty
      Just w -> deriveBySymbProper at $ fromList w

deriveByWordProper ::
  ( GenMonadConstraint
      m2
      (CaptureMonadicRegExp m1 k a, Map k [a]),
    GenMonadConstraint m2 ((), Map k [a]),
    GenMonadConstraint m2 (Map k [a], Map k [a]),
    GenMonadConstraint m2 (m1 (), Map k [a]),
    GenMonadConstraint m1 (),
    Monoid (m2 (m1 (), Map k [a])),
    Monoid (m1 ()),
    Semiring (m2 (m1 (), Map k [a])),
    GenMonad m2,
    GenMonad m1,
    Ord k,
    Eq a,
    Semimodule (CaptureMonadicRegExp m1 k a) (m2 (CaptureMonadicRegExp m1 k a, Map k [a])),
    Semimodule (m1 ()) (m2 (CaptureMonadicRegExp m1 k a, Map k [a]))
  ) =>
  [a] ->
  CaptureMonadicRegExp m1 k a ->
  StateT (Map k [a]) m2 (CaptureMonadicRegExp m1 k a)
deriveByWordProper = foldl' (\acc a -> acc >=> deriveBySymbProper a) return
