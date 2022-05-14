{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Graded.GradedModuleOfLinComb where

import           Control.Arrow                  ( Arrow(first) )
import           Data.Coerce                    ( coerce )
import qualified Data.Map                      as Map
import           Data.Semiring                  ( Semiring(one)
                                                , plus
                                                , times
                                                , zero
                                                )
import           Data.Singletons                ( Sing
                                                , SingI(sing)
                                                )
import           Data.Singletons.Prelude        ( (%+) )
import           Data.Singletons.TypeLits       ( SNat(SNat) )
import           Data.Vector.Sized             as V
                                                ( Vector
                                                , cons
                                                , empty
                                                , head
                                                , tail
                                                )
import           GenMonad.GenMonad             as G
                                                ( GenMonad
                                                  ( (>>=)
                                                  , GenMonadConstraint
                                                  , return
                                                  )
                                                )
import           Graded.GradedFun               ( Graduation(GradFun) )
import           Graded.GradedModule            ( GradedModule(..)
                                                , combineToModule
                                                )
import           LinComb.LinComb4              as L4
                                                ( LinComb(LinComb)
                                                , toList
                                                )
import qualified LinComb.LinComb4              as L4
                                                ( toScalar )
import qualified Prelude                       as P
import           Prelude                 hiding ( (++)
                                                , drop
                                                , head
                                                , last
                                                , splitAt
                                                , tail
                                                , take
                                                , unzip
                                                )
import           Test.QuickCheck                ( Arbitrary(arbitrary) )
import           ToString.ToString              ( ToString
                                                  ( toHTMLString
                                                  , toString
                                                  )
                                                )

newtype FunctorCompo f g a = FunctorCompo {run :: f (g a)}
  deriving (Eq, Ord)
  deriving newtype (Show, Semigroup, Monoid, Semiring)

instance {-# OVERLAPS #-} ToString (f (g a)) => ToString (FunctorCompo f g a) where
  toString (FunctorCompo c) = toString c
  toHTMLString (FunctorCompo c) = toHTMLString c

class IsReducible f g where

    reduce :: f (g a) -> f a

instance (IsReducible f g, GenMonad f, GenMonad g) => GenMonad (FunctorCompo f g) where

  type GenMonadConstraint (FunctorCompo f g) val
    = ( GenMonadConstraint f val
      , GenMonadConstraint g val
      , GenMonadConstraint f (g val)
      )

  m >>= f =
    FunctorCompo
      $     reduce ((coerce :: FunctorCompo f g a -> f (g a)) m)
      G.>>= (coerce . f)

  return = FunctorCompo . G.return . G.return

withMod
  :: (Semiring t, ToString t) => (a, t) -> GradedModule t a -> GradedModule t a
withMod (e, w) (GradMod (GradFun s f) (v :: Vector n a1)) =
  case (SNat :: Sing 1) %+ (SNat :: Sing n) of
    SNat ->
      GradMod
          (GradFun (toString w P.++ "|" P.++ s)
                   (\v' -> (w `times` head v') `plus` f (tail v'))
          )
        $      e
        `cons` v

toFunAndVect :: (Semiring t, ToString t) => [(a, t)] -> GradedModule t a
toFunAndVect []            = GradMod (GradFun "" (const zero)) empty
toFunAndVect ((e, w) : xs) = withMod (e, w) $ toFunAndVect xs

toGradedModule
  :: (Semiring t, ToString t, Eq t) => LinComb t a -> GradedModule t a
toGradedModule l@(LinComb m) = case L4.toList l of
  [(x, w)] | w == one -> G.return x
  _                   -> toFunAndVect $ Map.toList m

instance (Semiring b, ToString b, Eq b) => IsReducible (GradedModule b) (LinComb b) where

  reduce (GradMod f v) = combineToModule sing f $ Prelude.fmap toGradedModule v

newtype GradedModuleOfLinComb b a = Grd (FunctorCompo (GradedModule b) (LinComb b) a)
  deriving newtype (Semigroup, Monoid, Semiring)
deriving instance (Eq (LinComb b a)) => Eq (GradedModuleOfLinComb b a)
deriving instance (Ord (LinComb b a)) => Ord (GradedModuleOfLinComb b a)

instance {-# OVERLAPS #-} (Semiring b, Eq b, ToString b, ToString a) => ToString (GradedModuleOfLinComb b a) where
  toString (Grd g) = toString g
  toHTMLString (Grd g) = toHTMLString g

instance (Semiring b, ToString b, Eq b, GenMonad (GradedModule b), GenMonad (LinComb b)) => GenMonad (GradedModuleOfLinComb b) where

  type GenMonadConstraint (GradedModuleOfLinComb b) val
    = GenMonadConstraint (FunctorCompo (GradedModule b) (LinComb b)) val

  Grd m >>= f = Grd (m G.>>= ((\(Grd x) -> x) . f))

  return = Grd . G.return

fromGradedModule
  :: (Semiring t, Ord a, Ord t) => GradedModule t a -> GradedModuleOfLinComb t a
fromGradedModule (GradMod f v) =
  Grd $ FunctorCompo $ GradMod f $ Prelude.fmap G.return v

fromScalar :: ToString t => t -> GradedModuleOfLinComb t ()
fromScalar w =
  Grd $ FunctorCompo $ GradMod (GradFun (toString w) (const w)) empty

toScalar :: Semiring t => GradedModuleOfLinComb t () -> t
toScalar (Grd (FunctorCompo (GradMod (GradFun _ f) v))) =
  f $ Prelude.fmap L4.toScalar v

instance {-# OVERLAPPING #-}  (Semiring t, Eq t) => Eq (GradedModuleOfLinComb t ()) where
  g == g' = toScalar g == toScalar g'

instance (ToString b, Arbitrary b) => Arbitrary (GradedModuleOfLinComb b ()) where
  arbitrary = fromScalar <$> arbitrary

instance (Show t, Read t) => Read (GradedModuleOfLinComb t ()) where
  readsPrec n s = first fromScalar <$> readsPrec n s

instance (Num (LinComb weight ()), ToString weight, Num weight, Semiring weight) => Num (GradedModuleOfLinComb weight ()) where
  x + y = fromScalar $ toScalar x + toScalar y
  x * y = fromScalar $ toScalar x * toScalar y
  abs         = fromScalar . abs . toScalar
  signum      = fromScalar . signum . toScalar
  fromInteger = fromScalar . fromInteger
  negate      = fromScalar . negate . toScalar

instance (Semiring weight, Fractional weight, ToString weight) => Fractional (GradedModuleOfLinComb weight ()) where
  fromRational r = fromScalar $ fromRational r
  l1 / l2 = fromScalar $ toScalar l1 / toScalar l2

instance (Semiring weight, Floating weight, ToString weight) => Floating (GradedModuleOfLinComb weight ()) where
  pi = fromScalar pi
  exp l = fromScalar $ exp $ toScalar l
  log l = fromScalar $ log $ toScalar l
  sin l = fromScalar $ sin $ toScalar l
  cos l = fromScalar $ cos $ toScalar l
  asin l = fromScalar $ asin $ toScalar l
  acos l = fromScalar $ acos $ toScalar l
  atan l = fromScalar $ atan $ toScalar l
  sinh l = fromScalar $ sinh $ toScalar l
  cosh l = fromScalar $ cosh $ toScalar l
  asinh l = fromScalar $ asinh $ toScalar l
  acosh l = fromScalar $ acosh $ toScalar l
  atanh l = fromScalar $ atanh $ toScalar l
