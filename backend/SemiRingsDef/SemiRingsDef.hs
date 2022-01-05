{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SemiRingsDef.SemiRingsDef where

import           Common                         ( Castable(..) )
import           Data.Semiring                  ( Add(Add)
                                                , Semiring
                                                )
import           LinComb.LinComb4               ( LinComb )
import           Prelude                       as P
import           Test.QuickCheck                ( Arbitrary )

newtype SR t = SR {get :: t}
  deriving (Eq, Ord, Num, Semiring, Enum, Bounded, Arbitrary, Fractional, Floating)
  deriving newtype (Read, Show)
deriving via (Add t) instance Semiring t => Semigroup (SR t)
deriving via (Add t) instance Semiring t => Monoid (SR t)

deriving instance Real t =>  Real (SR t)
deriving instance RealFrac t =>  RealFrac (SR t)
deriving instance RealFloat t =>  RealFloat (SR t)

instance Castable (SR t) t where
  cast = get

instance Castable t (SR t) where
  cast = SR

instance Semiring t => Castable (LinComb (SR t) ()) t where
  cast = cast . (cast :: LinComb (SR t) () -> SR t)

instance Castable t (LinComb (SR t) ()) where
  cast = cast . (cast :: t -> SR t)

