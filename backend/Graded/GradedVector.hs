{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Graded.GradedVector where

import           Data.Singletons                ( Sing
                                                , SingI(sing)
                                                )
import           Data.Singletons.Decide         ( (%~)
                                                , Decision(Disproved, Proved)
                                                )
import           Data.Singletons.Prelude        ( (%+) )
import           Data.Singletons.Prelude.List   ( Length
                                                , SList(SCons, SNil)
                                                )
import           Data.Singletons.TypeLits       ( SNat(SNat) )
import           Data.Type.Equality             ( (:~:)(Refl) )
import           Data.Vector.Sized              ( Vector
                                                , head
                                                , knownLength
                                                , tail
                                                )
import           GHC.TypeNats                   ( type (+)
                                                , KnownNat
                                                , Nat
                                                )
import           Graded.Graded                  ( Graded(..)
                                                , withSomeGrad
                                                )
import           Prelude                 hiding ( head
                                                , tail
                                                )
import           Unsafe.Coerce                  ( unsafeCoerce )

--from https://stackoverflow.com/questions/46634706/haskell-singletons-typelits-package

data IsZero (n :: Nat) where
    Zero ::(0 ~ n) => IsZero n
    NonZero ::(m ~ (1 + n)) => IsZero m
deriving instance Show (IsZero n)

isZero :: forall n . Sing n -> IsZero n
isZero n = case n %~ (SNat @0) of
    Proved    Refl -> Zero
    Disproved _    -> unsafeCoerce NonZero

data GradVect (ns :: [Nat]) a where
  GradNil ::GradVect '[] a
  GradCons ::KnownNat n => Graduation a n -> GradVect ns a -> GradVect (n ': ns) a

getLengthSing :: GradVect ns a -> Sing (Length ns)
getLengthSing GradNil         = SNat
getLengthSing (GradCons _ gs) = (SNat :: Sing 1) %+ getLengthSing gs

getNsSing :: GradVect ns a -> Sing ns
getNsSing GradNil         = SNil
getNsSing (GradCons _ ns) = SCons sing $ getNsSing ns

data SomeGradVect n a where
    SomeGradVect ::GradVect ns a -> SomeGradVect (Length ns) a

withSomeGradVect
    :: SomeGradVect n a
    -> (forall ns . (Length ns ~ n) => GradVect ns a -> b)
    -> b
withSomeGradVect (SomeGradVect v) f = f v

append
    :: KnownNat m
    => Graduation a m
    -> SomeGradVect n a
    -> SomeGradVect (1 + n) a
append x (SomeGradVect v) = SomeGradVect $ GradCons x v

appendSome :: Graded a => a -> SomeGradVect n a -> SomeGradVect (1 + n) a
appendSome x (SomeGradVect v) =
    withSomeGrad (toSomeGrad x) (\y -> append y (SomeGradVect v))

toSomeGradVect :: Graded a => Sing n -> Vector n a -> SomeGradVect n a
toSomeGradVect s v = case isZero s of
    Zero    -> SomeGradVect GradNil
    NonZero -> appendSome x $ knownLength xs (toSomeGradVect sing xs)
      where
        x  = head v
        xs = tail v

toList :: Graded a => GradVect ns a -> [a]
toList GradNil         = []
toList (GradCons x xs) = fromGrad x : toList xs
