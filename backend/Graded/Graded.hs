{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}


module Graded.Graded where

import           Data.Proxy                     ( Proxy(..) )
import           GHC.TypeNats                   ( KnownNat
                                                , Nat
                                                )
import           Prelude                 hiding ( head
                                                , last
                                                )

data SomeGrad a where
  SomeGrad ::KnownNat n => Graduation a n -> SomeGrad a

withSomeGrad
  :: SomeGrad a -> (forall n . KnownNat n => Graduation a n -> b) -> b
withSomeGrad (SomeGrad x) f = f x

class Graded t where
    data Graduation t (n :: Nat)
    fromGrad :: KnownNat n =>  Graduation t n -> t
    toSomeGrad :: t -> SomeGrad t

    graduation :: Graduation t n -> Proxy n
    graduation _ = Proxy



