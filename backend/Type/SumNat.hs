{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Type.SumNat where

import           Data.Constraint                ( (:-)(Sub)
                                                , Constraint
                                                , Dict(Dict)
                                                )
import           Data.Singletons                ( Sing
                                                , SingI(sing)
                                                )
import           Data.Singletons.Prelude        ( (%+) )
import           Data.Singletons.Prelude.List   ( SList(SCons, SNil) )
import           Data.Singletons.TypeLits       ( SNat(SNat)
                                                , withKnownNat
                                                )
import           GHC.TypeNats                   ( type (+)
                                                , KnownNat
                                                , Nat
                                                )

type family SumNat (ns :: [Nat]) :: Nat where
    SumNat '[] = 0
    SumNat (n ': ns) = n + SumNat ns

sumSumNat :: Sing ns -> Sing (SumNat ns)
sumSumNat SNil         = SNat
sumSumNat (SCons n ns) = withKnownNat n sing %+ sumSumNat ns

allSumNatKnownNat :: Sing ns -> (() :: Constraint) :- KnownNat (SumNat ns)
allSumNatKnownNat ns = withKnownNat (sumSumNat ns) (Sub Dict)
