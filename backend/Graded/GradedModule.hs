{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Graded.GradedModule where

import           Control.Arrow                  ( Arrow(first) )
import           Data.Constraint                ( (&&&)
                                                , (:-)(Sub)
                                                , (:=>)(ins)
                                                , Constraint
                                                , Dict(Dict)
                                                )
import           Data.Semiring                  ( Semiring(one)
                                                , plus
                                                , times
                                                , zero
                                                )
import           Data.Singletons                ( Sing
                                                , SingI(sing)
                                                )
import           Data.Singletons.Prelude        ( (%+) )
import           Data.Singletons.Prelude.List   ( Length
                                                , SList(SCons, SNil)
                                                )
import           Data.Singletons.TypeLits       ( SNat(SNat) )
import           Data.Vector.Sized             as V
                                                ( (++)
                                                , Vector
                                                , cons
                                                , drop
                                                , empty
                                                , head
                                                , last
                                                , singleton
                                                , take
                                                , toList
                                                )
import           GHC.TypeNats                   ( KnownNat )
import           GenMonad.GenMonad             as G
                                                ( GenMonad((>>=), return) )
import           Graded.Graded                  ( Graded(..)
                                                , SomeGrad(SomeGrad)
                                                )
import           Graded.GradedFun               ( Compo(..)
                                                , Graduation(GradFun)
                                                , NFun
                                                , allNatsCompo
                                                , (||->)
                                                )
import           Graded.GradedVector            ( GradVect(..)
                                                , getNsSing
                                                , toSomeGradVect
                                                , withSomeGradVect
                                                )
import           Prelude                 hiding ( (++)
                                                , drop
                                                , head
                                                , last
                                                , splitAt
                                                , tail
                                                , take
                                                , unzip
                                                )
import qualified Prelude                       as P
import           Test.QuickCheck                ( Arbitrary(arbitrary) )
import           ToString.ToString              ( ToString
                                                    ( toHTMLString
                                                    , toString
                                                    )
                                                )
import           Type.SumNat                    ( SumNat
                                                , allSumNatKnownNat
                                                )

data GradedModule t a where
     GradMod ::KnownNat n => Graduation (NFun t) n -> Vector n a -> GradedModule t a

instance (Monoid t, Show t) => Semigroup (GradedModule t a) where
    g@(GradMod (GradFun s f) (v :: Vector n a)) <> g'@(GradMod (GradFun s' f') (v' :: Vector
            n1
            a))
        | s == show (mempty :: t)
        = g'
        | s' == show (mempty :: t)
        = g
        | otherwise
        = case (SNat :: Sing n) %+ (SNat :: Sing n1) of
            SNat -> GradMod
                (GradFun ("<" P.++ s P.++ "+" P.++ s' P.++ ">")
                         (\v'' -> f (take v'') <> f' (drop v''))
                )
                (v ++ v')

instance (Show t, Monoid t) => Monoid (GradedModule t a) where
    mempty = GradMod (GradFun (show (mempty :: t)) (const mempty)) empty

instance (Semiring t, Show t) => Semiring (GradedModule t a) where
    plus g@(GradMod (GradFun s f) (v :: Vector n a)) g'@(GradMod (GradFun s' f') (v' :: Vector
            n1
            a))
        | s == show (zero :: t)
        = g'
        | s' == show (zero :: t)
        = g
        | otherwise
        = case (SNat :: Sing n) %+ (SNat :: Sing n1) of
            SNat -> GradMod
                (GradFun ("<" P.++ s P.++ "+" P.++ s' P.++ ">")
                         (\v'' -> f (take v'') `plus` f' (drop v''))
                )
                (v ++ v')
    times g@(GradMod (GradFun s f) (v :: Vector n a)) g'@(GradMod (GradFun s' f') (v' :: Vector
            n1
            a))
        | s == show (zero :: t) || s' == show (zero :: t)
        = zero
        | s == show (one :: t)
        = g'
        | s' == show (one :: t)
        = g
        | otherwise
        = case (SNat :: Sing n) %+ (SNat :: Sing n1) of
            SNat -> GradMod
                (GradFun ("<" P.++ s P.++ "*" P.++ s' P.++ ">")
                         (\v'' -> f (take v'') `times` f' (drop v''))
                )
                (v ++ v')
    zero = GradMod (GradFun (show (zero :: t)) (const zero)) empty
    one  = GradMod (GradFun (show (one :: t)) (const one)) empty

instance Show a => Show (GradedModule t a) where
    show (GradMod f v) = show (fromGrad f) P.++ show (V.toList v)

instance {-# OVERLAPS #-} (ToString a) => ToString (GradedModule t a) where
    toString (GradMod f v) = toString (fromGrad f) P.++ toString (V.toList v)

    toHTMLString (GradMod f v) =
        toHTMLString (fromGrad f) P.++ toHTMLString (V.toList v)

instance Eq a => Eq (GradedModule t a) where
    (GradMod f1 v1) == (GradMod f2 v2) =
        fromGrad f1 == fromGrad f2 && V.toList v1 == V.toList v2

instance (Eq a, Ord a) => Ord (GradedModule t a) where
    compare (GradMod f1 v1) (GradMod f2 v2) =
        case compare (fromGrad f1) (fromGrad f2) of
            EQ -> compare (V.toList v1) (V.toList v2)
            r  -> r

withGradMod
    :: GradedModule t a
    -> (forall n . Graduation (NFun t) n -> Vector n a -> b)
    -> b
withGradMod (GradMod f v) g = g f v

instance Graded (GradedModule t a) where
    data Graduation (GradedModule t a) n = GradGradMod (Graduation (NFun t) n) (Vector n a)
    fromGrad (GradGradMod f v) = GradMod f v
    toSomeGrad (GradMod f v) = SomeGrad $ GradGradMod f v

class Unzip ns where
    unzip :: GradVect ns (GradedModule t a) -> (GradVect ns (NFun t), Vector (SumNat ns) a)

instance Unzip '[] where
    unzip _ = (GradNil, empty)

instance Unzip ns => Unzip (n ': ns) where
    unzip (GradCons (GradGradMod f x) xs) = (GradCons f fs, x ++ as)
        where (fs, as) = Graded.GradedModule.unzip xs

instance (KnownNat n, Unzip ns) :=> Unzip (n ': ns) where
    ins = Sub Dict

allNatsUnzip :: Sing ns -> (() :: Constraint) :- Unzip ns
allNatsUnzip SNil            = Sub Dict
allNatsUnzip (SCons SNat ns) = Sub Dict &&& allNatsUnzip ns ||-> ins

zip
    :: (Compo ns)
    => Sing ns
    -> Graduation (NFun t) (Length ns)
    -> (GradVect ns (NFun t), Vector (SumNat ns) a)
    -> GradedModule t a
zip s g (fs, as) = case allSumNatKnownNat s of
    Sub Dict -> GradMod (compo g fs) as

unzipZip
    :: Sing ns
    -> Graduation (NFun t) (Length ns)
    -> GradVect ns (GradedModule t a)
    -> GradedModule t a
unzipZip s f vs = case (allNatsCompo s, allNatsUnzip s) of
    (Sub Dict, Sub Dict) ->
        Graded.GradedModule.zip s f $ Graded.GradedModule.unzip vs

combineToModule
    :: Sing n
    -> Graduation (NFun t) n
    -> Vector n (GradedModule t a)
    -> GradedModule t a
combineToModule s f v =
    withSomeGradVect (toSomeGradVect s v) (\vs -> unzipZip (getNsSing vs) f vs)

instance GenMonad (GradedModule t) where

    return a = GradMod (GradFun "id" head) $ singleton a

    GradMod f v >>= g = combineToModule sing f $ Prelude.fmap g v

fromScalar :: ToString t => t -> GradedModule t ()
fromScalar w = GradMod (GradFun (toString w) (const w)) empty

toScalar :: Semiring t => GradedModule t () -> t
toScalar ((GradMod (GradFun _ f) v)) = f $ Prelude.fmap (const one) v

instance (ToString b, Arbitrary b) => Arbitrary (GradedModule b ()) where
    arbitrary = fromScalar <$> arbitrary

instance (Show t, Read t) => Read (GradedModule t ()) where
    readsPrec n s = first fromScalar <$> readsPrec n s

instance (ToString weight, Num weight, Semiring weight) => Num (GradedModule weight ()) where
    x + y = combineToModule (sing :: SNat 2)
                            (GradFun "+" (\v -> head v + last v))
                            (cons x $ singleton y)
    x * y = combineToModule (sing :: SNat 2)
                            (GradFun "*" (\v -> head v * last v))
                            (cons x $ singleton y)
    abs x = combineToModule (sing :: SNat 1)
                            (GradFun "abs" (abs . head))
                            (singleton x)
    signum x = combineToModule (sing :: SNat 1)
                               (GradFun "signum" (signum . head))
                               (singleton x)
    fromInteger = fromScalar . fromInteger
    negate x = combineToModule (sing :: SNat 1)
                               (GradFun "negate" (negate . head))
                               (singleton x)

instance (Semiring weight, Fractional weight, ToString weight) => Fractional (GradedModule weight ()) where
    fromRational r = fromScalar $ fromRational r
    x / y = combineToModule (sing :: SNat 2)
                            (GradFun "/" (\v -> head v / last v))
                            (cons x $ singleton y)

instance (Semiring weight, Floating weight, ToString weight) => Floating (GradedModule weight ()) where
    pi = fromScalar pi
    exp l = combineToModule (sing :: SNat 1)
                            (GradFun "exp" (exp . head))
                            (singleton l)
    log l = combineToModule (sing :: SNat 1)
                            (GradFun "log" (log . head))
                            (singleton l)
    sin l = combineToModule (sing :: SNat 1)
                            (GradFun "sin" (sin . head))
                            (singleton l)
    cos l = combineToModule (sing :: SNat 1)
                            (GradFun "cos" (cos . head))
                            (singleton l)
    asin l = combineToModule (sing :: SNat 1)
                             (GradFun "asin" (asin . head))
                             (singleton l)
    acos l = combineToModule (sing :: SNat 1)
                             (GradFun "acos" (acos . head))
                             (singleton l)
    atan l = combineToModule (sing :: SNat 1)
                             (GradFun "atan" (atan . head))
                             (singleton l)
    sinh l = combineToModule (sing :: SNat 1)
                             (GradFun "sinh" (sinh . head))
                             (singleton l)
    cosh l = combineToModule (sing :: SNat 1)
                             (GradFun "cosh" (cosh . head))
                             (singleton l)
    asinh l = combineToModule (sing :: SNat 1)
                              (GradFun "asinh" (asinh . head))
                              (singleton l)
    acosh l = combineToModule (sing :: SNat 1)
                              (GradFun "acosh" (acosh . head))
                              (singleton l)
    atanh l = combineToModule (sing :: SNat 1)
                              (GradFun "atanh" (atanh . head))
                              (singleton l)
