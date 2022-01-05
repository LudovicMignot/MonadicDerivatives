{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Graded.GradedFun where

import           Data.Constraint               as C
                                                ( (&&&)
                                                , (:-)(Sub)
                                                , (:=>)(ins)
                                                , Constraint
                                                , Dict(Dict)
                                                )
import qualified Data.Constraint               as C
                                                ( trans )
import           Data.List                      ( intercalate )
import           Data.Maybe                     ( isJust )
import           Data.Proxy                     ( Proxy(..) )
import           Data.Singletons.Decide         ( (:~:)(Refl)
                                                , Decision(Proved)
                                                , SDecide((%~))
                                                )
import           Data.Singletons.Prelude        ( SingI(sing) )
import           Data.Singletons.Prelude.Bool   ( SBool(SFalse, STrue)
                                                , Sing
                                                )
import           Data.Singletons.Prelude.List   ( Length
                                                , Replicate
                                                , SList(SCons, SNil)
                                                , sLength
                                                , sReplicate
                                                )
import           Data.Singletons.TypeLits       ( (%<=?)
                                                , SNat(SNat)
                                                )
import qualified Data.Text                     as T
import           Data.Vector.Sized             as V
                                                ( Vector
                                                , cons
                                                , head
                                                , splitAt'
                                                )
import           GHC.TypeLits                   ( Nat
                                                , sameNat
                                                )
import           GHC.TypeNats                   ( type (+)
                                                , KnownNat
                                                )
import           Graded.Graded                  ( Graded(..)
                                                , SomeGrad(SomeGrad)
                                                )
import           Graded.GradedVector            ( GradVect(GradCons, GradNil)
                                                , getLengthSing
                                                , getNsSing
                                                , toList
                                                )
import           HTMLEntities.Text              ( text )
import           ToString.ToString              ( ToString
                                                    ( toHTMLString
                                                    , toString
                                                    )
                                                )
import           Type.SumNat                    ( SumNat
                                                , sumSumNat
                                                )

data NFun a where
    NFun ::KnownNat n =>{f_name :: String, f_fun ::Vector n a -> a} -> NFun a

instance Show (NFun a) where
    show = f_name

instance {-# OVERLAPS #-} ToString (NFun a) where
    toString = f_name

    toHTMLString (NFun n _) =
        "<span style=\"font-weight : bold; color : blue\" >"
            ++ T.unpack (text $ T.pack n)
            ++ "</span>"

arity :: (Vector n a -> a) -> Proxy n
arity _ = Proxy

arity' :: KnownNat n => (Vector n a -> a) -> Sing n
arity' _ = SNat

instance Graded (NFun a) where
    data Graduation (NFun a) n = GradFun {name :: String, run :: Vector n a -> a}
    fromGrad (GradFun s f) = NFun s f
    toSomeGrad (NFun s f) = SomeGrad (GradFun s f)

instance Eq (NFun a) where
    (NFun s1 f1) == (NFun s2 f2) =
        s1 == s2 && isJust (sameNat (arity f1) (arity f2))

instance Ord (NFun a) where
    compare (NFun s1 f1) (NFun s2 f2) = case compare s1 s2 of
        EQ -> case arity' f1 %<=? arity' f2 of
            STrue  -> LT
            SFalse -> GT
        r -> r

eval :: Graduation (NFun a) (1 + n) -> a -> Graduation (NFun a) n
eval (GradFun s f) x = GradFun s $ \es -> f $ x `cons` es

(||->) :: (a :- b) -> (b :- c) -> a :- c
(||->) = flip C.trans

class Compo ns where
    compo :: Graduation (NFun a) (Length ns) -> GradVect ns (NFun a) -> Graduation (NFun a) (SumNat ns)

instance Compo '[] where
    compo (GradFun s f) _ = GradFun s f

type family GenOne (n :: Nat) where
    GenOne n = Replicate n 1

singOfOnes :: Sing n -> Sing (GenOne n)
singOfOnes s = sReplicate s (SNat :: Sing 1)

lengthGenOneIsSum :: Sing n -> Length (GenOne n) :~: SumNat (GenOne n)
lengthGenOneIsSum s =
    case sLength (singOfOnes s) %~ sumSumNat (singOfOnes s) of
        Proved Refl -> Refl
        _           -> error "lengthGenOneIsSum: Problem, contradiction"

allId :: GradVect ns (NFun a) -> Bool
allId GradNil                        = True
allId (GradCons (GradFun "id" _) gs) = allId gs
allId _                              = False

instance (KnownNat n, Compo ns) => Compo (n ': ns) where
    compo f@(GradFun n _) gs'@(GradCons g'@(GradFun n' g) gs) =
        case (getNsSing gs :: Sing ns) %~ (sing :: Sing '[]) of
            (Proved Refl) | n == "id" -> g'
            _ ->
                case
                        ( (SNat :: Sing n) %~ (SNat :: Sing 1)
                        , getNsSing gs
                            %~ singOfOnes (getLengthSing gs :: Sing (Length ns))
                        )
                    of
                        (Proved Refl, Proved Refl)
                            | allId gs' -> case
                                    lengthGenOneIsSum (getLengthSing gs)
                                of
                                    Refl -> f
                            | n == "Not" && n' == "Not" -> GradFun "id" V.head
                        _ -> GradFun newname $ \es ->
                            let (es1, es2) = splitAt' (Proxy :: Proxy n) es
                            in  run (compo (eval f (g es1)) gs) es2
      where
        newname
            | null (toList gs')
            = n
            | otherwise
            = n ++ "∘(|" ++ intercalate "," (fmap f_name (toList gs')) ++ "|)"

instance (KnownNat n, Compo ns) :=> Compo (n ': ns) where
    ins = Sub Dict

allNatsCompo :: Sing ns -> (() :: Constraint) :- Compo ns
allNatsCompo SNil            = Sub Dict
allNatsCompo (SCons SNat ns) = Sub Dict &&& allNatsCompo ns ||-> ins
