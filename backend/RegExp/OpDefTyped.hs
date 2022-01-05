{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
module RegExp.OpDefTyped where

import           Common                         ( IsBool )
import           Data.Constraint               as C
                                                ( (:-)(Sub)
                                                , Dict(Dict)
                                                , HasDict(evidence)
                                                , trans
                                                , withDict
                                                )
import qualified Data.Set                      as Set2
import           Data.Singletons                ( Sing
                                                , SingI(sing)
                                                )
import           Data.Singletons.Decide         ( Decision(Proved)
                                                , SDecide((%~))
                                                )
import           Data.Type.Equality             ( type (:~:)(Refl)
                                                , apply
                                                , castWith
                                                , outer
                                                , sym
                                                )
import           LinComb.LinComb4              as L4
                                                ( LinComb )
import           Prelude                 hiding ( head
                                                , last
                                                )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp )
import           RegExp.OpClass                 ( HasFun(..) )
import           RegExp.OpDef                   ( BooleanOp
                                                , andExp
                                                , arithMean'
                                                , geomMean'
                                                , gradExtDist'
                                                , gradExtMult'
                                                , implExp
                                                , notExp
                                                )
import           SemiRingsDef.SemiRingsDef     as SRD
                                                ( SR )
import           Singletons.Singletons          ( )
import           Type.UnknownSizedVect          ( UnknownSizedVect )

eqImplIsBool :: a :~: b -> IsBool a :- IsBool b
eqImplIsBool c = withDict (evidence c) $ Sub Dict

eqImplHasFun
    :: m1 () :~: m2 ()
    -> HasFun BooleanOp n m1 (MonadicRegExp m1 a) :- HasFun BooleanOp n m2 (MonadicRegExp m2 a)
eqImplHasFun c = withDict (evidence c) $ Sub Dict

isBoolWithEq :: forall t t' . IsBool t => t :~: t' -> () :- IsBool t'
isBoolWithEq a = C.trans (eqImplIsBool a :: IsBool t :- IsBool t')
                         (Sub Dict :: () :- IsBool t)

testBoolish :: forall t . Sing t -> Maybe (() :- IsBool t)
testBoolish s = case (sing :: Sing (Set2.Set ())) %~ s of
    Proved a -> Just $ isBoolWithEq a
    _        -> case (sing :: Sing (Maybe ())) %~ s of
        Proved a -> Just $ isBoolWithEq a
        _        -> case (sing :: Sing (LinComb (SRD.SR Bool) ())) %~ s of
            Proved a -> Just $ isBoolWithEq a
            _        -> Nothing

isBoolFunWithEq
    :: forall n m m' a
     . HasFun BooleanOp n m (MonadicRegExp m a)
    => m () :~: m' ()
    -> () :- HasFun BooleanOp n m' (MonadicRegExp m' a)
isBoolFunWithEq a = C.trans
    (eqImplHasFun a :: HasFun BooleanOp n m (MonadicRegExp m a) :- HasFun BooleanOp n m' (MonadicRegExp m' a)
    )
    (Sub Dict :: () :- HasFun BooleanOp n m (MonadicRegExp m a))

testBoolFunish1
    :: forall a m
     . Ord a
    => Sing a
    -> Sing (m ())
    -> Maybe (() :- HasFun BooleanOp 1 m (MonadicRegExp m a))
testBoolFunish1 _ s = case (sing :: Sing (Set2.Set ())) %~ s of
    Proved a -> Just $ isBoolFunWithEq a
    _        -> case (sing :: Sing (Maybe ())) %~ s of
        Proved a -> Just $ isBoolFunWithEq a
        _        -> case (sing :: Sing (LinComb (SRD.SR Bool) ())) %~ s of
            Proved a -> Just $ isBoolFunWithEq a
            _        -> Nothing

testBoolFunish2
    :: forall a m
     . Ord a
    => Sing a
    -> Sing (m ())
    -> Maybe (() :- HasFun BooleanOp 2 m (MonadicRegExp m a))
testBoolFunish2 _ s = case (sing :: Sing (Set2.Set ())) %~ s of
    Proved a -> Just $ isBoolFunWithEq a
    _        -> case (sing :: Sing (Maybe ())) %~ s of
        Proved a -> Just $ isBoolFunWithEq a
        _        -> case (sing :: Sing (LinComb (SRD.SR Bool) ())) %~ s of
            Proved a -> Just $ isBoolFunWithEq a
            _        -> Nothing

notExpIfBool
    :: forall m a
     . (SingI (m ()), Ord a, SingI a)
    => MonadicRegExp m a
    -> Maybe (MonadicRegExp m a)
notExpIfBool e =
    case
            ( testBoolish (sing :: Sing (m ()))
            , testBoolFunish1 (sing :: Sing a) (sing :: Sing (m ()))
            )
        of
            (Just (Sub Dict), Just (Sub Dict :: () :- HasFun BooleanOp 1 m (MonadicRegExp m a)))
                -> Just $ notExp e
            _ -> Nothing

implExpIfBool
    :: forall m a
     . (SingI (m ()), Ord a, SingI a)
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> Maybe (MonadicRegExp m a)
implExpIfBool e1 e2 =
    case
            ( testBoolish (sing :: Sing (m ()))
            , testBoolFunish2 (sing :: Sing a) (sing :: Sing (m ()))
            )
        of
            (Just (Sub Dict), Just (Sub Dict :: () :- HasFun BooleanOp 2 m (MonadicRegExp m a)))
                -> Just $ implExp e1 e2
            _ -> Nothing

andExpIfBool
    :: forall m a
     . (SingI (m ()), Ord a, SingI a)
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> Maybe (MonadicRegExp m a)
andExpIfBool e1 e2 =
    case
            ( testBoolish (sing :: Sing (m ()))
            , testBoolFunish2 (sing :: Sing a) (sing :: Sing (m ()))
            )
        of
            (Just (Sub Dict), Just (Sub Dict :: () :- HasFun BooleanOp 2 m (MonadicRegExp m a)))
                -> Just $ andExp e1 e2
            _ -> Nothing

eqMonEqExp
    :: forall m m' a
     . m () :~: m' ()
    -> MonadicRegExp m a :~: MonadicRegExp m' a
eqMonEqExp a = case outer a of
    Refl -> Refl

gradExtDistIfWellTyped
    :: forall m a
     . (SingI (m ()), Ord a)
    => UnknownSizedVect (MonadicRegExp m a)
    -> Maybe (MonadicRegExp m a)
gradExtDistIfWellTyped v =
    case (sing :: (Sing (LinComb (SR Int) ()))) %~ (sing :: Sing (m ())) of
        Proved a ->
            Just $ castWith (eqMonEqExp a) $ (gradExtDist' @(SRD.SR Int))
                (castWith (sym (apply Refl (eqMonEqExp a))) v)
        _ ->
            case
                    (sing :: (Sing (LinComb (SR Double) ())))
                        %~ (sing :: Sing (m ()))
                of
                    Proved a ->
                        Just
                            $ castWith (eqMonEqExp a)
                            $ (gradExtDist' @(SRD.SR Double))
                                  (castWith (sym (apply Refl (eqMonEqExp a))) v)
                    _ -> Nothing

gradExtMultIfWellTyped
    :: forall m a
     . (SingI (m ()), Ord a)
    => UnknownSizedVect (MonadicRegExp m a)
    -> Maybe (MonadicRegExp m a)
gradExtMultIfWellTyped v =
    case (sing :: (Sing (LinComb (SR Int) ()))) %~ (sing :: Sing (m ())) of
        Proved a ->
            Just $ castWith (eqMonEqExp a) $ (gradExtMult' @(SRD.SR Int))
                (castWith (sym (apply Refl (eqMonEqExp a))) v)
        _ ->
            case
                    (sing :: (Sing (LinComb (SR Double) ())))
                        %~ (sing :: Sing (m ()))
                of
                    Proved a ->
                        Just
                            $ castWith (eqMonEqExp a)
                            $ (gradExtMult' @(SRD.SR Double))
                                  (castWith (sym (apply Refl (eqMonEqExp a))) v)
                    _ -> Nothing

arithMeanIfWellTyped
    :: forall m a
     . (SingI (m ()), Ord a)
    => UnknownSizedVect (MonadicRegExp m a)
    -> Maybe (MonadicRegExp m a)
arithMeanIfWellTyped v =
    case (sing :: (Sing (LinComb (SR Double) ()))) %~ (sing :: Sing (m ())) of
        Proved a -> Just $ castWith (eqMonEqExp a) $ arithMean'
            (castWith (sym (apply Refl (eqMonEqExp a))) v)
        _ -> Nothing

geomMeanIfWellTyped
    :: forall m a
     . (SingI (m ()), Ord a)
    => UnknownSizedVect (MonadicRegExp m a)
    -> Maybe (MonadicRegExp m a)
geomMeanIfWellTyped v =
    case (sing :: (Sing (LinComb (SR Double) ()))) %~ (sing :: Sing (m ())) of
        Proved a -> Just $ castWith (eqMonEqExp a) $ geomMean'
            (castWith (sym (apply Refl (eqMonEqExp a))) v)
        _ -> Nothing
