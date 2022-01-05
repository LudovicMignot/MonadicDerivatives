{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module RegExp.MonadicRegExpWithFun where

import           Common                         ( ToStringVia(toStringVia) )
import           Data.Foldable                  ( foldl' )
import           Data.List                      ( intercalate )
import           Data.Maybe                     ( isJust )
import           Data.Semiring                  ( Semiring
                                                , one
                                                , plus
                                                , times
                                                , zero
                                                )
import           Data.Star                      ( Star
                                                , star
                                                )
import qualified Data.Text                     as T
                                                ( pack
                                                , unpack
                                                )
import           Data.Vector.Sized             as V
                                                ( Vector
                                                , knownLength
                                                , map
                                                , toList
                                                )
import           GenMonad.GenMonad              ( (<&>)
                                                , GenMonad
                                                    ( GenMonadConstraint
                                                    , liftM2
                                                    , return
                                                    )
                                                )
import           Graded.Graded                  ( Graded(Graduation, fromGrad) )
import           HTMLEntities.Text              ( text )
import           Prelude                 hiding ( (*>)
                                                , (<*)
                                                , (>>=)
                                                , return
                                                )
import           RegExp.OpClass                 ( HasFun(..)
                                                , HasName(..)
                                                )
import           ToString.ToString              ( ToString
                                                    ( toHTMLString
                                                    , toString
                                                    )
                                                )

data MonadicRegExp m a where
  Sum ::MonadicRegExp m a -> MonadicRegExp m a -> MonadicRegExp m a
  Conc ::MonadicRegExp m a -> MonadicRegExp m a -> MonadicRegExp m a
  Star ::MonadicRegExp m a -> MonadicRegExp m a
  LeftAction ::m () -> MonadicRegExp m a -> MonadicRegExp m a
  RightAction ::MonadicRegExp m a -> m () -> MonadicRegExp m a
  Fun ::( Graded op,
      HasName op,
      HasFun op n m (),
      HasFun op n m (MonadicRegExp m a)
    ) =>
    Graduation op n ->
    Vector n (MonadicRegExp m a) ->
    MonadicRegExp m a
  Atom ::a -> MonadicRegExp m a
  Epsilon ::MonadicRegExp m a
  Empty ::MonadicRegExp m a

instance
  (ToStringVia (m ()), ToString a) =>
  Show (MonadicRegExp m a)
  where
    show = toString

parentheses :: (ToString a, ToStringVia (m ())) => MonadicRegExp m a -> String
parentheses e@Empty    = toString e
parentheses e@Epsilon  = toString e
parentheses e@(Atom _) = toString e
parentheses e@(Star _) = toString e
parentheses e          = mconcat ["(", toString e, ")"]

instance
  {-# OVERLAPS #-}
  (ToString a, ToStringVia (m ())) =>
  ToString (MonadicRegExp m a)
  where
    toString Empty    = "0"
    toString Epsilon  = "1"
    toString (Atom a) = toString a
    toString (LeftAction w e) =
        mconcat ["[", toStringVia w, "]", "*>", parentheses e]
    toString (RightAction e w) =
        mconcat [parentheses e, "<*", "[", toStringVia w, "]"]
    toString (Star e) = mconcat [parentheses e, "*"]
    toString (Conc e1@(Conc _ _) e2) =
        mconcat [toString e1, ".", parentheses e2]
    toString (Conc e1 e2) = mconcat [parentheses e1, ".", parentheses e2]
    toString (Sum e1@(Sum _ _) e2) = mconcat [toString e1, "+", parentheses e2]
    toString (Sum e1 e2) = mconcat [parentheses e1, "+", parentheses e2]
    toString (Fun op es) | null es = name $ knownLength es $ fromGrad op
    toString (Fun op es) = mconcat
        [ name (knownLength es $ fromGrad op)
        , "("
        , intercalate "," (toList $ fmap toString es)
        , ")"
        ]

    toHTMLString = T.unpack . text . T.pack . toString

instance (Eq (m ()), Eq a) => Eq (MonadicRegExp m a) where
    Sum  e1 e2      == Sum  e3 e4        = e1 == e2 && e3 == e4
    Conc e1 e2      == Conc e3 e4        = e1 == e2 && e3 == e4
    Star e          == Star e'           = e == e'
    LeftAction  w e == LeftAction  w' e' = w == w' && e == e'
    RightAction e w == RightAction e' w' = w == w' && e == e'
    Fun op es == Fun op' es' =
        name (knownLength es $ fromGrad op)
            == name (knownLength es' $ fromGrad op')
            && toList es
            == toList es'
    Atom a  == Atom a' = a == a'
    Epsilon == Epsilon = True
    Empty   == Empty   = True
    _       == _       = False

instance (Ord a, Ord (m ())) => Ord (MonadicRegExp m a) where
    compare (Sum e1 e2)       (Sum e3 e4)           = compare (e1, e2) (e3, e4)
    compare (Sum _  _ )       _                     = LT
    compare _                 (Sum  _  _ )          = GT
    compare (Conc e1 e2)      (Conc e3 e4)          = compare (e1, e2) (e3, e4)
    compare (Conc _  _ )      _                     = LT
    compare _                 (Conc _ _)            = GT
    compare (Star e)          (Star e' )            = compare e e'
    compare (Star _)          _                     = LT
    compare _                 (Star _          )    = GT
    compare (LeftAction w e)  (LeftAction w' e')    = compare (e, w) (e', w')
    compare (LeftAction _ _)  _                     = LT
    compare _                 (LeftAction  _  _ )   = GT
    compare (RightAction e w) (RightAction e' w')   = compare (e, w) (e', w')
    compare (RightAction _ _) _                     = LT
    compare _                 (RightAction _   _  ) = GT
    compare (Fun op es)       (Fun         op' es') = compare
        (name (knownLength es $ fromGrad op)  , toList es)
        (name (knownLength es' $ fromGrad op'), toList es')
    compare (Fun _ _) _         = LT
    compare _         (Fun _ _) = GT
    compare (Atom a)  (Atom a') = compare a a'
    compare (Atom _)  _         = LT
    compare _         (Atom _)  = GT
    compare Epsilon   Epsilon   = EQ
    compare Epsilon   Empty     = LT
    compare Empty     Epsilon   = GT
    compare Empty     Empty     = EQ

plus' :: MonadicRegExp m a -> MonadicRegExp m a -> MonadicRegExp m a
plus' Empty e     = e
plus' e     Empty = e
plus' e1    e2    = e1 `Sum` e2

conc' :: MonadicRegExp m a -> MonadicRegExp m a -> MonadicRegExp m a
conc' Empty   _       = Empty
conc' _       Empty   = Empty
conc' Epsilon e       = e
conc' e       Epsilon = e
conc' e1      e2      = e1 `Conc` e2

leftAction'
    :: (Eq (m ()), Semiring (m ()))
    => m ()
    -> MonadicRegExp m a
    -> MonadicRegExp m a
leftAction' w e | w == zero = Empty
                | w == one  = e
                | otherwise = LeftAction w e

fromList :: [a] -> MonadicRegExp m a
fromList = foldl' (\acc -> conc' acc . Atom) Epsilon

fromListOfLists :: [[a]] -> MonadicRegExp m a
fromListOfLists = foldl' (\acc -> plus' acc . fromList) Empty

instance Semigroup (MonadicRegExp m a) where
    (<>) = plus'

instance Monoid (MonadicRegExp m a) where
    mempty = Empty

instance Semiring (MonadicRegExp m a) where
    plus  = plus'
    times = conc'
    zero  = Empty
    one   = Epsilon

instance Star (MonadicRegExp m a) where
    star = Star

nullable :: (Star (m ()), GenMonad m) => MonadicRegExp m a -> m ()
nullable Epsilon           = one
nullable Empty             = zero
nullable (Atom _         ) = zero
nullable (Fun  op es     ) = fun op $ V.map nullable es
nullable (Sum  e1 e2     ) = nullable e1 `plus` nullable e2
nullable (Conc e1 e2     ) = nullable e1 `times` nullable e2
nullable (Star e         ) = star $ nullable e
nullable (LeftAction  w e) = w `times` nullable e
nullable (RightAction e w) = nullable e `times` w

nullableProper
    :: ( Monoid (m ())
       , GenMonad m
       , GenMonadConstraint m ()
       , Semiring (m ())
       , Eq (m ())
       )
    => MonadicRegExp m a
    -> Maybe (m ())
nullableProper Epsilon     = Just $ return ()
nullableProper Empty       = Just mempty
nullableProper (Atom _   ) = Just mempty
nullableProper (Sum e1 e2) = nullableProper e1 <> nullableProper e2
nullableProper (Conc e1 e2) =
    liftM2 times (nullableProper e1) (nullableProper e2)
nullableProper (Star e) = case nullableProper e of
    Just v | v == mempty -> Just $ return ()
    _                    -> Nothing
nullableProper (LeftAction w e) = (w `times`) <$> nullableProper e
nullableProper (RightAction e w) = nullableProper e <&> (`times` w)
nullableProper (Fun op es) = fmap (fun op) $ sequence $ V.map nullableProper es

isProper
    :: ( Monoid (m ())
       , GenMonad m
       , GenMonadConstraint m ()
       , Semiring (m ())
       , Eq (m ())
       )
    => MonadicRegExp m a
    -> Bool
isProper = isJust . nullableProper

-- !!! valable uniquement pour les expressions propres
nullableProper'
    :: (Monoid (m ()), GenMonad m, GenMonadConstraint m (), Semiring (m ()))
    => MonadicRegExp m a
    -> m ()
nullableProper' Epsilon             = return ()
nullableProper' Empty               = mempty
nullableProper' (Atom _           ) = mempty
nullableProper' (Sum  e1 e2       ) = nullableProper' e1 <> nullableProper' e2
nullableProper' (Conc e1 e2) = nullableProper' e1 `times` nullableProper' e2
nullableProper' (Star _           ) = return ()
nullableProper' (LeftAction  w  e ) = w `times` nullableProper' e
nullableProper' (RightAction e  w ) = nullableProper' e `times` w
nullableProper' (Fun         op es) = fun op $ V.map nullableProper' es


