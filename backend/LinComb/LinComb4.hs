{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DerivingVia #-}

module LinComb.LinComb4 where

import           Data.Coerce                    ( coerce )
import           Data.Function                  ( on )
import           Data.List                      ( intercalate )
import qualified Data.Map.Strict               as Map
import           Data.Map.Strict                ( Map )
import           Data.Semiring                  ( Semiring
                                                , one
                                                , plus
                                                , times
                                                , zero
                                                )
import           Data.Star                      ( Star
                                                , star
                                                )
import           GenMonad.GenMonad             as G
                                                ( GenMonad
                                                    ( (>>)
                                                    , (>>=)
                                                    , GenMonadConstraint
                                                    , return
                                                    )
                                                )
import           Test.QuickCheck                ( Arbitrary
                                                , arbitrary
                                                )
import           ToString.ToString              ( ToString
                                                    ( toHTMLString
                                                    , toString
                                                    )
                                                )

newtype LinComb weight key = LinComb {get :: Map key weight}

instance Semiring weight => GenMonad (LinComb weight) where

    type GenMonadConstraint (LinComb weight) val = (Ord val, Ord weight)

    return = LinComb . flip Map.singleton one

    LinComb m >>= f = coerce $ Map.foldlWithKey'
        (\acc p w -> if w == zero
            then acc
            else Map.unionWith plus (Map.map (times w) (coerce (f p))) acc
        )
        Map.empty
        m

instance (Semiring weight, Ord weight) => Semiring (LinComb weight ()) where
    zero = LinComb mempty
    one  = G.return ()
    l1 `plus` l2 = LinComb $ Map.unionWith plus (coerce l1) (coerce l2)
    times = (G.>>)

instance (Ord a, Semigroup weight) => Semigroup (LinComb weight a) where
    l1 <> l2 = LinComb $ Map.unionWith (<>) (coerce l1) (coerce l2)

instance (Ord a, Semigroup weight) => Monoid (LinComb weight a) where
    mempty = LinComb mempty

toScalar :: Semiring weight => LinComb weight () -> weight
toScalar l = Map.findWithDefault zero () $ coerce l

fromScalar :: weight -> LinComb weight ()
fromScalar = coerce . Map.singleton ()

null :: LinComb v k -> Bool
null (LinComb l) = Map.null l

instance (Semiring weight, Eq weight) => Eq (LinComb weight ()) where
    m1 == m2 = toScalar m1 == toScalar m2

instance (Semiring weight, Ord weight) => Ord (LinComb weight ()) where
    compare = compare `on` toScalar

instance (Star weight, Ord weight) => Star (LinComb weight ()) where
    star = fromScalar . star . toScalar

instance (Num weight, Semiring weight) => Num (LinComb weight ()) where
    x + y = fromScalar $ toScalar x + toScalar y
    x * y = fromScalar $ toScalar x * toScalar y
    abs         = fromScalar . abs . toScalar
    signum      = fromScalar . signum . toScalar
    fromInteger = fromScalar . fromInteger
    negate      = fromScalar . negate . toScalar

instance (Semiring weight, Fractional weight) => Fractional (LinComb weight ()) where
    fromRational r = fromScalar $ fromRational r
    l1 / l2 = fromScalar $ toScalar l1 / toScalar l2

instance (Semiring weight, Floating weight) => Floating (LinComb weight ()) where
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

instance Arbitrary weight => Arbitrary (LinComb weight ()) where
    arbitrary = fromScalar <$> arbitrary

instance (Semiring weight, Eq weight, Show weight, Show key) => Show (LinComb weight key) where
    show = toString -- show . Map.toList . get

instance {-# OVERLAPS #-} ToString weight => ToString (LinComb weight ()) where
    toString (LinComb m) = maybe "0" toString (Map.lookup () m)

instance {-# OVERLAPS #-} (Semiring weight, Eq weight, ToString key, ToString weight) => ToString (LinComb weight key) where
    toString (LinComb m) | Map.null m = "0[]"
    toString (LinComb m) =
        intercalate " ⊞ " $ stringFromCouple <$> Map.toList m
      where
        stringFromCouple (k, w)
            | w == one  = toString k
            | otherwise = mconcat [toString w, "[", toString k, "]"]

    toHTMLString (LinComb m) | Map.null m =
        "<span style=\"font-weight : bold; color : blue\" >0</span>"
    toHTMLString (LinComb m) =
        intercalate
                "<span style=\"font-weight : bold; color : blue\" > ⊞ </span>"
            $   stringFromCouple
            <$> Map.toList m
      where
        stringFromCouple (k, w)
            | w == one = toHTMLString k
            | otherwise = mconcat
                [ toString w
                , "<span style=\"font-weight : bold; color : blue\" >[</span>"
                , toString k
                , "<span style=\"font-weight : bold; color : blue\" >]</span>"
                ]

toList :: LinComb a k -> [(k, a)]
toList (LinComb m) = Map.toList m
