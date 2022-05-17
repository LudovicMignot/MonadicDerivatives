{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Semimodule.Semimodule where

import           Common                         ( Castable(cast) )
import           Data.Bifunctor                 ( first )
import           Data.Semiring                  ( Add(Add)
                                                , Semiring(one, zero)
                                                , times
                                                )
import           Data.Set                       ( Set )
import           GenMonad.GenMonad             as G
                                                ( GenMonad
                                                    ( (*>)
                                                    , (<$>)
                                                    , (<&>)
                                                    , (<*)
                                                    )
                                                )
import           Graded.GradedFun               ( Graduation(GradFun) )
import           Graded.GradedModule            ( GradedModule(GradMod) )
import           Graded.GradedModuleOfLinComb   ( FunctorCompo(..)
                                                , GradedModuleOfLinComb(..)
                                                , toScalar
                                                )
import           LinComb.LinComb4               ( LinComb )
import           ToString.ToString              ( ToString(toString) )

class (Semiring k, Monoid a) => Semimodule k a where
    leftAction :: k -> a -> a
    rightAction :: a -> k -> a

instance Semiring k => Semimodule k (Add k) where
    leftAction k (Add a) = Add $ k `times` a
    rightAction (Add a) k = Add $ a `times` k

instance (Semigroup k, Semiring k) => Semimodule k (Maybe k) where
    leftAction k s = times k G.<$> s
    rightAction s k = s G.<&> (`times` k)

instance (Semigroup k, Semiring k, Semigroup s) => Semimodule k (Maybe (k, s)) where
    leftAction k s = first (times k) G.<$> s
    rightAction s k = s G.<&> first (`times` k)

instance Semigroup k => Semimodule (Maybe ()) (Maybe k) where
    leftAction  = (G.*>)
    rightAction = (G.<*)

instance (Semiring k, Ord k) => Semimodule k (Set k) where
    leftAction k s = times k G.<$> s
    rightAction s k = s G.<&> (`times` k)

instance (Semiring k, Ord k, Ord s) => Semimodule k (Set (k, s)) where
    leftAction k s = first (times k) G.<$> s
    rightAction s k = s G.<&> first (`times` k)

instance (Ord k) => Semimodule (Set ()) (Set k) where
    leftAction  = (G.*>)
    rightAction = (G.<*)

instance (Ord k, Semiring k, Semigroup w, Semiring w, Ord w) => Semimodule k (LinComb w k) where
    leftAction k s = times k G.<$> s
    rightAction s k = s G.<&> (`times` k)

instance (Ord k, Semiring k, Semigroup w, Semiring w, Ord w, Ord s) =>  Semimodule k (LinComb w (k, s)) where
    leftAction k s = first (times k) G.<$> s
    rightAction s k = s G.<&> first (`times` k)

instance (Semiring w, Ord k, Ord w, Semigroup w) => Semimodule (LinComb w ()) (LinComb w k) where
    leftAction  = (G.*>)
    rightAction = (G.<*)

-- instance (Show t, Monoid t, Semiring t, Eq t, Ord a, Eq(LinComb t a), Ord t, Monoid a) => Semimodule (GradedModuleOfLinComb t ())  (GradedModuleOfLinComb t a) where
instance (Show t, Monoid t, Semiring t, Eq t) => Semimodule (GradedModuleOfLinComb t ())  (GradedModuleOfLinComb t a) where
    leftAction w g@(Grd (FunctorCompo (GradMod (GradFun n f) v)))
        | w == zero || n == show (zero :: t) = zero
        | w == one = g
        | otherwise = Grd $ FunctorCompo
            (GradMod
                (GradFun ("#" ++ toString (toScalar w) ++ "*" ++ n ++ "#")
                         ((cast w `times`) . f)
                )
                v
            )
    rightAction g@(Grd (FunctorCompo (GradMod (GradFun n f) v))) w
        | w == zero || n == show (zero :: t) = zero
        | w == one = g
        | otherwise = Grd $ FunctorCompo
            (GradMod
                (GradFun ("#" ++ n ++ "*" ++ toString (toScalar w) ++ "#")
                         ((`times` cast w) . f)
                )
                v
            )

