
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
module RegExp.OpDef where

import           Common                         ( Castable(cast)
                                                , IsBool
                                                )
import           Data.Foldable                 as F
                                                ( Foldable(fold)
                                                , foldl'
                                                )
import qualified Data.Map.Strict               as Map2
import           Data.Proxy                     ( Proxy(..) )
import           Data.Semiring                  ( Semiring
                                                , zero
                                                )
import qualified Data.Set                      as Set2
import           Data.Singletons.TypeLits       ( KnownNat
                                                , SNat(SNat)
                                                )
import           Data.Type.Equality             ( type (:~:)(Refl) )
import           Data.Vector.Sized             as V
                                                ( Vector
                                                , cons
                                                , fromTuple
                                                , head
                                                , knownLength
                                                , last
                                                , map
                                                , singleton
                                                , toList
                                                )
import           GHC.TypeNats                   ( sameNat )
import           GenMonad.GenMonad             as G
                                                ( GenMonad(return) )
import           Graded.Graded                  ( Graded(..)
                                                , SomeGrad(SomeGrad)
                                                )
import           Graded.GradedFun               ( Graduation(GradFun)
                                                , NFun(f_name)
                                                )
import           Graded.GradedModule           as GM
                                                ( GradedModule(GradMod)
                                                , combineToModule
                                                )
import           Graded.GradedModuleOfLinComb  as GL
                                                ( FunctorCompo
                                                    ( FunctorCompo
                                                    , run
                                                    )
                                                , GradedModuleOfLinComb(..)
                                                , fromScalar
                                                )
import           LinComb.LinComb4              as L4
                                                ( LinComb(LinComb)
                                                , fromScalar
                                                )
import           Prelude                 hiding ( head
                                                , last
                                                )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp
                                                    ( Empty
                                                    , Epsilon
                                                    , Fun
                                                    )
                                                , conc'
                                                , leftAction'
                                                , plus'
                                                )
import           RegExp.OpClass                 ( HasFun(..)
                                                , HasName(..)
                                                )
import           Semimodule.Semimodule          ( Semimodule(..) )
import           Type.UnknownSizedVect          ( UnknownSizedVect
                                                , withSomevect
                                                )

data Sum = Sum

instance Graded Sum where
    data Graduation Sum n = GradSum
    fromGrad GradSum = Sum
    toSomeGrad Sum = SomeGrad (GradSum :: Graduation Sum 2)

instance HasName Sum where
    name Sum = "Sum"

instance (Monoid (m a)) => HasFun Sum n m a where
    fun GradSum es = mconcat $ toList es

class ToExp m where
  toExp :: m (MonadicRegExp m a) -> MonadicRegExp m a

instance ToExp Maybe where
    toExp Nothing  = Empty
    toExp (Just e) = e


instance ToExp Set2.Set where
    toExp = F.foldl' plus' Empty

instance (Semiring weight, Ord weight) => ToExp (L4.LinComb weight) where
    toExp (L4.LinComb l) = Map2.foldlWithKey
        (\acc e w -> leftAction' (L4.fromScalar w) e `plus'` acc)
        Empty
        l

-- instance (Monoid t, Semiring t, Show t, Ord t, Ord a, Eq
--                       (LinComb t (MonadicRegExp (GradedModuleOfLinComb t) a))) => Semimodule (MonadicRegExp (GradedModuleOfLinComb t) a) (GradedModuleOfLinComb t (MonadicRegExp (GradedModuleOfLinComb t) a)) where
instance (Monoid t, Semiring t, Show t, Ord t, Ord a) => Semimodule (MonadicRegExp (GradedModuleOfLinComb t) a) (GradedModuleOfLinComb t (MonadicRegExp (GradedModuleOfLinComb t) a)) where

    leftAction Empty   _  = mempty
    leftAction Epsilon fc = fc
    leftAction e       fc = case toExp fc of
        Empty -> mempty
        e'    -> G.return $ e `conc'` e'
    rightAction _  Empty   = mempty
    rightAction fc Epsilon = fc
    rightAction fc e       = case toExp fc of
        Empty -> mempty
        e'    -> G.return $ e' `conc'` e

data BooleanOp = Not | And | Impl | Or
  deriving (Eq, Ord)

instance Graded BooleanOp where
    data Graduation BooleanOp 1 = GradNot
    data Graduation BooleanOp 2 = GradAnd | GradImpl | GradOr

    fromGrad x = case sameNat (graduation x) (Proxy :: Proxy 1) of
        Nothing -> case sameNat (graduation x) (Proxy :: Proxy 2) of
            Nothing   -> error "Impossible case"
            Just Refl -> case x of
                GradAnd  -> And
                GradImpl -> Impl
                GradOr   -> Or
        Just _ -> Not

    toSomeGrad Not  = SomeGrad GradNot
    toSomeGrad And  = SomeGrad GradAnd
    toSomeGrad Impl = SomeGrad GradImpl
    toSomeGrad Or   = SomeGrad GradOr

instance HasName BooleanOp where
    name Not  = "Not"
    name And  = "And"
    name Impl = "Impl"
    name Or   = "Or"

instance IsBool (m ()) => HasFun BooleanOp 1 m () where
    fun GradNot es = cast $ not $ cast $ head es

instance IsBool (m ()) => HasFun BooleanOp 2 m () where
    fun GradOr   es = cast $ cast (head es) || cast (last es)
    fun GradAnd  es = cast $ cast (head es) && cast (last es)
    fun GradImpl es = cast $ not (cast (head es)) || cast (last es)

instance {-# OVERLAPS #-} (Ord a, IsBool t, IsBool (LinComb t ()), Semiring t, Ord t)
  => HasFun BooleanOp 1 (LinComb t) (MonadicRegExp (LinComb t) a) where
    fun op es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} (Ord a, IsBool t, Semiring t, Ord t, Semigroup t, IsBool (LinComb t ()))
  => HasFun BooleanOp 2 (LinComb t) (MonadicRegExp (LinComb t) a) where
    fun GradOr es = fold es
    fun op     es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} HasFun BooleanOp 1 Maybe (MonadicRegExp Maybe a) where
    fun op es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} HasFun BooleanOp 2 Maybe (MonadicRegExp Maybe a) where
    fun GradOr es = fold es
    fun op     es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} (Ord a) => HasFun BooleanOp 1 Set2.Set (MonadicRegExp Set2.Set a) where
    fun op es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} (Ord a) => HasFun BooleanOp 2 Set2.Set (MonadicRegExp Set2.Set a) where
    fun GradOr es = fold es
    fun op     es = G.return $ Fun op $ V.map toExp es

instance {-# OVERLAPS #-} (IsBool t)
  => HasFun BooleanOp 1 (GradedModuleOfLinComb t) (MonadicRegExp (GradedModuleOfLinComb t) a) where
    fun f@GradNot v =
        Grd
            $ FunctorCompo
            $ combineToModule
                  SNat
                  (GradFun (name $ fromGrad f) (cast . not . cast . head))
            $ fmap (run . \(Grd x) -> x) v

instance {-# OVERLAPS #-} (IsBool t)
  => HasFun BooleanOp 2 (GradedModuleOfLinComb t) (MonadicRegExp (GradedModuleOfLinComb t) a) where
    fun f@GradOr v =
        Grd
            $ FunctorCompo
            $ combineToModule
                  SNat
                  (GradFun (name $ fromGrad f)
                           (\es -> cast $ cast (head es) || cast (last es))
                  )
            $ fmap (run . \(Grd x) -> x) v
    fun f@GradAnd v =
        Grd
            $ FunctorCompo
            $ combineToModule
                  SNat
                  (GradFun (name $ fromGrad f)
                           (\es -> cast $ cast (head es) && cast (last es))
                  )
            $ fmap (run . \(Grd x) -> x) v
    fun f@GradImpl v =
        Grd
            $ FunctorCompo
            $ combineToModule
                  SNat
                  (GradFun
                      (name $ fromGrad f)
                      (\es -> cast $ not (cast (head es)) || cast (last es))
                  )
            $ fmap (run . \(Grd x) -> x) v

notExp
    :: (IsBool (m ()), HasFun BooleanOp 1 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
notExp e = Fun GradNot $ singleton e

andExp
    :: (IsBool (m ()), HasFun BooleanOp 2 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
andExp e e' = Fun GradAnd $ e `cons` singleton e'

and'
    :: (IsBool (m ()), HasFun BooleanOp 2 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
and' Empty _     = Empty
and' _     Empty = Empty
and' e     e'    = Fun GradAnd $ e `cons` singleton e'

implExp
    :: (IsBool (m ()), HasFun BooleanOp 2 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
implExp e e' = Fun GradImpl $ e `cons` singleton e'

impl'
    :: ( IsBool (m ())
       , HasFun BooleanOp 1 m (MonadicRegExp m a)
       , HasFun BooleanOp 2 m (MonadicRegExp m a)
       )
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
impl' Empty _     = notExp Empty
impl' e     Empty = notExp e
impl' e     e'    = implExp e e'

instance (KnownNat n, Ord a, Castable t (Set2.Set ()), Castable  (Set2.Set ()) t) => HasFun (NFun t) n Set2.Set (MonadicRegExp Set2.Set a)where
    fun f es = G.return $ Fun f $ V.map toExp es

data FloatingOp = ArithMean | GeomMean

instance  Graded FloatingOp where
    data Graduation FloatingOp n = GradArithMean | GradGeomMean

    fromGrad GradArithMean = ArithMean
    fromGrad GradGeomMean  = GeomMean

    toSomeGrad ArithMean = SomeGrad (GradArithMean :: Graduation FloatingOp 2)
    toSomeGrad GeomMean  = SomeGrad (GradGeomMean :: Graduation FloatingOp 2)

instance HasName FloatingOp where
    name ArithMean = "/*/"
    name GeomMean  = "/**/"

instance Floating (m a) => HasFun FloatingOp n m a where
    fun GradArithMean es =
        if null es then 0 else sum es / fromIntegral (length es)
    fun GradGeomMean es =
        if null es then 1 else product es ** (1 / fromIntegral (length es))

instance {-# OVERLAPS #-}
  (Semiring weight, Ord a, Ord weight, Floating weight)
  => HasFun FloatingOp n (L4.LinComb weight) (MonadicRegExp (L4.LinComb weight) a) where
    fun GradArithMean es = G.return $ Fun GradArithMean $ V.map toExp es
    fun GradGeomMean  es = G.return $ Fun GradGeomMean $ V.map toExp es

instance {-# OVERLAPS #-}
  (Floating weight)
  => HasFun FloatingOp n (GradedModuleOfLinComb weight) (MonadicRegExp (GradedModuleOfLinComb weight) a) where
    fun GradArithMean es =
        Grd
            $ FunctorCompo
            $ combineToModule
                  (knownLength es SNat)
                  (GradFun "/*/" $ \xs ->
                      if null xs then 0 else sum xs / fromIntegral (length xs)
                  )
            $ fmap (run . \(Grd x) -> x) es
    fun GradGeomMean es =
        Grd
            $ FunctorCompo
            $ combineToModule
                  (knownLength es SNat)
                  ( GradFun "/**/"
                  $ \xs -> if null xs
                        then 1
                        else product xs ** (1 / fromIntegral (length xs))
                  )
            $ fmap (run . \(Grd x) -> x) es

arithMean, geomMean
    :: forall m n a
     . (Floating (m ()), HasFun FloatingOp n m (MonadicRegExp m a))
    => Vector n (MonadicRegExp m a)
    -> MonadicRegExp m a
arithMean = Fun GradArithMean
geomMean = Fun GradGeomMean

arithMean2, geomMean2
    :: forall m a
     . (Floating (m ()), HasFun FloatingOp 2 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
arithMean2 e1 e2 = arithMean $ fromTuple (e1, e2)
geomMean2 e1 e2 = geomMean $ fromTuple (e1, e2)

arithMean3, geomMean3
    :: forall m a
     . (Floating (m ()), HasFun FloatingOp 3 m (MonadicRegExp m a))
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
arithMean3 e1 e2 e3 = arithMean $ fromTuple (e1, e2, e3)
geomMean3 e1 e2 e3 = geomMean $ fromTuple (e1, e2, e3)

arithMean', geomMean'
    :: forall m a
     . ( Floating (m ())
       , forall n . HasFun FloatingOp n m (MonadicRegExp m a)
       )
    => UnknownSizedVect (MonadicRegExp m a)
    -> MonadicRegExp m a
arithMean' v = withSomevect v arithMean
geomMean' v = withSomevect v geomMean

instance HasName (NFun t) where
    name = f_name

instance (Castable t (m ()), Castable (m ()) t) => HasFun (NFun t) n m () where
    fun (GradFun _ f) v = cast $ f $ fmap cast v

instance HasFun (NFun t) n (GradedModuleOfLinComb t) (MonadicRegExp (GradedModuleOfLinComb t) a)where
    fun f v =
        Grd $ FunctorCompo $ combineToModule (knownLength v SNat) f $ fmap
            (run . \(Grd x) -> x)
            v

instance
  (Semiring t, Ord a, Ord t)
  => HasFun (NFun t) n (L4.LinComb t) (MonadicRegExp (L4.LinComb t) a) where
    fun f es = G.return $ Fun f $ V.map toExp es

instance (Semiring t, Show t, Eq t) => ToExp (GradedModuleOfLinComb t) where
    toExp (Grd (FunctorCompo (GradMod f@(GradFun s _) v)))
        | s == show (zero :: t) = Empty
        | s == "id"             = foldMap toExp' v
        | otherwise             = Fun f $ fmap toExp' v
      where
        toExp' (L4.LinComb l) = Map2.foldlWithKey
            (\acc e w -> leftAction' (GL.fromScalar w) e `plus'` acc)
            Empty
            l

gradExtDistFun :: (Num a, Ord a) => Graduation (NFun a) n
gradExtDistFun = GradFun "ExtDist" $ \v -> maximum v - minimum v

gradExtDist
    :: forall t m n a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) n m (MonadicRegExp m a))
       )
    => Vector n (MonadicRegExp m a)
    -> MonadicRegExp m a
gradExtDist (es :: Vector n (MonadicRegExp m a)) =
    knownLength es $ Fun (gradExtDistFun :: Graduation (NFun t) n) es

gradExtDist2
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) 2 m (MonadicRegExp m a))
       )
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
gradExtDist2 e1 e2 = gradExtDist @t $ fromTuple (e1, e2)

gradExtDist3
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) 3 m (MonadicRegExp m a))
       )
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
gradExtDist3 e1 e2 e3 = gradExtDist @t $ fromTuple (e1, e2, e3)

gradExtDist'
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , forall n . (HasFun (NFun t) n m (MonadicRegExp m a))
       )
    => UnknownSizedVect (MonadicRegExp m a)
    -> MonadicRegExp m a
gradExtDist' v = withSomevect v (gradExtDist @t)

gradExtMultFun :: (Num a, Ord a) => Graduation (NFun a) n
gradExtMultFun = GradFun "ExtMult" $ \v -> maximum v * minimum v

gradExtMult
    :: forall t m n a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) n m (MonadicRegExp m a))
       )
    => Vector n (MonadicRegExp m a)
    -> MonadicRegExp m a
gradExtMult (es :: Vector n (MonadicRegExp m a)) =
    knownLength es $ Fun (gradExtMultFun :: Graduation (NFun t) n) es

gradExtMult2
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) 2 m (MonadicRegExp m a))
       )
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
gradExtMult2 e1 e2 = gradExtMult @t $ fromTuple (e1, e2)

gradExtMult3
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , (HasFun (NFun t) 3 m (MonadicRegExp m a))
       )
    => MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
    -> MonadicRegExp m a
gradExtMult3 e1 e2 e3 = gradExtMult @t $ fromTuple (e1, e2, e3)

gradExtMult'
    :: forall t m a
     . ( Num t
       , Ord t
       , Castable t (m ())
       , Castable (m ()) t
       , forall n . (HasFun (NFun t) n m (MonadicRegExp m a))
       )
    => UnknownSizedVect (MonadicRegExp m a)
    -> MonadicRegExp m a
gradExtMult' v = withSomevect v (gradExtMult @t)


absoluteP1Fun :: Num a => Graduation (NFun a) 1
absoluteP1Fun = GradFun "abs+1" $ \v -> 1 + abs (head v)

absoluteP1
    :: forall t m a
     . ( Num t
       , HasFun (NFun t) 1 m (MonadicRegExp m a)
       , HasFun (NFun t) 1 m ()
       )
    => Vector 1 (MonadicRegExp m a)
    -> MonadicRegExp m a
absoluteP1 = Fun (absoluteP1Fun :: Graduation (NFun t) 1)
