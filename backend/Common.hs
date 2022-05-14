{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Common where

import           Data.Semiring                  ( Semiring )
import qualified Data.Set                      as Set2
import           Data.Star                      ( Star
                                                , star
                                                )
import           GenMonad.GenMonad             as G
                                                ( GenMonad(return) )
import           Graded.GradedFun               ( Graduation(GradFun) )
import           Graded.GradedModule            ( GradedModule(GradMod) )
import           Graded.GradedModuleOfLinComb   ( FunctorCompo(..)
                                                , GradedModuleOfLinComb(..)
                                                )
import qualified Graded.GradedModuleOfLinComb  as GL
import           LinComb.LinComb4              as L4
                                                ( LinComb
                                                , fromScalar
                                                , toScalar
                                                )
import           Text.Read                      ( readMaybe )
import           ToString.ToString              ( ToString(toString) )

class Castable t1 t2 where
  cast :: t1 -> t2

type IsBool t = (Castable t Bool, Castable Bool t)

instance {-# OVERLAPS #-} Castable a a where
  cast = id

instance Castable t (LinComb t ()) where
  cast = L4.fromScalar

instance Semiring t => Castable (LinComb t ()) t where
  cast = L4.toScalar

instance {-# OVERLAPS #-} (Semiring b, Castable b t) => Castable (GradedModuleOfLinComb b ()) t where
  cast (Grd (FunctorCompo (GradMod (GradFun _ f) v))) = cast $ f $ fmap cast v

instance {-# OVERLAPS #-} (Castable t b, ToString b) => Castable t (GradedModuleOfLinComb b ()) where
  cast b = GL.fromScalar $ cast b

instance Castable (Maybe ()) Bool where
  cast Nothing   = False
  cast (Just ()) = True

instance Castable Bool (Maybe ()) where
  cast False = Nothing
  cast True  = Just ()

instance Castable (Set2.Set ()) Bool where
  cast = not . Set2.null

instance Castable Bool (Set2.Set ()) where
  cast False = Set2.empty
  cast True  = G.return ()

instance Star (Maybe ()) where
  star _ = Just ()

instance Star (Set2.Set ()) where
  star _ = Set2.singleton ()

class (Read (ReadProxy t), Castable (ReadProxy t) t) => ReadVia t where
  type ReadProxy t
  readMaybeVia :: String -> Maybe t
  readMaybeVia s = cast <$> (readMaybe s :: Maybe (ReadProxy t))

instance (Read b, Show b) => ReadVia (GradedModuleOfLinComb b ()) where
  type ReadProxy (GradedModuleOfLinComb b ()) = b

instance Read b => ReadVia (LinComb b ()) where
  type ReadProxy (LinComb b ()) = b

instance ReadVia (Maybe ()) where
  type ReadProxy (Maybe ()) = Bool

instance ReadVia (Set2.Set ()) where
  type ReadProxy (Set2.Set ()) = Bool

class (ToString (ToStringProxy t), Castable t (ToStringProxy t)) => ToStringVia t where
  type ToStringProxy t
  toStringVia :: t -> String
  toStringVia t = toString (cast t :: ToStringProxy t)

instance (Semiring b, ToString b) => ToStringVia (GradedModuleOfLinComb b ()) where
  type ToStringProxy (GradedModuleOfLinComb b ()) = b

instance (Semiring b, ToString b) => ToStringVia (LinComb b ()) where
  type ToStringProxy (LinComb b ()) = b

instance ToStringVia (Maybe ()) where
  type ToStringProxy (Maybe ()) = Bool

instance ToStringVia (Set2.Set ()) where
  type ToStringProxy (Set2.Set ()) = Bool
