{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}


module RegExp.ExpDerivative where

import           Data.Foldable                  ( foldl' )
import           Data.Star                      ( Star
                                                , star
                                                )
import           Data.Vector.Sized             as V
                                                ( map )
import           GenMonad.GenMonad              ( GenMonad
                                                   ( (>=>)
                                                   , (>>=)
                                                   , GenMonadConstraint
                                                   , return
                                                   )
                                                )
import           Prelude                 hiding ( (*>)
                                                , (<*)
                                                , (>>=)
                                                , return
                                                )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp(..)

                                                -- , nullable
                                                , nullable
                                                , nullableProper'
                                                )
import           RegExp.OpClass                 ( HasFun(fun) )
import           Semimodule.Semimodule          ( Semimodule(..) )

deriveBySymb
   :: ( Eq a
      , Star (m ())
      , GenMonad m
      , GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => a
   -> MonadicRegExp m a
   -> m (MonadicRegExp m a)
deriveBySymb _ Empty   = mempty -- return Empty
deriveBySymb _ Epsilon = mempty -- return Empty
deriveBySymb a (Atom b) | a == b    = return Epsilon
                        | otherwise = mempty -- return Empty
deriveBySymb a (Fun op es) = fun op $ V.map (deriveBySymb a) es
deriveBySymb a (Sum e1 e2) = deriveBySymb a e1 `mappend` deriveBySymb a e2
deriveBySymb a (Conc e1 e2) =
   (deriveBySymb a e1 `rightAction` e2)
      `mappend` (nullable e1 `leftAction` deriveBySymb a e2)
deriveBySymb a estar@(Star e) =
   star (nullable e) `leftAction` deriveBySymb a e `rightAction` estar
deriveBySymb a (LeftAction  w e) = w `leftAction` deriveBySymb a e
deriveBySymb a (RightAction e w) = deriveBySymb a e `rightAction` w

deriveByWord
   :: ( Eq a
      , Star (m ())
      , GenMonad m
      , GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => [a]
   -> MonadicRegExp m a
   -> m (MonadicRegExp m a)
deriveByWord = foldl' (\acc a -> acc >=> deriveBySymb a) return

-- !!! valable uniquement pour les expressions propres
deriveBySymbProper
   :: ( Eq a
      , Monoid (m ())
      , GenMonad m
      , GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => a
   -> MonadicRegExp m a
   -> m (MonadicRegExp m a)
deriveBySymbProper _ Empty   = mempty
deriveBySymbProper _ Epsilon = mempty
deriveBySymbProper a (Atom b) | a == b    = return Epsilon
                              | otherwise = mempty
deriveBySymbProper a (Sum e1 e2) =
   deriveBySymbProper a e1 <> deriveBySymbProper a e2
deriveBySymbProper a (Conc e1 e2) =
   (deriveBySymbProper a e1 `rightAction` e2)
      <> (nullableProper' e1 `leftAction` deriveBySymbProper a e2)
deriveBySymbProper a estar@(Star e) =
   deriveBySymbProper a e `rightAction` estar
deriveBySymbProper a (LeftAction w e) = w `leftAction` deriveBySymbProper a e
deriveBySymbProper a (RightAction e w) = deriveBySymbProper a e `rightAction` w
deriveBySymbProper a (Fun op es) = fun op $ V.map (deriveBySymbProper a) es

deriveByWordProper
   :: ( Eq a
      , Monoid (m ())
      , GenMonad m
      , GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => [a]
   -> MonadicRegExp m a
   -> m (MonadicRegExp m a)
deriveByWordProper = foldl' (\acc a -> acc >=> deriveBySymbProper a) return

deriveByWordProper'
   :: ( Eq a
      , Monoid (m ())
      , GenMonad m
      , GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => [a]
   -> MonadicRegExp m a
   -> m (MonadicRegExp m a)
deriveByWordProper' [] e = return e
deriveByWordProper' (a : w) e =
   deriveBySymbProper a e >>= deriveByWordProper' w

weightOf
   :: ( GenMonadConstraint m (MonadicRegExp m a)
      , GenMonadConstraint m ()
      , GenMonad m
      , Eq a
      , Monoid (m ())
      , Semimodule (MonadicRegExp m a) (m (MonadicRegExp m a))
      , Semimodule (m ()) (m (MonadicRegExp m a))
      )
   => [a]
   -> MonadicRegExp m a
   -> m ()
weightOf s e = deriveByWordProper' s e >>= nullableProper'
