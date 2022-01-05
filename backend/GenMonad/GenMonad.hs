{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module GenMonad.GenMonad where

import           Control.Monad.State.Lazy       ( StateT(StateT)
                                                , runStateT
                                                )
import qualified Data.Set                      as Set
import           GHC.Exts                       ( Constraint )
import           Prelude                 hiding ( (<$)
                                                , (>>)
                                                , (>>=)
                                                , fmap
                                                , return
                                                )
import qualified Prelude                       as P
                                                ( (>>=)
                                                , return
                                                )

class GenMonad m where
  type GenMonadConstraint m val :: Constraint
  type GenMonadConstraint m val = ()

  (>>=) :: (GenMonadConstraint m a, GenMonadConstraint m b) => m a -> (a -> m b) -> m b
  default (>>=) :: Monad m => m a -> (a -> m b) -> m b
  (>>=) = (P.>>=)

  return :: GenMonadConstraint m a => a -> m a
  default return :: Monad m => a -> m a
  return = P.return

  fmap :: (GenMonadConstraint m a, GenMonadConstraint m b) => (a -> b) -> m a -> m b
  fmap f m_a = m_a >>= (return . f)

  (<$)        :: (GenMonadConstraint m a, GenMonadConstraint m b) => a -> m b -> m a
  (<$)        =  fmap . const

  ($>) :: (GenMonadConstraint m a, GenMonadConstraint m b) =>m a -> b -> m b
  ($>) = flip (<$)

  (<$>) :: (GenMonadConstraint m a, GenMonadConstraint m b) => (a -> b) -> m a -> m b
  (<$>) = fmap

  (<&>) :: (GenMonadConstraint m a, GenMonadConstraint m b) => m a -> (a -> b) -> m b
  (<&>) = flip fmap

  (>>) :: (GenMonadConstraint m a, GenMonadConstraint m b) => m a -> m b -> m b
  m_a >> m_b = m_a >>= const m_b

  (*>) :: (GenMonadConstraint m a, GenMonadConstraint m ()) => m () -> m a -> m a
  (*>) = (>>)

  (<*) :: (GenMonadConstraint m a, GenMonadConstraint m ()) => m a -> m () -> m a
  m_a <* m = m_a >>= \_ -> m >>= const m_a

  (>=>) :: (GenMonadConstraint m a, GenMonadConstraint m b, GenMonadConstraint m c) => (a -> m b) -> (b -> m c) -> a -> m c
  f >=> g = \a -> f a >>= g

  join :: (GenMonadConstraint m (m a), GenMonadConstraint m a) => m (m a) -> m a
  join m = m >>= id

  liftM2 :: (GenMonadConstraint m a, GenMonadConstraint m b, GenMonadConstraint m c) => (a -> b -> c) -> m a -> m b -> m c
  liftM2 f mx my = mx >>= \x -> my >>= \y -> return $ f x y

instance GenMonad Maybe

instance GenMonad Set.Set where
  type GenMonadConstraint Set.Set val = Ord val

  return = Set.singleton

  (>>=)  = flip foldMap

instance GenMonad m => GenMonad (StateT s m) where
  type GenMonadConstraint (StateT s m) val = GenMonadConstraint m (val, s)

  return x = StateT $ \s -> return (x, s)

  StateT f >>= g = StateT $ \s' -> f s' >>= \(a, s) -> runStateT (g a) s
