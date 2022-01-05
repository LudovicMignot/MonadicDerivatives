{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Type.UnknownSizedVect where

import           Data.Vector.Sized              ( Vector
                                                , cons
                                                , empty
                                                , knownLength
                                                )

data UnknownSizedVect a where
    Somevect ::Vector n a -> UnknownSizedVect a

withSomevect :: UnknownSizedVect a -> (forall n . Vector n a -> b) -> b
withSomevect (Somevect v) f = knownLength v $ f v

concatToSome :: a -> UnknownSizedVect a -> UnknownSizedVect a
concatToSome a uv = withSomevect uv (\v -> Somevect $ a `cons` v)

fromList :: [a] -> UnknownSizedVect a
fromList = Prelude.foldr concatToSome (Somevect empty)

