{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
module RegExp.OpClass where

import           Data.Vector.Sized              ( Vector )
import           Graded.Graded                  ( Graded(Graduation) )
import           Prelude                 hiding ( head
                                                , last
                                                )

class HasFun op n m a where
    fun :: Graduation op n -> Vector n (m a) -> m a

class HasName op where
    name :: op -> String




