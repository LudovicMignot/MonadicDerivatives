
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE StandaloneKindSignatures  #-}

module Singletons.Singletons where

import qualified Data.Set                      as Set2
import           Data.Singletons
import           Data.Singletons.CustomStar
import           Graded.GradedModule            ( GradedModule )
import           Graded.GradedModuleOfLinComb   ( GradedModuleOfLinComb )
import qualified LinComb.LinComb4              as L4
import           SemiRingsDef.SemiRingsDef      ( SR )

type Unit = ()

$(singletonStar [''SR, ''Int, ''Bool, ''Maybe, ''Unit, ''L4.LinComb, ''GradedModule, ''Set2.Set, ''GradedModuleOfLinComb, ''Char, ''Double])
