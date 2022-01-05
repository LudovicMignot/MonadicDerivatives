
module Parser.RegExpFromString where

import           Common                         ( ReadVia )
import           Control.Monad                  ( join )
import           Data.Singletons                ( SingI )
import qualified Parser.RegExpParser           as H
                                                ( expfromString )
import           Parser.RegExpTok               ( alexScanTokens )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp )


expFromString
    :: (ReadVia (m ()), SingI (m ())) => String -> Maybe (MonadicRegExp m Char)
expFromString = join . H.expfromString . alexScanTokens

