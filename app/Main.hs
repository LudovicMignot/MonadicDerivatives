module Main where

import           API.API                        ( app )
import           Data.Maybe                     ( fromMaybe )
import           Network.Wai.Handler.Warp       ( run )
import           System.Environment             ( lookupEnv )
import           Text.Read                      ( readMaybe )

main :: IO ()
main = do
    port <- lookupEnv "PORT"
    run (fromMaybe 8081 $ port >>= readMaybe) app
