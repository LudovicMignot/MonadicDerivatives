module Main where

import           Debug.Trace                    ( trace )
import           MainWeb                        ( body
                                                , header
                                                )
import           Reflex.Dom                     ( mainWidgetWithHead )


main :: IO ()
main =
    trace "starting the app...\n loading..." $ mainWidgetWithHead header body
