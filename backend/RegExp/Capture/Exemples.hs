module RegExp.Capture.Exemples where

import Control.Monad.State.Lazy (runStateT)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GenMonad.GenMonad
  ( (>>=),
  )
import RegExp.Capture.Capture
  ( CaptureMonadicRegExp (Atom, Epsilon, Star),
    capture,
    deriveByWordProper,
    nullableProper,
    (<<+>>),
    (<<.>>),
  )
import Prelude hiding (fmap, return, (<$>), (>>), (>>=))

-- exemples
a :: CaptureMonadicRegExp Set.Set Int Char
a = Atom 'a'

b :: CaptureMonadicRegExp Set.Set Int Char
b = Atom 'b'

exp1 :: CaptureMonadicRegExp Set.Set Int Char
exp1 = a <<+>> b

exp2 :: CaptureMonadicRegExp Set.Set Int Char
exp2 = a <<+>> b <<+>> Epsilon

exp3 :: CaptureMonadicRegExp Set.Set Int Char
exp3 = a <<.>> b

exp4 :: CaptureMonadicRegExp Set.Set Int Char
exp4 = capture 1 (Star a) <<.>> capture 2 (Star b)

exp5 :: CaptureMonadicRegExp Set.Set Int Char
exp5 = capture 1 (Star a) <<.>> capture 2 (Star b) <<.>> b

res :: CaptureMonadicRegExp Set.Set Int Char -> Set.Set (Set.Set (), Map Int [Char])
res e = runStateT (nullableProper e) Map.empty

resderiv :: CaptureMonadicRegExp Set.Set Int Char -> [Char] -> Set.Set (Set.Set (), Map Int [Char])
resderiv e w = runStateT (deriveByWordProper w e >>= nullableProper) Map.empty
