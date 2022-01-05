{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module ToString.ToString where

import           Data.List                      ( intercalate )
import           Data.Monoid                    ( Sum(Sum) )
import           Data.Set                      as Set
                                                ( Set
                                                , toList
                                                )

class ToString t where
  toString :: t -> String

  print' :: t -> IO ()
  print' = putStrLn . toString

  toHTMLString :: t -> String
  toHTMLString = toString

instance {-# OVERLAPS #-} ToString Char where
    toString t = [t]

instance {-# OVERLAPS #-} ToString n => ToString (Sum n) where
    toString (Sum n) = toString n

instance {-# OVERLAPS #-} ToString String where
    toString = id

instance Show t => ToString t where
    toString = show

instance {-# OVERLAPS #-} ToString t => ToString (Maybe t) where
    toString Nothing  = "Nothing"
    toString (Just t) = "Just " ++ toString t

    toHTMLString Nothing =
        "<span style=\"font-weight : bold; color : blue\" >Nothing</span>"
    toHTMLString (Just t) =
        "<span style=\"font-weight : bold; color : blue\" >Just </span>"
            ++ toHTMLString t

instance {-# OVERLAPS #-} ToString t => ToString [t] where
    toString ts = "[" ++ intercalate ", " (toString <$> ts) ++ "]"

    toHTMLString ts =
        "<span style=\"font-weight : bold; color : blue\" >[</span>"
            ++ intercalate
                   "<span style=\"font-weight : bold; color : blue\" >, </span>"
                   (toHTMLString <$> ts)
            ++ "<span style=\"font-weight : bold; color : blue\" >]</span>"

instance {-# OVERLAPS #-} ToString t => ToString (Set t) where
    toString ts = "{" ++ intercalate ", " (toString <$> Set.toList ts) ++ "}"

    toHTMLString ts =
        "<span style=\"font-weight : bold; color : blue\" >{</span>"
            ++ intercalate
                   "<span style=\"font-weight : bold; color : blue\" >, </span>"
                   (toHTMLString <$> Set.toList ts)
            ++ "<span style=\"font-weight : bold; color : blue\" >}</span>"
