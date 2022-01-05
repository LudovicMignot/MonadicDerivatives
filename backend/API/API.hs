{-# LANGUAGE ExplicitNamespaces #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module API.API where

import           Common                         ( ReadVia
                                                , ToStringVia(toStringVia)
                                                )
import           CommonAPI                      ( DerComp(DerComp)
                                                , DerCompAPI
                                                , invalidRep
                                                )
import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Data.Maybe                     ( isJust )
import           Data.Set                       ( Set )
import           Data.Singletons                ( SingI )
import           GenMonad.GenMonad              ( GenMonad
                                                , GenMonadConstraint
                                                )
import qualified LinComb.LinComb4              as L4
import           Network.Wai.Middleware.Cors    ( simpleCors )
import           Parser.RegExpFromString        ( expFromString )
import           RegExp.ArbitraryExp            ( )
import           RegExp.ExpDerivative           ( deriveByWordProper
                                                , weightOf
                                                )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp
                                                , isProper
                                                )
import           SemiRingsDef.SemiRingsDef      ( SR )
import           Semimodule.Semimodule          ( Semimodule )
import           Servant                        ( type (:<|>)((:<|>))
                                                , Application
                                                , Handler
                                                , Proxy(..)
                                                , Server
                                                , serve
                                                )
import           Test.QuickCheck                ( Arbitrary(arbitrary)
                                                , generate
                                                , resize
                                                )
import           ToString.ToString              ( ToString
                                                  ( toHTMLString
                                                  , toString
                                                  )
                                                )

isValidWord :: [Char] -> Bool
isValidWord = all (`elem` (['a' .. 'z'] :: String))

mToString :: ToString a => Maybe a -> String
mToString = maybe "[Invalid Input]" toString

mToStringVia :: ToStringVia a => Maybe a -> String
mToStringVia = maybe "[Invalid Input]" toStringVia

mToHTMLString :: ToString a => Maybe a -> String
mToHTMLString = maybe "[Invalid Input]" toHTMLString

filterMaybe :: (a -> Bool) -> Maybe a -> Maybe a
filterMaybe f (Just a) | f a = Just a
filterMaybe _ _              = Nothing

computeRes
  :: forall (m' :: * -> *)
   . ( ToStringVia (m' ())
     , SingI (m' ())
     , Semimodule (m' ()) (m' (MonadicRegExp m' Char))
     , GenMonadConstraint m' (MonadicRegExp m' Char)
     , GenMonadConstraint m' ()
     , ToString (m' (MonadicRegExp m' Char))
     , ReadVia (m' ())
     , Semimodule (MonadicRegExp m' Char) (m' (MonadicRegExp m' Char))
     , GenMonad m'
     , Monoid (m' ())
     , Eq (m' ())
     )
  => String
  -> String
  -> (Bool, (String, String, String))
computeRes e w =
  ( isJust m_expr
  , (mToString m_expr, mToHTMLString m_res, mToStringVia m_weight)
  )
 where
  m_expr =
    filterMaybe isProper $ expFromString e :: Maybe (MonadicRegExp m' Char)
  m_res    = deriveByWordProper w <$> m_expr
  m_weight = weightOf w <$> m_expr

getAlea :: MonadIO m => m String
getAlea = liftIO $ fmap
  (either toString toString)
  (generate $ resize 5 arbitrary :: IO
      (Either (MonadicRegExp Maybe Char) (MonadicRegExp (L4.LinComb Int) Char))
  )

server :: Server DerCompAPI
server = derivation :<|> getAlea
 where
  derivation :: Maybe String -> Maybe String -> Handler DerComp
  derivation Nothing _       = return invalidRep
  derivation _       Nothing = return invalidRep
  derivation (Just e) (Just w)
    | not (isValidWord w) = return invalidRep
    | otherwise = return $ DerComp (b_m || b_s || b_lb || b_li || b_ld)
                                   True
                                   res_m
                                   res_s
                                   res_lbool
                                   res_lint
                                   res_ldouble
   where
    (b_m , res_m      ) = computeRes @Maybe e w
    (b_s , res_s      ) = computeRes @Set e w
    (b_lb, res_lbool  ) = computeRes @(L4.LinComb (SR Bool)) e w
    (b_li, res_lint   ) = computeRes @(L4.LinComb (SR Int)) e w
    (b_ld, res_ldouble) = computeRes @(L4.LinComb (SR Double)) e w


derCompAPI :: Proxy DerCompAPI
derCompAPI = Proxy

app :: Application
app = simpleCors $ serve derCompAPI server
