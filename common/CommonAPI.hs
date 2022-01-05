{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
module CommonAPI where

import           Data.Aeson.Types               ( FromJSON
                                                , ToJSON
                                                )
import           GHC.Generics                   ( Generic )
import           Servant.API                    ( type (:<|>)
                                                , type (:>)
                                                , Get
                                                , JSON
                                                , QueryParam
                                                )

type DerCompAPI
  = "dercomp" :> QueryParam "expr" String :> QueryParam "word" String :> Get '[JSON] DerComp
  :<|> "alea" :> Get '[JSON] String

data DerComp = DerComp
  { valid_expr         :: Bool
  , valid_word         :: Bool
  , res_maybe          :: (String, String, String)
  , res_set            :: (String, String, String)
  , res_lincomb_bool   :: (String, String, String)
  , res_lincomb_int    :: (String, String, String)
  , res_lincomb_double :: (String, String, String)
  }
  deriving (Eq, Show, Generic)

instance ToJSON DerComp
instance FromJSON DerComp

invalidTriple :: (String, String, String)
invalidTriple = ("[Invalid Input]", "[Invalid Input]", "[Invalid Input]")

invalidRep :: DerComp
invalidRep = DerComp False
                     False
                     invalidTriple
                     invalidTriple
                     invalidTriple
                     invalidTriple
                     invalidTriple
                    --  invalidTriple
                    --  invalidTriple
                    --  invalidTriple


