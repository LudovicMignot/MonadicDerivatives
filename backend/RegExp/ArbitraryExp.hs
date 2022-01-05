{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
module RegExp.ArbitraryExp where

import           Common                         ( IsBool
                                                , ToStringVia
                                                )
import           Prelude                 hiding ( (*>)
                                                , (<*)
                                                , (>>=)
                                                , return
                                                )
import qualified Prelude                       as P
                                                ( return )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp
                                                    ( Atom
                                                    , Empty
                                                    , Epsilon
                                                    , LeftAction
                                                    , Star
                                                    )
                                                , conc'
                                                , plus'
                                                )
import           RegExp.OpClass                 ( HasFun )
import           RegExp.OpDef                   ( BooleanOp
                                                , and'
                                                , impl'
                                                , notExp
                                                )
import           Test.QuickCheck                ( Arbitrary(arbitrary)
                                                , Gen
                                                , choose
                                                , elements
                                                , frequency
                                                , oneof
                                                , sized
                                                )
import           ToString.ToString              ( ToString )

instance Arbitrary (m ()) => Arbitrary (MonadicRegExp m Char) where
    arbitrary = sized (\n -> (\(Proper e) -> e) <$> sizedProperExp n)

newtype Proper m a = Proper (MonadicRegExp m a)
deriving via
  (MonadicRegExp m a)
  instance
    (ToStringVia (m ()), ToString a) =>
    ToString (Proper m a)
deriving via
  (MonadicRegExp m a)
  instance
    (ToStringVia (m ()), ToString a) =>
    Show (Proper m a)

newtype NoEps m a = NoEps (MonadicRegExp m a)
deriving via
  (MonadicRegExp m a)
  instance
    (ToStringVia (m ()), ToString a) =>
    ToString (NoEps m a)
deriving via
  (MonadicRegExp m a)
  instance
    (ToStringVia (m ()), ToString a) =>
    Show (NoEps m a)

instance Arbitrary (m ()) => Arbitrary (NoEps m Char) where
    arbitrary = sized sizedNoEpsExp

instance Arbitrary (m ()) => Arbitrary (Proper m Char) where
    arbitrary = sized sizedProperExp

sizedProperExp :: (Arbitrary (m ())) => Int -> Gen (Proper m Char)
sizedProperExp 0 = frequency
    [ (8, Proper . Atom <$> elements ['a' .. 'e'])
    , (1, elements [Proper Epsilon, Proper Empty])
    ]
sizedProperExp n = do
    frequency
        [ ( 1
          , do
              NoEps e <- sizedNoEpsExp (n - 1)
              P.return $ Proper $ Star e
          )
        , ( 1
          , do
              Proper e <- sizedProperExp (n - 1)
              w        <- arbitrary
              P.return $ Proper $ LeftAction w e
          )
        , ( 2
          , do
              k'        <- choose (0, n - 1)
              op        <- elements [conc', plus']
              Proper e1 <- sizedProperExp (n - 1 - k')
              Proper e2 <- sizedProperExp k'
              P.return $ Proper $ op e1 e2
          )
        ]

sizedNoEpsExp :: Arbitrary (m ()) => Int -> Gen (NoEps m Char)
sizedNoEpsExp 0 = NoEps . Atom <$> elements ['a' .. 'e']
sizedNoEpsExp n = oneof
    [ do
        k'       <- choose (0, n - 1)
        NoEps e1 <- sizedNoEpsExp (n - 1 - k')
        NoEps e2 <- sizedNoEpsExp k'
        P.return $ NoEps $ plus' e1 e2
    , do
        k' <- choose (0, n - 1)
        oneof
            [ do
                Proper e1 <- sizedProperExp (n - 1 - k')
                NoEps  e2 <- sizedNoEpsExp k'
                P.return $ NoEps $ conc' e1 e2
            , do
                Proper e2 <- sizedProperExp k'
                NoEps  e1 <- sizedNoEpsExp (n - 1 - k')
                P.return $ NoEps $ conc' e1 e2
            ]
    , do
        NoEps e <- sizedNoEpsExp (n - 1)
        w       <- arbitrary
        P.return $ NoEps $ LeftAction w e
    ]

data ExtBoolProper m a where
    ExtBoolProper ::IsBool (m ()) => MonadicRegExp m a -> ExtBoolProper m a
instance (Show a, ToStringVia (m ())) => Show (ExtBoolProper m a) where
    show (ExtBoolProper e) = show e

data ExtBoolNoEps m a where
    ExtBoolNoEps ::IsBool (m ()) => MonadicRegExp m a -> ExtBoolNoEps m a
instance (Show a, ToStringVia (m ())) => Show (ExtBoolNoEps m a) where
    show (ExtBoolNoEps e) = show e

instance (Arbitrary (m ()) , IsBool (m ()),
  HasFun BooleanOp 1 m (MonadicRegExp m Char)
       , HasFun BooleanOp 2 m (MonadicRegExp m Char))  => Arbitrary (ExtBoolNoEps m Char) where
    arbitrary = sized sizedNoEpsExtExp

instance (Arbitrary (m ()) , IsBool (m ()), HasFun BooleanOp 1 m (MonadicRegExp m Char)
       , HasFun BooleanOp 2 m (MonadicRegExp m Char)) => Arbitrary (ExtBoolProper m Char) where
    arbitrary = sized sizedExtProperExp

sizedExtProperExp
    :: ( IsBool (m ())
       , Arbitrary (m ())
       , HasFun BooleanOp 1 m (MonadicRegExp m Char)
       , HasFun BooleanOp 2 m (MonadicRegExp m Char)
       )
    => Int
    -> Gen (ExtBoolProper m Char)
sizedExtProperExp 0 = frequency
    [ (8, ExtBoolProper . Atom <$> elements ['a' .. 'e'])
    , (1, elements [ExtBoolProper Epsilon, ExtBoolProper Empty])
    ]
sizedExtProperExp n = do
    frequency
        [ ( 1
          , do
              ExtBoolNoEps e <- sizedNoEpsExtExp (n - 1)
              P.return $ ExtBoolProper $ Star e
          )
        , ( length unOps
          , do
              op              <- elements unOps
              ExtBoolProper e <- sizedExtProperExp (n - 1)
              P.return $ ExtBoolProper $ op e
          )
        , ( 1
          , do
              ExtBoolProper e <- sizedExtProperExp (n - 1)
              w               <- arbitrary
              P.return $ ExtBoolProper $ LeftAction w e
          )
        , ( length binOps
          , do
              k'               <- choose (0, n - 1)
              op               <- elements binOps
              ExtBoolProper e1 <- sizedExtProperExp (n - 1 - k')
              ExtBoolProper e2 <- sizedExtProperExp k'
              P.return $ ExtBoolProper $ op e1 e2
          )
        ]
  where
    binOps = [conc', plus', and', impl']
    unOps  = [notExp]

sizedNoEpsExtExp
    :: ( IsBool (m ())
       , Arbitrary (m ())
       , HasFun BooleanOp 1 m (MonadicRegExp m Char)
       , HasFun BooleanOp 2 m (MonadicRegExp m Char)
       )
    => Int
    -> Gen (ExtBoolNoEps m Char)
sizedNoEpsExtExp 0 = ExtBoolNoEps . Atom <$> elements ['a' .. 'e']
sizedNoEpsExtExp n = oneof
    [ do
        k'              <- choose (0, n - 1)
        ExtBoolNoEps e1 <- sizedNoEpsExtExp (n - 1 - k')
        ExtBoolNoEps e2 <- sizedNoEpsExtExp k'
        P.return $ ExtBoolNoEps $ plus' e1 e2
    , do
        k' <- choose (0, n - 1)
        oneof
            [ do
                ExtBoolProper e1 <- sizedExtProperExp (n - 1 - k')
                ExtBoolNoEps  e2 <- sizedNoEpsExtExp k'
                P.return $ ExtBoolNoEps $ conc' e1 e2
            , do
                ExtBoolProper e2 <- sizedExtProperExp k'
                ExtBoolNoEps  e1 <- sizedNoEpsExtExp (n - 1 - k')
                P.return $ ExtBoolNoEps $ conc' e1 e2
            ]
    , do
        ExtBoolNoEps e <- sizedNoEpsExtExp (n - 1)
        w              <- arbitrary
        P.return $ ExtBoolNoEps $ LeftAction w e
    , do
        ExtBoolNoEps e <- sizedNoEpsExtExp (n - 1)
        P.return $ ExtBoolNoEps $ notExp $ e `plus'` Epsilon
    , do
        k' <- choose (0, n - 1)
        oneof
            [ do
                ExtBoolProper e1 <- sizedExtProperExp (n - 1 - k')
                ExtBoolNoEps  e2 <- sizedNoEpsExtExp k'
                P.return $ ExtBoolNoEps $ and' e1 e2
            , do
                ExtBoolProper e2 <- sizedExtProperExp k'
                ExtBoolNoEps  e1 <- sizedNoEpsExtExp (n - 1 - k')
                P.return $ ExtBoolNoEps $ and' e1 e2
            ]
    , do
        k'              <- choose (0, n - 1)
        ExtBoolNoEps e1 <- sizedNoEpsExtExp (n - 1 - k')
        ExtBoolNoEps e2 <- sizedNoEpsExtExp k'
        P.return $ ExtBoolNoEps $ impl' (e1 `plus'` Epsilon) e2
    ]

