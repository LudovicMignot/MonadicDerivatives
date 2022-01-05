{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE FlexibleInstances      #-}

{-# LANGUAGE TypeApplications #-}
module RegExp.MonadicRegExpWithFunSpec where

import           Common                         ( Castable(cast) )
import           Data.List                      ( foldl'
                                                , inits
                                                , tails
                                                )
import           Data.Semiring                  ( Semiring(times) )
import qualified Data.Set                      as Set2
import           Data.Vector.Sized              ( Vector
                                                , fromTuple
                                                )
import           GenMonad.GenMonad             as G
                                                ( (>>)
                                                , GenMonad(return)
                                                )
import           LinComb.LinComb4               ( LinComb
                                                , fromScalar
                                                , toScalar
                                                )
import           RegExp.ArbitraryExp            ( ExtBoolProper(ExtBoolProper)
                                                , NoEps(NoEps)
                                                , Proper(Proper)
                                                )
import           RegExp.ExpDerivative           ( weightOf )
import           RegExp.MonadicRegExpWithFun    ( MonadicRegExp
                                                    ( Conc
                                                    , Epsilon
                                                    , LeftAction
                                                    , Star
                                                    )
                                                )
import           RegExp.MonadicRegExpWithFun   as R
                                                ( MonadicRegExp(Sum)
                                                , fromList
                                                )
import           RegExp.OpDef                   ( andExp
                                                , geomMean
                                                , implExp
                                                , notExp
                                                )
import           SemiRingsDef.SemiRingsDef      ( SR )
import           Test.Hspec                     ( Spec
                                                , describe
                                                , it
                                                , parallel
                                                , shouldBe
                                                )
import           Test.QuickCheck                ( NonEmptyList(NonEmpty)
                                                , Testable(property)
                                                , arbitrary
                                                , elements
                                                , forAll
                                                , listOf
                                                , resize
                                                )

spec :: Spec
spec = parallel $ do
    describe "deriveByWordProper'' (Proper)" $ do
        it
                "is 1 when a symbol list of length n is derived by itself (LinComb3 Int)"
            $ property
            $ \(NonEmpty s) ->
                  weightOf (s :: String) (R.fromList s)
                      `shouldBe` (G.return () :: LinComb (SR Int) ())
        it "is equivalent to derive E* or E.E*+Epsilon (Maybe)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(NoEps e) ->
                  weightOf s (Star e :: MonadicRegExp Maybe Char)
                      `shouldBe` weightOf s (R.Sum (Conc e (Star e)) Epsilon)
        it "is equivalent to derive E* or E.E*+Epsilon (Set)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(NoEps e) ->
                  weightOf s (Star e :: MonadicRegExp Set2.Set Char)
                      `shouldBe` weightOf s (R.Sum (Conc e (Star e)) Epsilon)
        it "is equivalent to derive E* or E.E*+Epsilon (LinComb3 Int)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 5 arbitrary) $ \(NoEps e) ->
                  weightOf s (Star e :: MonadicRegExp (LinComb (SR Int)) Char)
                      `shouldBe` weightOf s (R.Sum (Conc e (Star e)) Epsilon)
        it "is equivalent to derive 5.E* or 5.(E.E*+Epsilon) (LinComb3 Int)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(NoEps e) ->
                  weightOf
                          s
                          (LeftAction
                              (fromScalar 5)
                              (Star e :: MonadicRegExp (LinComb (SR Int)) Char)
                          )
                      `shouldBe` weightOf
                                     s
                                     (LeftAction
                                         (fromScalar 5)
                                         (R.Sum (Conc e (Star e)) Epsilon)
                                     )

    describe "derivatives of a sum" $ do
        it "returns the sum of derivatives (Proper, LinComb)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(Proper e) (Proper e') ->
                  weightOf s (Sum e e') `shouldBe` weightOf s e <> weightOf
                      s
                      (e' :: MonadicRegExp (LinComb (SR Int)) Char)
        it "returns the sum of derivatives (Proper, Maybe)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(Proper e) (Proper e') ->
                  weightOf s (Sum e e') `shouldBe` weightOf s e <> weightOf
                      s
                      (e' :: MonadicRegExp Maybe Char)
        it "returns the sum of derivatives (Proper, Set)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(Proper e) (Proper e') ->
                  weightOf s (Sum e e') `shouldBe` weightOf s e <> weightOf
                      s
                      (e' :: MonadicRegExp Set2.Set Char)
    describe "derivatives of geomMean"
        $ it "returns the geomMean of derivatives (Proper, LinComb)"
        $ forAll (resize 10 $ listOf $ elements "abcde")
        $ \s ->
              forAll (resize 15 arbitrary)
                  $ \(Proper e1) (Proper e2) (Proper e3) ->
                        let
                            r1 = weightOf
                                s
                                (geomMean
                                    (fromTuple
                                        ( e1
                                        , e2
                                        , e3 :: MonadicRegExp
                                            (LinComb (SR Double))
                                            Char
                                        ) :: Vector
                                          3
                                          ( MonadicRegExp
                                                (LinComb (SR Double))
                                                Char
                                          )
                                    )
                                )
                            r21 = weightOf s e1
                            r22 = weightOf s e2
                            r23 = weightOf s e3
                            r2' = r21 * r22 * r23
                            r2  = r2' ** (1 / 3)
                        in
                            isNaN (toScalar r1)
                            && isNaN (toScalar r2)
                            || r1
                            == r2
    describe "general formulae: sum" $ do
        it "returns the sum of the weights (LinComb (SR Double), Proper)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(Proper e1) (Proper e2) ->
                  weightOf
                          s
                          (Sum
                              (e1 :: MonadicRegExp (LinComb (SR Double)) Char)
                              e2
                          )
                      `shouldBe` weightOf s e1
                      <>         weightOf s e2

    describe "general formulae: conc" $ do
        it "returns the sum of the splitted weights (LinComb (SR Int), Proper)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 15 arbitrary) $ \(Proper e1) (Proper e2) ->
                  weightOf
                          s
                          (Conc (e1 :: MonadicRegExp (LinComb (SR Int)) Char) e2
                          )
                      `shouldBe` Data.List.foldl'
                                     (\acc (s1, s2) ->
                                         acc
                                             <> (    weightOf s1 e1
                                                G.>> weightOf s2 e2
                                                )
                                     )
                                     mempty
                                     (allSplits s)
    describe "general formulae: star" $ do
        it "returns the sum of the splitted weights (LinComb (SR Int), Proper)"
            $ forAll (resize 10 $ listOf $ elements "abcde")
            -- dans la suite, NoEps car on étoile l'expression
            $ \s -> forAll (resize 15 arbitrary) $ \(NoEps e) ->
                  weightOf s (Star (e :: MonadicRegExp (LinComb (SR Int)) Char))
                      `shouldBe` if null s
                                     then G.return ()
                                     else Data.List.foldl'
                                         (\acc (s1, s2) ->
                                             acc
                                                 <> (       weightOf s1 e
                                                    `times` weightOf
                                                                s2
                                                                (Star e)
                                                    )
                                         )
                                         mempty
                                         (allSplits s)
    describe "general formulae: extended Boolean operators" $ do

        it " Negation returns the negation of the weights (Set, ExtBoolProper)"
            $ forAll (resize 7 $ listOf $ elements "abcde")
            $ \s -> forAll (resize 10 arbitrary) $ \(ExtBoolProper e) ->
                  cast (weightOf s (notExp (e :: MonadicRegExp Set2.Set Char)))
                      `shouldBe` not (cast (weightOf s e))
        it
                "Intersection returns the conjunction of the weights (Set, ExtBoolProper)"
            $ forAll (resize 7 $ listOf $ elements "abcde")
            $ \s ->
                  forAll (resize 10 arbitrary)
                      $ \(ExtBoolProper e1) (ExtBoolProper e2) ->
                            let
                                res  = cast res'
                                res' = weightOf
                                    s
                                    (andExp
                                        (e1 :: MonadicRegExp Set2.Set Char)
                                        e2
                                    )
                            in
                                res
                                    `shouldBe` (  cast (weightOf s e1)
                                               && cast (weightOf s e2)
                                               )
        it "-> returns the implication of the weights (Set, ExtBoolProper)"
            $ forAll (resize 7 $ listOf $ elements "abcde")
            $ \s ->
                  forAll (resize 10 arbitrary)
                      $ \(ExtBoolProper e1) (ExtBoolProper e2) ->
                            let
                                res  = cast res'
                                res' = weightOf
                                    s
                                    (implExp
                                        (e1 :: MonadicRegExp Set2.Set Char)
                                        e2
                                    )
                            in
                                res
                                    `shouldBe` (  not (cast (weightOf s e1))
                                               || cast (weightOf s e2)
                                               )
    where allSplits s = Prelude.zip (inits s) (tails s)

