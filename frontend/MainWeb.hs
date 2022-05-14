{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module MainWeb where

import           CommonAPI                      ( DerComp
                                                    (  res_gradmodoflincomb_double
                                                     , res_gradmodoflincomb_int
                                                     , res_gradmodoflincomb_bool
                                                     ,
                                                    res_lincomb_bool
                                                    , res_lincomb_double
                                                    , res_lincomb_int
                                                    , res_maybe
                                                    , res_set
                                                    , valid_expr
                                                    , valid_word
                                                    )
                                                , DerCompAPI
                                                , invalidRep
                                                )
import           Control.Monad                  ( join )
import           Control.Monad.Cont             ( MonadIO(liftIO) )
import           Data.Functor                   ( void )
import qualified Data.Map                      as Map
import           Data.Proxy                     ( Proxy(..) )
import qualified Data.Text                     as T
import           Reflex                         ( Reflex(updated)
                                                , fmapMaybe
                                                , leftmost
                                                )
import           Reflex.Dom                     ( (&)
                                                , (.~)
                                                , (=:)
                                                , Dynamic
                                                , Event
                                                , EventName(Click)
                                                , HasDomEvent(domEvent)
                                                , MonadHold(holdDyn)
                                                , MonadWidget
                                                , PerformEvent(performEvent)
                                                , constDyn
                                                , def
                                                , dyn
                                                , dynText
                                                , el
                                                , elAttr, elDynAttr
                                                , elAttr', elDynHtml'
                                                , ffor
                                                , text
                                                , textInput
                                                , textInputConfig_attributes
                                                , textInputConfig_initialValue
                                                , textInputConfig_inputType
                                                )
import           Reflex.Dom.Widget.Input        ( _textInput_value )
import           Servant.API                    ( type (:<|>)((:<|>)) )
import           Servant.Reflex                 ( BaseUrl(BasePath)
                                                , QParam(QParamSome)
                                                , ReqResult
                                                , client
                                                , reqSuccess
                                                , reqFailure
                                                )
import           Test.QuickCheck                ( elements
                                                , generate
                                                , listOf
                                                , resize
                                                )

header :: (MonadWidget t m) => m ()
header =
    elAttr "link"
           (Map.fromList [("rel", "stylesheet"), ("href", bootstrapCSSCDN)])
        $ return ()
  where
    bootstrapCSSCDN
        = "https://stackpath.bootstrapcdn.com/bootstrap/4.1.2/css/bootstrap.min.css"

diceButton :: (MonadWidget t m) => m (Event t ())
diceButton = do
    (e, _) <- elAttr' "div" ("class" =: "btn btn-primary mx-1") $ text "⚃"
    return $ () <$ domEvent Click e

expInput
    :: (MonadWidget t m)
    => Dynamic t Bool
    -> T.Text
    -> T.Text
    -> m (Dynamic t String)
expInput isValid ident start = do
    let errorState =
            Map.fromList [("class", "form-control is-invalid"), ("id", ident)]
        validState =
            Map.fromList [("class", "form-control is-valid"), ("id", ident)]
    rec n <-
            textInput
            $  def
            &  textInputConfig_inputType
            .~ "text"
            &  textInputConfig_initialValue
            .~ start
            &  textInputConfig_attributes
            .~ attrs

        let result = T.unpack <$> _textInput_value n
            attrs  = (\b -> if b then validState else errorState) <$> isValid
    return result

lecteurExp
    :: (MonadWidget t m)
    => Dynamic t Bool
    -> (Event t () -> m (Event t (ReqResult () String)))
    -> m (Dynamic t String)
lecteurExp isValid getAleaExp =
    el "form" $ elAttr "div" ("class" =: "form-group") $ do
        let eDef = "(a+b)*.a.(a+b)"
        elAttr "label" ("for" =: "inputExp") $ text "Expression"
        res <- elAttr "div" ("class" =: "input-group") $ do
            rec d_t <- holdDyn (T.pack eDef)
                    $ fmapMaybe (fmap T.pack . reqSuccess) evt2
                express <- dyn $ expInput isValid "inputExp" <$> d_t
                evt     <- diceButton
                evt2 :: Event t (ReqResult () String) <- getAleaExp evt
            join <$> holdDyn (constDyn eDef) express
        elAttr "small" ("class" =: "form-text text-muted")
            $ text
                  "Enter a regular expression, made of the symbols in {a,..., z, +, ., *, 0, 1}."
        return res

helpButton :: (MonadWidget t m) => T.Text -> T.Text -> m () -> m ()
helpButton id_ title content = do
    elAttr
            "button"
            (Map.fromList
                [ ("type"       , "button")
                , ("class", "btn btn-primary rounded-circle ml-3 mb-3")
                , ("data-toggle", "modal")
                , ("data-target", mappend "#" id_)
                ]
            )
        $ text "?"
    --
    elAttr
            "div"
            (Map.fromList
                [ ("class"      , "modal fade")
                , ("id"         , id_)
                , ("data-toggle", "modal")
                , ("data-target", mappend "#" id_)
                ]
            )
        $ elAttr "div" ("class" =: "modal-dialog modal-dialog-centered")
        $ elAttr "div" ("class" =: "modal-content")
        $ do
              _ <- elAttr "div" ("class" =: "modal-header") $ do
                  elAttr "h5" ("class" =: "modal-title") $ text title
                  elAttr
                          "button"
                          (Map.fromList
                              [ ("type"        , "button")
                              , ("class"       , "close")
                              , ("data-dismiss", "modal")
                              , ("data-target" , mappend "#" id_)
                              ]
                          )
                      $ el "span"
                      $ return "&times"
              elAttr "div" ("class" =: "modal-body") content
              elAttr "div" ("class" =: "modal-footer")
                  $ elAttr
                        "button"
                        (Map.fromList
                            [ ("type"        , "button")
                            , ("class"       , "btn btn-secondary")
                            , ("data-dismiss", "modal")
                            ]
                        )
                  $ text "Close"

filterMaybe :: (a -> Bool) -> a -> Maybe a
filterMaybe f a | f a = Just a
filterMaybe _ _       = Nothing

wordInput
    :: (MonadWidget t m)
    => Dynamic t Bool
    -> T.Text
    -> T.Text
    -> m (Dynamic t String)
wordInput isValid ident start = do
    let errorState =
            Map.fromList [("class", "form-control is-invalid"), ("id", ident)]
        validState =
            Map.fromList [("class", "form-control is-valid"), ("id", ident)]
    rec n <-
            textInput
            $  def
            &  textInputConfig_inputType
            .~ "text"
            &  textInputConfig_initialValue
            .~ start
            &  textInputConfig_attributes
            .~ attrs

        let result = T.unpack <$> _textInput_value n
            attrs  = (\b -> if b then validState else errorState) <$> isValid
    return result

lecteurWord :: (MonadWidget t m) => Dynamic t Bool -> m (Dynamic t String)
lecteurWord isValid = el "form" $ elAttr "div" ("class" =: "form-group") $ do
    elAttr "label" ("for" =: "inputWord") $ text "Word"
    res <- elAttr "div" ("class" =: "input-group") $ do
        let eDef = "aabaa"
        rec
            d_t  <- holdDyn (T.pack eDef) evt2
            word <- dyn $ wordInput isValid "inputWord" <$> d_t
            evt  <- diceButton
            evt2 <-
                performEvent
                $   ffor evt
                $   const
                $   liftIO
                $   T.pack
                <$> (generate (resize 4 $ listOf $ elements ['a' .. 'z']) :: IO
                          String
                    )
        join <$> holdDyn (constDyn eDef) word
    elAttr "small" ("class" =: "form-text text-muted")
        $ text "Enter a word, made of the symbols in {a, b, c, d, e}."
    return res

expAndResWidgetLine
    :: (MonadWidget t m)
    => T.Text
    -> Dynamic t String
    -> Dynamic t (String, String, String)
    -> m ()
expAndResWidgetLine title w dyn_triple = do
    let dynInvalid = fmap ((\s -> if s == "[Invalid Input]" then "style" =: "color : red" else mempty) . \(x, _, _) -> x) dyn_triple
    el "tr" $ do
        elAttr
                "th"
                (  "rowspan"
                =: "3"
                <> "style"
                =: "vertical-align : middle; text-align : center; width : 33%"
                )
            $ elDynAttr "span" dynInvalid $ text title
        elAttr "td" ("style" =: "text-align : right; padding-right : 0")
            $  elDynAttr "span" dynInvalid $ text "E="
        elAttr "td" ("style" =: "text-align : left; padding-left : 0")
            $ elDynAttr "span" dynInvalid $ dynText ((\(x, _, _) -> T.pack x) <$> dyn_triple)
    el "tr" $ do
        elAttr "td" ("style" =: "text-align : right; padding-right : 0") $ elDynAttr "span" dynInvalid $ do
            text "d"
            el "sub" $ dynText $ T.pack <$> w
            text "(E)="
        elAttr "td" ("style" =: "text-align : left; padding-left : 0")
            $   elDynAttr "span" dynInvalid $ elDynHtml' "span" -- dynText
            $   (\(_, x, _) -> T.pack x)
            <$> dyn_triple
    el "tr" $ do
        elAttr "td" ("style" =: "text-align : right; padding-right : 0") $ elDynAttr "span" dynInvalid $ do
            text "weight"
            el "sub" $ dynText $ T.pack <$> w
            text "(E)="
        elAttr "td" ("style" =: "text-align : left; padding-left : 0") $ elDynAttr "span" dynInvalid
            $   dynText
            $   (\(_, _, x) -> T.pack x)
            <$> dyn_triple

body :: forall t m . (MonadWidget t m) => m ()
body = do

    let (getRes :<|> getAlea) = client
            (Proxy :: Proxy DerCompAPI)
            (Proxy :: Proxy m)
            (Proxy :: Proxy ())
            -- (constDyn (BasePath "https://mon-test-stack.herokuapp.com/")) -- heroku
                        (constDyn (BasePath "http://localhost:8081")) -- local

    _ <- elAttr "div" ("class" =: "container") $ do
        rec
            elAttr "div" ("style" =: "text-align : center") $ do
                elAttr
                        "h1"
                        (  "class"
                        =: "text-center"
                        <> "style"
                        =: "display : inline-block"
                        )
                    $ text "Monadic derivatives"
                helpButton "modal1" "How To"
                    $ elAttr "ul" ("style" =: "text-align : left")
                    $ do
                          el "li" $ do
                              el "h5" $ text "Expression:"
                              elAttr "ul" ("style" =: "padding-left : 1em") $ do
                                  el "li" $ text "Empty word: 1"
                                  el "li" $ text "Empty expression: 0"
                                  el "li" $ text "Symbols: in ['a' .. 'z']"
                                  el "li" $ do
                                      el "h6" $ text "Operators"
                                      elAttr
                                              "ul"
                                              ("style" =: "padding-left : 1em")
                                          $ do
                                                el "li"
                                                    $ text
                                                          "Scalar multiplication: [value] *> Exp, Exp <* [value]"
                                                el "li" $ text
                                                    "Regular: +, ., *"
                                                el "li"
                                                    $ text
                                                          "Boolean: ¬, Not, &, And, ->"
                                                el "li" $ do
                                                    text "Numeric:"
                                                    elAttr
                                                            "ul"
                                                            ("style"
                                                            =: "padding-left : 1em"
                                                            )
                                                        $ do
                                                              el "li"
                                                                  $ text
                                                                        "ExtMult: multiary extrema multiplication (max * min)"
                                                              el "li"
                                                                  $ text
                                                                        "ExtDist: multiary extrema distance (max - min)"
                                                              el "li"
                                                                  $ text
                                                                        "/*/: multiary algebraic mean"
                                                              el "li"
                                                                  $ text
                                                                        "/**/: multiary geometric mean"


                          el "li" $ text
                              "Word: A sequence of symbols in ['a' .. 'z']"
            el "hr" $ return ()
            dynExpString <- lecteurExp (valid_expr <$> derCompsDyn) getAlea
            dynWord <- lecteurWord (valid_word <$> derCompsDyn)

            res :: Event t (ReqResult () DerComp) <-
                getRes (QParamSome <$> dynExpString) (QParamSome <$> dynWord)
                    $ leftmost
                          [void (updated dynExpString), void (updated dynWord)]

            derCompsDyn <- holdDyn invalidRep $ fmapMaybe reqSuccess res
            let errs = fmapMaybe reqFailure res

        el "hr" $ return ()
        el "h2"
            $  dynText
            $  return "Derivatives with respect to the word "
            <> fmap T.pack dynWord
        elAttr
                "table"
                ("style" =: "margin : auto" <> "class" =: "table table-striped")
            $ el "tbody"
            $ do
                  expAndResWidgetLine "Maybe"
                                      dynWord
                                      (res_maybe <$> derCompsDyn)
                  expAndResWidgetLine "Set" dynWord (res_set <$> derCompsDyn)
                  expAndResWidgetLine "LinComb (SR Bool)"
                                      dynWord
                                      (res_lincomb_bool <$> derCompsDyn)
                  expAndResWidgetLine "LinComb (SR Int)"
                                      dynWord
                                      (res_lincomb_int <$> derCompsDyn)
                  expAndResWidgetLine "LinComb (SR Double)"
                                      dynWord
                                      (res_lincomb_double <$> derCompsDyn)
                  expAndResWidgetLine
                      "GradedModuleOfLinComb (SR Bool)"
                      dynWord
                      (res_gradmodoflincomb_bool <$> derCompsDyn)
                  expAndResWidgetLine
                      "GradedModuleOfLinComb (SR Int)"
                      dynWord
                      (res_gradmodoflincomb_int <$> derCompsDyn)
                  expAndResWidgetLine
                      "GradedModuleOfLinComb (SR Double)"
                      dynWord
                      (res_gradmodoflincomb_double <$> derCompsDyn)
    footer


footer :: (MonadWidget t m) => m ()
footer = do
    elAttr "script" (Map.fromList [("defer", "defer"), ("src", jqueryCDN)])
        $ return ()
    elAttr "script" (Map.fromList [("defer", "defer"), ("src", popperCDN)])
        $ return ()
    elAttr "script" (Map.fromList [("defer", "defer"), ("src", bootstrapJsCDN)])
        $ return ()
  where
    jqueryCDN = "https://code.jquery.com/jquery-3.3.1.min.js"
    popperCDN
        = "https://cdnjs.cloudflare.com/ajax/libs/popper.js/1.14.3/umd/popper.min.js"
    bootstrapJsCDN
        = "https://stackpath.bootstrapcdn.com/bootstrap/4.1.2/js/bootstrap.bundle.js"
