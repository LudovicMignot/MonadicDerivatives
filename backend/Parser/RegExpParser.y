{

{-# LANGUAGE RankNTypes      #-}

module Parser.RegExpParser where

import Control.Applicative (liftA2)
import RegExp.OpDefTyped 
import Parser.RegExpTok as A

import RegExp.MonadicRegExpWithFun as E

import Data.Maybe (listToMaybe)
import Text.Read(readMaybe)
import Common(ReadVia, readMaybeVia)

import LinComb.LinComb4
import  Singletons.Singletons
import Control.Monad(join)

import Type.UnknownSizedVect as TU

import           Data.Singletons                ( SingI )

}

%name expfromString Exp

%tokentype { Token }
%error { parseError }
%right impl
%left somme
%left inter
%left conc
%left righta
%right lefta
%left star
%left maxmindist
%left maxminmult
%left arithmean
%left geommean
%left non

%monad {Maybe}

%token
  virg {A.Virg}
  maxminmult {A.MaxMinMult}
  maxmindist {A.MaxMinDist}
  arithmean {A.ArithMean}
  geommean {A.GeomMean}
  inter {A.And}
  non {A.Non}
  impl {A.Impl}
  somme {A.Somme}
  conc {A.Conc}
  star {A.Star}
  symb {A.Symb $$}
  coef {A.Coef $$}
  vide {A.Vide}
  eps {A.Epsilon}
  po {A.ParO}
  pf {A.ParF}
  lefta {A.LeftA}
  righta {A.RightA}

%%
Exp :: {(forall m. (ReadVia (m ()), SingI (m ()))  => Maybe (MonadicRegExp m Char))}
  : Exp somme Exp {
    liftA2 Sum $1 $3
  }
  | Exp conc Exp {
    liftA2 E.Conc $1 $3
  }
  | Exp star { fmap E.Star $1}
  | po Exp pf {$2}
  | coef lefta Exp  {
    liftA2 LeftAction (readMaybeVia $1) $3
  }
  | Exp righta coef {
    liftA2 RightAction $1 (readMaybeVia $3)
  }
  | non Exp {
    $2 >>= notExpIfBool
  }
  | Exp impl Exp {
    join (liftA2 implExpIfBool $1 $3)
  }
  | Exp inter Exp {
    join (liftA2 andExpIfBool $1 $3)
  }
  | Atom {$1}
  | maxmindist po NonEmptyList pf {
    sequence $3 >>= gradExtDistIfWellTyped . TU.fromList
  }
  | maxminmult po NonEmptyList pf {
    sequence $3 >>= gradExtMultIfWellTyped . TU.fromList
  }
  | arithmean ExpList {
    sequence $2 >>= arithMeanIfWellTyped . TU.fromList
  }
  | geommean ExpList {
    sequence $2 >>= geomMeanIfWellTyped . TU.fromList
  }

Atom :: {(forall t m. (ReadVia (m ()), SingI (m ()))  => Maybe (MonadicRegExp m Char))}
  : vide {Just E.Empty}
  | eps {Just E.Epsilon}
  | symb { fmap E.Atom (listToMaybe $1)}

ExpList :: {forall m. (ReadVia (m ()), SingI (m ()))  => [Maybe (MonadicRegExp m Char)]}
  : po pf {[]}
  | po NonEmptyList pf {
    $2
  }

NonEmptyList :: {forall m. (ReadVia (m ()), SingI (m ()))  => [Maybe (MonadicRegExp m Char)]}
  : Exp virg NonEmptyList {$1 : $3}
  | Exp {[$1]}


{
parseError _ = Nothing
}
