{ module Parser.RegExpTok where}

%wrapper "basic"

$symb = [a-z]

tokens :-
  $white+ ;
  "ExtMult" {\_ -> MaxMinMult}
  "ExtDist" {\_ -> MaxMinDist}
  "/*/" {\_ -> ArithMean}
  "/**/" {\_ -> GeomMean}
  "&" | "And" {\_ -> And}
  "¬" | "Not" {\_ -> Non}
  "->" {\_ -> Impl}
  "["[^\]]*"]" {\s -> Coef $ tail $ init s}
  "*" {\_ -> Star}
  "+" {\_ -> Somme}
  "."|"·" {\_ -> Conc}
  $symb {\s -> Symb s}
  "0" {\_ -> Vide}
  "1" {\_ -> Epsilon}
  "(" {\_ -> ParO}
  ")" {\_ -> ParF}
  "*>" {\_ -> LeftA}
  "<*" {\_ -> RightA}
  "," {\_ -> Virg}
  . {\_ ->  Autre}

{data Token
  =	Star
  | MaxMinMult
  | ArithMean
  | GeomMean
  | Somme
  | Virg
  | MaxMinDist
  | And
  | Non
  | Impl
  | Conc
  | Symb String
  | Coef String
  | Vide
  | Epsilon
  | ParO
  | ParF
  | LeftA
  | RightA
  | Autre
	deriving (Eq, Show)
}
