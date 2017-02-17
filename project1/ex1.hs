{-|



   Author: Justin Lee
   KUID: 2393250
   Date: Thu Feb 9 2017

    Project 1: Exercise 2: a parser and interpreter for ABE supporting plus, 
    minus, division, multiplication, if, isZero, Leq

    1.Define a type for representing the abstract syntax of the extended ABE 
      language using data.
    2.Using Parsec, write a function parseABE :: String -> ABE that accepts the 
      concrete syntax of ABE and generates an ABE data structure representing it
    3.Write a function, eval :: ABE -> (Either String ABE), that takes a 
      ABE data structure and interprets it and returns an ABE value or an 
      error message. Your eval function should check for divide-by-zero errors 
      at runtime.
    4.Write a function, typeof :: ABE -> (Either String ABE), that returns 
      either a String representing an error message or an ABE structure. 
      Your typeof function should return an error message if it encounters a 
      constant 0 in the denominator of a division operator.
    5.Write a function, interp that combines your parser, type checker and 
      evaluator into a single operation that parses, type checks, and 
      evaluates an ABE expression. Take advantage of the Either type to 
      ensure eval is not called when typeof fails.

ABE ::= number | boolean
        ABE + ABE |
        ABE - ABE |
        ABE * ABE |
        ABE / ABE |
        ABE && ABE |
        ABE <= ABE |
        isZero ABE |
        if ABE then ABE else ABE
-}

{-# LANGUAGE GADTs #-}

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token
import ParserUtils

-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

main = do
 --testParser 100
 --testEval' 100
 return(0)


data ABE where 
 Num :: Int -> ABE
 Boolean :: Bool -> ABE
 Plus :: ABE -> ABE -> ABE
 Minus :: ABE -> ABE -> ABE
 Mult :: ABE -> ABE -> ABE
 Div :: ABE -> ABE -> ABE
 If0 :: ABE -> ABE -> ABE -> ABE
 And :: ABE -> ABE -> ABE
 Leq :: ABE -> ABE -> ABE
 IsZero :: ABE -> ABE
 If :: ABE -> ABE -> ABE -> ABE
 deriving (Show, Eq)

--2. Parsec
expr :: Parser ABE
expr = buildExpressionParser operators term

--operators for order of presedence
operators  = [ [ inFix "*" Mult AssocLeft
               , inFix "/" Div AssocLeft], 

               [ inFix "+" Plus AssocLeft
               , inFix "-" Minus AssocLeft],

               [ inFix "<=" Leq AssocLeft
               , preFix "isZero" IsZero ],

               [ inFix "&&" And AssocLeft ]
             ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

if0Expr :: Parser ABE
if0Expr = do reserved lexer "if0"
             c <-expr
             reserved lexer "then"
             t <- expr
             reserved lexer "else"
             e <- expr
             return(If0 c t e)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <-expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return(If c t e)

term = parens lexer expr
       <|> numExpr
       <|> if0Expr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr

--parseABE :: ABE -> ABE			
parseABE = parseString expr

eval :: ABE -> ABE
eval (Num n) = (Num n)
eval (Boolean n) = (Boolean n)
eval (Plus t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1+v2))
eval (Minus t1 t2) = let (Num v1) = (eval t1)
                         (Num v2) = (eval t2)
                     in (Num (v1-v2))
eval (Mult t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1*v2))
eval (Div t1 t2) = let (Num v1) = (eval t1)
                       (Num v2) = (eval t2)
                   in if (v2 == 0) then (error "error div by 0")else (Num (div v1 v2))
eval (If0 t1 t2 t3) = let (Num v) = (eval t1)
                   in if (v == 0) then (eval t2) else (eval t3)
eval (If t1 t2 t3) = let (Boolean v) = (eval t1)
                   in if (v == True) then (eval t2) else (eval t3)
eval (And t1 t2) = let (Boolean v1) = (eval t1)
                       (Boolean v2) = (eval t2)
                   in (Boolean (v1 && v2))
eval (IsZero t) = let (Num v) = (eval t)
                  in (Boolean (v == 0))
eval (Leq t1 t2) = let (Num v1) = (eval t1)
                       (Num v2) = (eval t2)
                   in (Boolean (v1 <= v2))
                   

--interp :: String -> ABE
interp = eval . parseABE

--Testing portion below from Perry Alexander, where I added functionality 
--for multiplication, division, and if0

-- AST Pretty Printer
pprint :: ABE -> String
pprint (Num n) = show n
pprint (Plus n m) = "(" ++ pprint n ++ "+" ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ "-" ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ "*" ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ "/" ++ pprint m ++ ")"
pprint (If0 n m o) = "(" ++ "if0 " ++ pprint n ++ " then " ++ pprint m ++ " else " ++ pprint o ++ ")"

instance Arbitrary ABE where
  arbitrary =
    sized $ \n -> genABE ((rem n 10) + 10)

genNum =
  do t <- choose (0,100)
     return (Num t)

genPlus n =
  do s <- genABE n
     t <- genABE n
     return (Plus s t)

genMinus n =
  do s <- genABE n
     t <- genABE n
     return (Minus s t)

genMult n =
  do s <- genABE n
     t <- genABE n
     return (Mult s t)

genDiv n =
  do s <- genABE n
     t <- genABE n
     return (Div s t)
     --if (t == Num 0) then return(error "error div by 0 buster") 
     --else return(Div s t)

genIf0 n =
  do s <- genABE n
     t <- genABE n
     u <- genABE n
     return (If0 s t u)

genABE :: Int -> Gen ABE
genABE 0 =
  do term <- genNum
     return term
genABE n =
  do term <- oneof [genNum,(genPlus (n-1))
                   ,(genMinus (n-1))
                   ,(genMult (n-1))
                   ,(genDiv (n-1))
                   ,(genIf0 (n-1))]
     return term

-- QuickCheck 
testParser :: Int -> IO ()
testParser n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> parseABE (pprint t) == t)

testEval' :: Int -> IO ()
testEval' n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> (interp $ pprint t) == (eval t))

