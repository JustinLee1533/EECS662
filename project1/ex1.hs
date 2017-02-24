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

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

--Parsec
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

parseABE :: String -> ABE			
parseABE = parseString expr

eval :: ABE -> (Either String ABE)
eval (Num n) = (Right (Num n))
eval (Boolean n) = (Right (Boolean n))

eval (Plus t1 t2) = 
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Num v1)) -> case r2 of
                         (Left m) -> r2
                         (Right (Num v2)) -> (Right(Num (v1+v2)))
                         (Right _) -> (Left "Type error in +")
    (Right _) -> (Left "Type error in +")

eval (Minus t1 t2) = 
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Num v1)) -> case r2 of
                        (Left m) -> r2
                        (Right (Num v2)) -> (Right(Num (v1-v2)))
                        (Right _) -> (Left "Type error in -")
    (Right _) -> (Left "Type error in -")

eval (Mult t1 t2) = 
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Num v1)) -> case r2 of
                        (Left m) -> r2
                        (Right (Num v2)) -> if (v2 == 0) then 
                         (Left "divide by 0 error") else (Right(Num (v1*v2)))
                        (Right _) -> (Left "Type error in *")
    (Right _) -> (Left "Type error in *")

eval (Div t1 t2) =  
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Num v1)) -> case r2 of
                        (Left m) -> r2
                        (Right (Num 0)) -> (Left "Eval error: divide by 0")
                        (Right (Num v2)) -> (Right(Num (div v1 v2)))
                        (Right _) -> (Left "Type error in div")
    (Right _) -> (Left "Type error in div")

eval (If0 t1 t2 t3) = 
 let r = (eval t1)
 in case r of
    (Left m) -> r
    (Right (Num v)) -> (if (v == 0) then (eval t2) else (eval t3))
    (Right _) -> (Left "Type error in If0")

eval (If t1 t2 t3) = 
 let r = (eval t1)
 in case r of 
    (Left m) -> r
    (Right (Boolean v)) -> if (v) then (eval t2) else (eval t3)
    (Right _) -> (Left "Type error in If")

eval (And t1 t2) = 
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Boolean v1)) -> case r2 of
                            (Left m) -> r2
                            (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                            (Right _) -> (Left "Type error in And")
    (Right _) -> (Left "Type error in And")
                   
eval (IsZero t) = 
 let v = (eval t)
 in case v of
    (Left m) -> v
    (Right (Num v)) -> (Right (Boolean (v == 0)))
    (Right _) -> (Left "Type error in isZero")

eval (Leq t1 t2) = 
 let r1 = (eval t1)
     r2 = (eval t2)
 in case r1 of
    (Left m) -> r1
    (Right (Num v1)) -> case r2 of
                        (Left m) -> r2
                        (Right (Num v2)) -> (Right(Boolean (v1 <= v2)))
                        (Right _) -> (Left "Type error in Leq")
    (Right _) -> (Left "Type error in Leq")
 
--typeof, for static type checking                  
typeof :: ABE -> (Either String TABE)
typeof (Num x) = (Right TNum)
typeof (Boolean b) = (Right TBool)
typeof (Plus l r) = let l' = (typeof l)
                        r' = (typeof r)
                     in if (l'==(Right TNum) && r'==(Right TNum))
                        then (Right TNum)
                        else Left "Type Mismatch in +"
typeof (Minus l r) = let l' = (typeof l)
                         r' = (typeof r)
                     in if (l'==(Right TNum) && r'==(Right TNum))
                        then (Right TNum)
                        else Left "Type Mismatch in -"
typeof (Mult l r) = let l' = (typeof l)
                        r' = (typeof r)
                     in if (l'==(Right TNum) && r'==(Right TNum))
                        then (Right TNum)
                        else Left "Type Mismatch in *"
typeof (Div l r) = let l' = (typeof l)
                       r' = (typeof r)
                     in if (l'==(Right TNum) && r'==(Right TNum))
                        then if (r ==  Num 0) 
                             then (Left "divide by 0 error")
                             else (Right TNum)
                        else Left "Type Mismatch in Div"
typeof (And l r) = if ((typeof l) == (Right TBool)
                      && (typeof r) == (Right TBool))
                   then (Right TBool)
                   else Left "Type mismatch in &&"
typeof (Leq l r) = if (typeof l) == (Right TNum) && (typeof r) == (Right TNum)
                   then (Right TBool)
                   else Left "Type mismatch in <="
typeof (IsZero v) = if (typeof v) == (Right TNum)
                    then (Right TBool)
                    else Left "Type mismatch in IsZero"
typeof (If c t e) = if (typeof c) == Right TBool
                       && (typeof t)==(typeof e)
                    then (typeof t)
                    else Left "Type mismatch in if"
typeof (If0 c t e) = if (typeof c) == Right TNum
                       && (typeof t)==(typeof e)
                    then (typeof t)
                    else Left "Type mismatch in if"

--optimize
optimize :: ABE -> ABE
optimize (Boolean b) = (Boolean b)
optimize (Num x) = (Num x)
optimize (Plus l (Num 0)) = optimize l
optimize (Plus l r) = let l' = (optimize l)
                          r' = (optimize r)
                      in (Plus l' r')
optimize (If (Boolean True) t e) = (optimize t)
optimize (If c t e) = (If (optimize c) (optimize t) (optimize e))
--TODO:optimize these
optimize (Minus l r) = let l' = (optimize l)
                           r' = (optimize r)
                       in (Minus l' r')
optimize (Mult l r) = let l' = (optimize l)
                          r' = (optimize r)
                      in (Mult l' r')
optimize (Div l r) = let l' = (optimize l)
                         r' = (optimize r)
                     in (Div l' r')
optimize (And l r) = let l' = (optimize l)
                         r' = (optimize r)
                     in (And l' r')
optimize (Leq l r) = let l' = (optimize l)
                         r' = (optimize r)
                     in (Leq l' r')
optimize (IsZero l) = let l' = (optimize l)
                      in (IsZero l')
optimize (If0 c t e) = (If0 (optimize c) (optimize t) (optimize e))



--Interp TODO: took out Right from eval p
interp :: String -> Either String ABE
interp e = let p=(parseABE e) in
                  case (typeof p) of
                    (Right _) -> (eval p)
                    (Left m) -> (Left m)

interpErr = eval . parseABE

--Testing portion below from Perry Alexander, where I added functionality 
--for multiplication, division, and if0

-- AST Pretty Printer
pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean n) = show n
pprint (Plus n m) = "(" ++ pprint n ++ "+" ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ "-" ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ "*" ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ "/" ++ pprint m ++ ")"
pprint (If0 n m o) = "(" ++ "if0 " ++ pprint n ++ " then " ++ pprint m
                     ++ " else " ++ pprint o ++ ")"
pprint (If n m o) = "(" ++ "if " ++ pprint n ++ " then " ++ pprint m
                     ++ " else " ++ pprint o ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ "<=" ++ pprint m ++ ")"
pprint (IsZero n) = "(" ++"isZero " ++ pprint n ++ ")"


instance Arbitrary ABE where
  arbitrary =
    sized $ \n -> genABE ((rem n 10) + 10)

genNum =
  do t <- choose (0,100)
     return (Num t)

genBool =
  do t <- choose (True,False)
     return (Boolean t)

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

genAnd n =
  do s <- genABE n
     t <- genABE n
     return (And s t)

genLeq n =
  do s <- genABE n
     t <- genABE n
     return (Leq s t)

genIsZero n =
  do s <- genABE n
     return (IsZero s)

genIf n =
  do s <- genABE n
     t <- genABE n
     u <- genABE n
     return (If s t u)


genABE :: Int -> Gen ABE
genABE 0 =
  do term <- genNum
     return term
genABE n =
  do term <- oneof [genNum,genBool,(genPlus (n-1))
                   ,(genMinus (n-1))
                   ,(genMult (n-1))
                   ,(genDiv (n-1))
                   ,(genIf0 (n-1))
                   ,(genAnd (n-1))
                   ,(genLeq (n-1))
                   ,(genIsZero (n-1))
                   ,(genIf (n-1))]
     return term

-- QuickCheck 
testParser :: Int -> IO ()
testParser n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> parseABE (pprint t) == t)

testEval' :: Int -> IO ()
testEval' n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> (interp $ pprint t) == (eval t))

testTypedEval :: Int -> IO ()
testTypedEval n = quickCheckWith stdArgs {maxSuccess=n}
                  (\t -> case typeof t of
                           (Right _) -> eval (parseABE (pprint t)) == (eval t)
                           (Left _) -> True)

testErrThenTyped :: Int -> IO ()
testErrThenTyped n =
  quickCheckWith stdArgs {maxSuccess=n}
  (\t -> let t' = pprint t in
           case (interpErr t') of
             (Right v) -> (Right v) == interp t'
             (Left _) -> True)
               
testTypedThenErr :: Int -> IO ()
testTypedThenErr n =
  quickCheckWith stdArgs {maxSuccess=n}
  (\t -> let t' = pprint t in
           case (interp t') of
             (Right v) -> (Right v) == interpErr t'
             (Left _) -> True)
{-
testOptimizedEval :: Int -> IO ()
testOptimizedEval n =
  quickCheckWith stdArgs {maxSuccess=n}
  (\t -> case typeof [] t of
           (Right _) -> ((eval []) . optimize) t == (eval [] t)
           (Left _) -> True)
-}
