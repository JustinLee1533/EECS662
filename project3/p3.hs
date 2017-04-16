{-|
  Author: Justin Lee
  KUID: 2393250
  Date: 4-20-2017

  Project 3 – Static Scoping and Elaboration The objective of this project is
  to add dynamically scoped and   statically scoped strict functions to BAE and
  introduce elaboration to the interpretation process.

  Exercise 1:

    1. Write a function, evalDynCFAE :: Env -> CFAE -> CFAE that evaluates its
    second argument using the environment provided in its first and returns a
    CFAE AST structure.

    2.Write a function, interpDynCFAE :: String -> CFAE that combines a parser
    that will be provided and interpreter for CFAE into a single interpretation
    function. This function should call evalDynCFAE using an empty environment.

  Exercise 2:

    1. Define a datatype called CFAEValue to represent values returned by
    interpreting CFAE expressions. This datatype should minimally include
    closures and numeric values.

    2. Write a function, evalStatCFAE :: Env -> CFAE -> CFAEValue that
    interprets its second value using the environment provided in its first.
    This evaluator needs to return a value rather than a CFAE expression to \
    implement static scoping using closures.

    3. Write a function, interpStatCFAE that combines a parser that will be
    provided and interpreter for CFAE into a single evaluation function. This
    function should call evalStatCFAE using an empty interpreter.

  Exercise 3:

    1. Define a type for representing the abstract syntax for CFBAE. You will
    need to add a bind expression to the abstract syntax for the CFAE syntax
    from the previous problem.

    2. Write a function, elabCFBAE :: CFBAE -> CFAE, that takes a CFBAE data
    structure and returns a semantically equivalent CFAE structure.
    Specifically, you must translate the bind construct from CFBAE into
    constructs from CFAE.

    3. Write a function, evalCFBAE :: Env -> CFBAE -> CFAEValue, that combines
    your elaborator and statically scoped CFAE interpreter into a single
    operation that elaborates and interprets a CFBAE expression.

    4. Write a function, interpCFBAE :: String -> CFAEValue, that combines your
    evaluator and a parser that will be provide into a single interpreter
    function. Your new interpreter should have access to a collection of
    pre-defined symbols - functions and numbers - that will be available to all
    programs. This collection of pre-defined items is typically called a
    prelude. Your prelude should minimally define inc and dec, that increment
    and decrement their arguments, respectively.
-}

{-# LANGUAGE GADTs #-}

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token
import Proj3Utils

-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

--Imports for UnsafeIO, Don't tell professor Gill
import System.IO.Unsafe(unsafePerformIO)

main = do
 return(0)

type Env = [(String, CFAE)]

--Dynamically scoped, strict evaluation; Your interpreter will use deferred
--substitution for efficiency and closures to represent function values:

--Strict Evaluation: all parameters to a function are evaluated before the function is called, call-by-value
--dynamic scoping: the environment used when evaluating a function is the environment where the function is evaluated.
evalDynCFAE :: Env -> CFAE -> Maybe CFAE

evalDynCFAE env (Num n) = (Just (Num n))

evalDynCFAE env (Plus t1 t2) = do
  t1' <- (evalDynCFAE env t1)
  t2' <- (evalDynCFAE env t2)
  case t1' of
    (Num v1) -> case t2' of
                  (Num v2) -> (Just (Num (v1+v2)))
                  _ -> (Nothing)
    _ -> (Nothing)

evalDynCFAE env (Minus t1 t2) = do
  t1' <- (evalDynCFAE env t1)
  t2' <- (evalDynCFAE env t2)
  case t1' of
    (Num v1) -> case t2' of
                  (Num v2) -> (Just (Num (v1-v2)))
                  _ -> (Nothing)
    _ -> (Nothing)

evalDynCFAE env (Mult t1 t2) =  do
  t1' <- (evalDynCFAE env t1)
  t2' <- (evalDynCFAE env t2)
  case t1' of
    (Num v1) -> case t2' of
                  (Num v2) -> (Just (Num (v1*v2)))
                  _ -> (Nothing)
    _ -> (Nothing)

evalDynCFAE env (Div t1 t2) =  do
  t1' <- (evalDynCFAE env t1)
  t2' <- (evalDynCFAE env t2)
  case t1' of
    (Num v1) -> case t2' of
                  (Num v2) -> (Just (Num (div v1 v2)))
                  _ -> (Nothing)
    _ -> (Nothing)

evalDynCFAE env (Lambda i b) = (Just (Lambda i b))

evalDynCFAE env (App f a) = do
  (Lambda i b) <- evalDynCFAE env f
  a' <- evalDynCFAE env a
  evalDynCFAE ((i, a'):env) b

evalDynCFAE env (Id id) = case
  (lookup id env) of
    Just x -> (Just x)
    Nothing -> (Nothing)

evalDynCFAE env (If c t e) =  do
  c' <- evalDynCFAE env c
  case c' of
    (Num v1) -> if v1 == 0 then (evalDynCFAE env t) else (evalDynCFAE env e)
    _ -> (Nothing)

interpDynCFAE :: String -> Maybe CFAE
interpDynCFAE t = let r = parseCFAE t in (evalDynCFAE [] r)

--exercise 2

evalStatCFAE :: EnvV -> CFAE -> Maybe CFAEValue

evalStatCFAE envV (Num n) = (Just (NumV n))

evalStatCFAE envV (Plus t1 t2) = do
   t1' <- (evalStatCFAE envV t1)
   t2' <- (evalStatCFAE envV t2)
   case t1' of
     (NumV v1) -> case t2' of
                   (NumV v2) -> (Just (NumV (v1+v2)))
                   _ -> (Nothing)
     _ -> (Nothing)

evalStatCFAE envV (Minus t1 t2) = do
    t1' <- (evalStatCFAE envV t1)
    t2' <- (evalStatCFAE envV t2)
    case t1' of
      (NumV v1) -> case t2' of
                    (NumV v2) -> (Just (NumV (v1-v2)))
                    _ -> (Nothing)
      _ -> (Nothing)

evalStatCFAE envV (Mult t1 t2) =  do
   t1' <- (evalStatCFAE envV t1)
   t2' <- (evalStatCFAE envV t2)
   case t1' of
     (NumV v1) -> case t2' of
                   (NumV v2) -> (Just (NumV (v1*v2)))
                   _ -> (Nothing)
     _ -> (Nothing)

evalStatCFAE envV (Div t1 t2) =  do
   t1' <- (evalStatCFAE envV t1)
   t2' <- (evalStatCFAE envV t2)
   case t1' of
     (NumV v1) -> case t2' of
                   (NumV v2) -> (Just (NumV (div v1 v2)))
                   _ -> (Nothing)
     _ -> (Nothing)

evalStatCFAE envV (Lambda i b) = Just (ClosureV i b envV)

evalStatCFAE envV (App f a) = do
   (ClosureV i b e) <- evalStatCFAE envV f
   a' <- evalStatCFAE envV a
   evalStatCFAE ((i, a'):e) b

evalStatCFAE envV (Id id) = case
   (lookup id envV) of
     Just x -> (Just x)
     Nothing -> (Nothing)

evalStatCFAE envV (If c t e) =  do
   c' <- evalStatCFAE envV c
   case c' of
     (NumV v1) -> if v1 == 0 then (evalStatCFAE envV t) else (evalStatCFAE envV e)
     _ -> (Nothing)
