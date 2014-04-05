{-
CS 386L Programming Assignment (HW 6)

yufeng@cs.utexas.edu

Implement type inference for a language with
     * variables, lambda functions, application
     * let binding
     * integers, boolean, binary integer & boolean operators
     * recursive values declaration
Implement Let polymorphism, using the algorithm defined on pages 333-334.
Implement a few basic operations on data types, including
  multiplication, addition, equality
Use the State monad to collect your constraints
Implement the unification algorithm 
Define Show instances for your data types to output the results using a pleasant notation

Use the following type definitions

type X = String

data Type = TInt | TBool | Fun Type Type | TVar X | TPoly [X] Type

data Term = Var X | Lam X Term | App Term Term | Let X Term Term 
        | Rec X Term
    | Num Int | Binary X Term Term -}

module HW6 where

import Prelude hiding (LT, GT, EQ, id)
import Data.Maybe
import Data.List


data BinaryOp = Add | Sub | Mul | Div | And | Or
              | GT | LT | LE | GE | EQ
  deriving (Eq, Show)

data UnaryOp = Neg | Not
  deriving (Eq, Show)

data Value = IntV  Int
           | BoolV Bool
           | ClosureV String Exp Env  -- new
  deriving (Eq, Show)

{-
instance Show Value where
    show (IntV n) = show n
    show (BoolV b) = show b
    show (ClosureV x b env) = "<Closure " ++ x ++ ">" -}

data Exp = Literal   Value
         | Unary     UnaryOp Exp
         | Binary    BinaryOp Exp Exp
         | If        Exp Exp Exp
         | Variable  String
         | Declare   String Exp Exp
         | Function  String Exp      -- new
         | Call      Exp Exp         -- changed
  deriving (Eq, Show)
  
type Env = [(String, Value)]


fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

thd3 :: (a, b, c) -> c
thd3 (_, _, x) = x

grep [] newType = TError
grep (x:xs) newType = if (fst x == newType) then 
                          snd x
                      else 
                          grep xs newType
                        
--Type inference
--infer :: Exp -> Type
infer e = let constr = (getConstraints e 1)
            in let newType = thd3 constr
                in grep (unification (fst3 constr)) newType

--extract constraints
--getConstraints :: Exp -> [(Type, Type)]
getConstraints (Literal (IntV x)) f = let new = TVar ("x"++ show f) 
                           in ([(new, TInt)], f, new)

getConstraints (Binary Add e1 e2) f = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)

getConstraints (Binary EQ e1 e2) f = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

substinty tyX tyT tyS = f tyS
    where
            f (TFun tyS1 tyS2) = (TFun (f tyS1) (f tyS2))
            f TInt = TInt
            f TBool = TBool
            f (TVar xx) = if xx==tyX then tyT else (TVar xx)

occur tyX tyT = occr tyT 
                where   occr (TFun tyT1 tyT2) = (occr tyT1) || (occr tyT2)
                        occr TInt = False
                        occr TBool = False
                        occr (TVar xx) = (xx == tyX)

substinconstr tyX tyT constr = 
    map (\(tyS1,tyS2) -> (substinty tyX tyT tyS1, substinty tyX tyT tyS2)) constr

unification ll = unify ll
    where 
        unify [] = []
        unify ((tyS,(TVar tyX)):rest) =
            if tyS == (TVar tyX) then 
                unify rest 
            else if (occur tyX tyS) then
                --error fi (msg ^ ": circular constraints")
                [(tyS,TError)]
            else
                (unify (substinconstr tyX tyS rest)) ++ [((TVar tyX),tyS)]
        unify (((TVar tyX),tyT):rest) =
            if tyT == (TVar tyX) then 
                unify rest 
            else if (occur tyX tyT) then
                --error fi (msg ^ ": circular constraints")
                [(tyT,TError)]
            else
                --(unify (substinconstr tyX tyT rest)) ++ [((TVar tyX),tyT)]
                (unify (substinconstr tyX tyT rest)) ++ [((TVar tyX),tyT)]
        unify ((TInt,TInt):xs) = unify xs
        unify ((TBool,TBool):xs) = unify xs
        unify (((TFun s1 t1),(TFun s2 t2)):xs) = unify ((s1,s2):(t1,t2):xs)

{-
let applysubst constr tyT =
    List.fold_left
    (fun tyS (TyId(tyX),tyC2) → substinty tyX tyC2 tyS) tyT (List.rev constr)

let substinconstr tyX tyT constr = 
    map (\tyS1 -> \tyS2 -> (substinty tyX tyT tyS1, substinty tyX tyT tyS2)) constr-}

data Type = TInt
          | TBool
          | TVar String
          | TFun Type Type
          | TPoly [String] Type
          | TError
  deriving Eq

instance Show Type where
  show TInt = "Int"
  show TBool = "Bool"
  show (TVar s) = s
  show (TFun t1 t2) = "("++show t1++" -> "++show t2++")"
  show (TPoly fv typ) = "forall"++show fv++".("++show typ++")"
  show TError = "Type error!"
