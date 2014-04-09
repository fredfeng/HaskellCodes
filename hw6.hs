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
import qualified Data.Map as Map  


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
grep (x:xs) newType = if checkError (x:xs) then
                          TError
                      else 
                          if (fst x == newType) then 
                              snd x
                          else 
                              grep xs newType
                        
checkError [] = False
checkError (x:xs) = if (fst x == TError) then
                        True
                    else
                        checkError xs
--Type inference
infer :: Exp -> Type
infer e = let env = Map.empty
            in let constr = (getConstraints e 1 env)
                in let newType = thd3 constr
                    in grep (unification (fst3 constr)) newType
                    --in unification (fst3 constr) 

eliminate :: Maybe Type -> Type 
eliminate (Just a) = a

--extract constraints
--getConstraints :: Exp -> [(Type, Type)]
getConstraints (Literal (IntV x)) f env = let new = TVar ("x"++ show f) 
                           in ([(new, TInt)], f, new)

getConstraints (Literal (BoolV x)) f env = let new = TVar ("x"++ show f) 
                           in ([(new, TBool)], f, new)

--no constraints for Variable x
getConstraints (Variable  x) f env = 
            if Map.member x $ env then
            --get the value from env.
                let tx = eliminate (Map.lookup x $ env)
                in  ([], f, tx)
            else
            --create a new one.
                ([], f, (TVar("x"++ show f)))
            --polymorphism....

getConstraints (Binary Add e1 e2) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) env in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)

getConstraints (Binary Mul e1 e2) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) env in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)

getConstraints (Binary EQ e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)


getConstraints (Function x body) f env = let tme = TVar ("x"++ show f) in
                            let tx = TVar ("x"++ show (f+1)) in
                            let newenv =  Map.insert ("x"++ show(f+1)) tx env in
                            let (c1, f1, tbody) = getConstraints body (f+1) newenv in
                            ([(tme, (TFun tx tbody))] ++ c1, f, tme)

--getConstraints (Call e1 e2) f = let new = TVar ("x"++ show f) in
--                            let (c1, f1, (TFun t11 t12)) = getConstraints e1 (f+1) in
 --                           let (c2, f2, t2) = getConstraints e2 (f1+1) in
 --                           ([(new, t12), (t11,t2)] ++ c1 ++ c2, f, new)

getConstraints (Call e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(t1, (TFun t2 new))] ++ c1 ++ c2, f, new)


getConstraints (Declare str e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, t2)] ++ c1 ++ c2, f, new)

getConstraints (If e1 e2 e3) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            let (c3, f3, t3) = getConstraints e3 (f2+1) env in
                            ([(t1, TBool), (t2,t3)] ++ c1 ++ c2 ++ c3, f, new)


replace x e1 (Literal a) = Literal a
replace x e1 (Variable y) = if x == y then
                                e1
                            else 
                                Variable y
replace x e1 (Binary Add e2 e3) = (Binary Add (replace x e1 e2) (replace x e1 e3)) 
replace x e1 (Binary Mul e2 e3) = (Binary Mul (replace x e1 e2) (replace x e1 e3)) 
replace x e1 (Call e2 e3) = (Call (replace x e1 e2) (replace x e1 e3)) 

replace x e1 (Declare y e2 e3) = if x==y then
                                     (Declare y e2 e3) 
                                 else
                                     (Declare y (replace x e1 e2) (replace x e1 e3)) 

substinty tyX tyT tyS = 
--f tyS
    case tyS of
        TInt -> TInt
        TBool -> TBool
        TVar xx -> if xx==tyX then tyT else (TVar xx)
        TFun tyS1 tyS2 -> (TFun (substinty tyX tyT tyS1) (substinty tyX tyT tyS2))
{-
    where
            f (TFun tyS1 tyS2) = (TFun (f tyS1) (f tyS2))
            f TInt = TInt
            f TBool = TBool
            f (TVar xx) = if xx==tyX then tyT else (TVar xx)-}

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
                --(unify (substinconstr tyX tyS rest)) ++ [((TVar tyX),tyS)]
                --(unify (substinconstr tyX tyS rest)) ++ [((TVar tyX),tyS)]
                compose (unify (substinconstr tyX tyS rest)) ((TVar tyX),tyS)
        unify (((TVar tyX),tyT):rest) =
            if tyT == (TVar tyX) then 
                unify rest 
            else if (occur tyX tyT) then
                --error fi (msg ^ ": circular constraints")
                [(tyT,TError)]
            else
                --(unify (substinconstr tyX tyT rest)) ++ [((TVar tyX),tyT)]
                compose (unify (substinconstr tyX tyT rest))  ((TVar tyX),tyT)
        unify ((TInt,TInt):xs) = unify xs
        unify ((TBool,TBool):xs) = unify xs
        unify (((TFun s1 t1),(TFun s2 t2)):xs) = unify ((s1,s2):(t1,t2):xs)
        unify _ = [(TError,TError)]

--compose :: [(Type, Type)] -> (Type, Type) -> [(Type, Type)]
compose l (tx, ty) =
        let lhs = [ (x,y) | (x,y) <- l, x /= tx] in 
        --let orgMap = (Map.fromList l) in 
        --let orgMap = Map.empty  in 
        --let newMap = (Map.insert tx ty $ orgMap) in
        --_ -> Map.toList (Map.insert tx (queryType ty newMap) $ newMap)
            case ty of
                TInt -> lhs ++ [(tx,ty)]
                TBool -> lhs ++ [(tx,ty)]
                _   -> lhs ++ [(tx,(queryType ty lhs))]

--queryType :: (Type, Type) -> Data.Map -> Type
queryType ty env =
        case ty of
            (TVar x)  -> 
                     --if (Map.member ty $ env) then
                        --eliminate (Map.lookup ty $ env) 
                    solve env ty
            (TFun f1 f2) -> TFun (queryType f1 env) (queryType f2 env)

solve [] ty = ty
solve (x:xs) newType = 
                      if (fst x == newType) then 
                          snd x
                      else 
                          grep xs newType
 
{-
compose l (tx, ty) =
        case l of 
            [] -> [(tx, ty)]
            x:xs -> case x of 
                (ttx, (TFun y1 y2)) -> (compose xs (tx,ty)) ++ [(ttx, (TFun (swap y1 (tx,ty)) (swap y2 (tx,ty))))]
                (ttx, tty) -> if tty == tx then
                                    (compose xs (tx,ty)) ++  [(ttx, ty)]
                              else 
                                    (compose xs (tx,ty)) ++  [(ttx, tty)] -}

swap :: Type -> (Type, Type) -> Type
swap tx (ty1, ty2) = if tx == ty1 then
                         ty2
                     else 
                         tx

--let-polymorphism
--generalize l =


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
