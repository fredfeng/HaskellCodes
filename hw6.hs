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

--helper Function to retrive data from tuple
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

--helper Function to retrive data from tuple
thd3 :: (a, b, c) -> c
thd3 (_, _, x) = x

-- search for the value of a given type var, if fails, return type error.
grep [] newType = TError
grep (x:xs) newType = if checkError (x:xs) then
                          TError
                      else 
                          if (fst x == newType) then 
                              snd x
                          else 
                              grep xs newType
                        
--check whether current list contains TError.
checkError [] = False
checkError (x:xs) = if (fst x == TError) then
                        True
                    else
                        checkError xs
--Type inference
infer :: Exp -> Type
infer e = let env = Map.empty in 
          let constr = (getConstraints e 1 env) in 
          let newType = thd3 constr in 
              grep (unification (fst3 constr)) newType
              --in unification (fst3 constr) 

--Type inference for polymorphism
--infer' :: Exp -> Data.Map -> Type
infer' e env = 
            let constr = (getConstraints e 1 env) in 
            let newType = thd3 constr in 
                grep (unification (fst3 constr)) newType

eliminate :: Maybe Type -> Type 
eliminate (Just a) = a
eliminate _  = TError

instantiate :: Type -> Int -> (Type,Int)
instantiate (TPoly arr t) f =
    case arr of
        [] -> (TVar "inst", f)
        (x:xs) -> 
            let instList = buildInstList arr f  in
            (getType instList t, f)

solveS :: [(String, Type)] -> String -> Type
solveS [] ty = TVar "SOLVE"
solveS (x:xs) newType = 
                      if (fst x == newType) then 
                          snd x
                      else 
                          solveS xs newType
 
getType :: [(String, Type)] -> Type -> Type
getType instList t =
    case t of
        --TVar x -> solveS instList x 
        TVar x -> 
            let newlist = (Map.fromList instList) in 
            eliminate (Map.lookup x $ newlist)
        TFun x y -> TFun (getType instList x) (getType instList y)

buildInstList :: [String] -> Int -> [(String, Type)]
buildInstList args f =
    case args of
        [] -> []
        (x:xs) -> [(x,TVar ("x"++ show (f+100)))] ++ (buildInstList xs (f+1001))

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
                let tx = eliminate (Map.lookup x $ env) in  
                    case tx of
                        --if it's polymorphism, instantiate it with fresh var..
                        TPoly arr t -> 
                              case t of
                                TVar y -> 
                                    --let new = TVar ("x"++ show f) in
                                    let (new,f1) = instantiate (TPoly arr t) f in 
                                    ([(new, TVar ("x"++ show (f+1))) ], f, new)
                                TFun y1 y2 ->
                                    --let new = TVar ("x"++ show f) in
                                    let (new,f1) = instantiate (TPoly arr t) f in 
                                    ([(new, TVar ("x"++ show (f+1))) ], f, new)
                        _ -> ([], f, tx)
            else
            --create a new one.
                ([], f, (TVar("x"++ show f)))

--data UnaryOp = Neg | Not
-- Unary     UnaryOp Exp
getConstraints (Unary Not e) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e (f+1) env in
                             ([(new, TBool), (t1,TBool)] ++ c1, f, new)

getConstraints (Unary Neg e) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e (f+1) env in
                             ([(new, TInt), (t1,TInt)] ++ c1, f, new)

--data BinaryOp = Add | Sub | Mul | Div | And | Or
--              | GT | LT | LE | GE | EQ

getConstraints (Binary Add e1 e2) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) env in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)


getConstraints (Binary Mul e1 e2) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) env in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)

getConstraints (Binary Div e1 e2) f env = let new = TVar ("x"++ show f) in
                             let (c1, f1, t1) = getConstraints e1 (f+1) env in
                             let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                             ([(new, TInt), (t1,TInt), (t2,TInt)] ++ c1 ++ c2, f, new)

getConstraints (Binary And e1 e2) f env = let new = TVar ("x-gt"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary Or e1 e2) f env = let new = TVar ("x-gt"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary GT e1 e2) f env = let new = TVar ("x-gt"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary LT e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary LE e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary GE e1 e2) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)

getConstraints (Binary EQ e1 e2) f env = let new = TVar ("x-eq"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+770) env in
                            ([(new, TBool), (t1,t2)] ++ c1 ++ c2, f, new)


getConstraints (Function x body) f env = let tme = TVar ("x"++ show f) in
                            let tx = TVar ("x"++ show (f+1)) in
                            let newenv =  Map.insert ("x"++ show(f+1)) tx env in
                            let (c1, f1, tbody) = getConstraints body (f+1) newenv in
                            ([(tme, (TFun tx tbody))] ++ c1, f, tme)

getConstraints (Call e1 e2) f env = 
        case e1 of
            Variable x ->
                        let new = TVar ("x-call"++ show f) in
                        let (c1, f1, (TFun targ tbody)) = getConstraints e1 (f+1) env in
                        let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                        ([(targ, t2), (new, tbody)] ++ c2, f, new)

            --for subtract
            Literal (IntV i) ->
                        let new = TVar ("x"++ show f) in
                        let (c1, f1, t1) = getConstraints e1 (f+1) env in
                        let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                        ([(t2, TInt), (new, TInt), (t1,t2)] ++ c1 ++ c2, f, new)

            Literal (BoolV b) ->
                        let new = TVar ("x"++ show f) in
                        let (c1, f1, t1) = getConstraints e1 (f+1) env in
                        let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                        ([(t2, TInt), (new, TInt), (t1,t2)] ++ c1 ++ c2, f, new)

            _ ->
                        let new = TVar ("xxx-call"++ show f) in
                        let (c1, f1, t1) = getConstraints e1 (f+1) env in
                        let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                        ([(t1, (TFun t2 new))] ++ c1 ++ c2, f, new)

getConstraints (Declare id exp body) f env = 
                            let texp = infer' exp env in
--if texp is TError or concrete type, no need to polymorphism
                            let tgen = generalize texp in
                            let newenv =  Map.insert id tgen env in
                            getConstraints body f newenv


getConstraints (If e1 e2 e3) f env = let new = TVar ("x"++ show f) in
                            let (c1, f1, t1) = getConstraints e1 (f+1) env in
                            let (c2, f2, t2) = getConstraints e2 (f1+1) env in
                            let (c3, f3, t3) = getConstraints e3 (f2+1) env in
                            ([(t1, TBool), (t2,t3)] ++ c1 ++ c2 ++ c3, f, new)

--let-polymorphism generalize TPoly
--generalize texp =  TPoly [String] Type
generalize texp =  
                case texp of
                    TInt -> TInt
                    TBool-> TBool
                    TVar x ->  TPoly [x] (TVar x)
                    TFun t1 t2 -> 
                        if checkPoly texp then
                            TPoly (nub (extractVar t1 ++ extractVar t2))  (TFun t1 t2)
                        else 
                            texp

--do we need polymorphism?
checkPoly :: Type -> Bool
checkPoly t = 
    case t of
        TInt -> False
        TBool -> False
        TError -> False
        TVar x -> True
        TFun t1 t2 -> checkPoly t1 || checkPoly t2

--extract Variable(s) from Type.
extractVar texp =
                case texp of
                    TInt -> []
                    TBool-> []
                    TVar x -> [x]
                    --remove duplicated elements
                    TFun t1 t2 -> nub ((extractVar t1) ++ (extractVar t2))

--old code to perform let binding without polymorphism, no use any more.
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
    case tyS of
        TInt -> TInt
        TBool -> TBool
        TVar xx -> if xx==tyX then tyT else (TVar xx)
        TFun tyS1 tyS2 -> (TFun (substinty tyX tyT tyS1) (substinty tyX tyT tyS2))

--check occurance.
occur tyX tyT = occr tyT 
                where   occr (TFun tyT1 tyT2) = (occr tyT1) || (occr tyT2)
                        occr TInt = False
                        occr TBool = False
                        occr (TVar xx) = (xx == tyX)

--performing substution.
substinconstr tyX tyT constr = 
    map (\(tyS1,tyS2) -> (substinty tyX tyT tyS1, substinty tyX tyT tyS2)) constr

--unification algorithm
unification ll = unify ll
    where 
        unify [] = []
        unify ((tyS,(TVar tyX)):rest) =
            if tyS == (TVar tyX) then 
                unify rest 
            else if (occur tyX tyS) then
                [(tyS,TError)]
            else
                compose (unify (substinconstr tyX tyS rest)) ((TVar tyX),tyS)
        unify (((TVar tyX),tyT):rest) =
            if tyT == (TVar tyX) then 
                unify rest 
            else if (occur tyX tyT) then
                [(tyT,TError)]
            else
                compose (unify (substinconstr tyX tyT rest))  ((TVar tyX),tyT)
        unify ((TInt,TInt):xs) = unify xs
        unify ((TBool,TBool):xs) = unify xs
        unify (((TFun s1 t1),(TFun s2 t2)):xs) = unify ((s1,s2):(t1,t2):xs)
        unify _ = [(TError,TError)]

--compose :: [(Type, Type)] -> (Type, Type) -> [(Type, Type)]
compose l (tx, ty) =
        let lhs = [ (x,y) | (x,y) <- l, x /= tx] in 
            case ty of
                TInt -> lhs ++ [(tx,ty)]
                TBool -> lhs ++ [(tx,ty)]
                _   -> lhs ++ [(tx,(queryType ty lhs))]

--queryType :: (Type, Type) -> Data.Map -> Type
queryType ty env =
        case ty of
            (TVar x)  -> 
                    solve env ty
            (TFun f1 f2) -> TFun (queryType f1 env) (queryType f2 env)

--solve a given type var.
solve [] ty = ty
solve (x:xs) newType = 
                      if (fst x == newType) then 
                          snd x
                      else 
                          solve xs newType
 
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
