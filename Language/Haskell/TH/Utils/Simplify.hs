{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types #-}
module Language.Haskell.TH.Utils.Simplify (Simplify,simplify) where

import Control.Monad (liftM)
import Language.Haskell.TH


-- | Simplify is used to evaluate simple expressions like
-- > 1 + 2
-- 3
-- > if 2 > 4 then 1 else 0
-- 0
--
-- Such kind of simple definitions which can be evaluated at compile
-- time will be substituted. Although these optimizations will already
-- be performed by the compiler but simplify becomes important after
-- substitution.
class Simplify a where
  simplify :: a -> a

-- | Simplifying can be done inside the Q monad.
instance Simplify a => Simplify (Q a) where
  simplify = liftM simplify

-- | Simplification of a list of terms is same as simplifying each one
-- of them.
instance Simplify a => Simplify [a] where
  simplify = map simplify

-- | Simplify Expression recursively.
instance Simplify Exp where
  simplify (VarE o) | o == 'otherwise  = (ConE 'True)
  simplify (AppE e1 e2) = AppE (simplify e1) (simplify e2)
  simplify (InfixE me1 e me2) =
    case (fmap simplify me1,simplify e,fmap simplify me2) of
      (Nothing,op,a) -> InfixE Nothing op a
      (a,op,Nothing) -> InfixE a op Nothing
      (Just a,op,Just b) -> simplifyInfix a op b
  simplify (UInfixE e1 e e2) = simplifyInfix (simplify e1)
                                             (simplify e)
                                             (simplify e2)
  simplify (ParensE e) = ParensE (simplify e)
  simplify (LamE pats e) = LamE pats (simplify e)
  simplify (LamCaseE m) = LamCaseE (simplify m)
  simplify (TupE es) = TupE (simplify es)
  simplify (UnboxedTupE es) = UnboxedTupE (simplify es)
  simplify (CondE e1 e2 e3) = case (simplify e1) of
    x | x == ConE 'True -> simplify e2
      | x == ConE 'False -> simplify e3
      | otherwise -> CondE x (simplify e1) (simplify e2)
  simplify (MultiIfE gexp) =
    let simplified = map (\(a,b) -> (simplify a, simplify b)) gexp
        filtered = filter (\(a,_) -> a /= NormalG (ConE 'False)) simplified
      in case filtered of
           o@((g,expr):_) | g == NormalG (ConE 'True) -> expr
                          | otherwise -> MultiIfE o
           _ -> MultiIfE []
  simplify (LetE decs expr)  = LetE (simplify decs) (simplify expr)
  simplify (CaseE expr m) = CaseE (simplify expr) (simplify m)
  simplify (DoE ss) = DoE (simplify ss)
  simplify (CompE ss) = CompE (simplify ss)
  simplify (ArithSeqE as) = ArithSeqE (simplify as)
  simplify (ListE es) = ListE (map (simplify) es)
  simplify (SigE e t) = SigE (simplify e) t
  simplify (RecConE name fexps) = RecConE name
                                          (map (\(a,b) -> (a,simplify b)) fexps)
  simplify (RecUpdE expr fexps) = RecUpdE (simplify expr)
                                         (map (\(a,b) -> (a,simplify b)) fexps)
  simplify a = a

-- | Simplify Match recursively.
instance Simplify Match where
  simplify (Match p b decs) = Match p (simplify b) (simplify decs)

-- | Simplify Body recursively.
instance Simplify Body where
  simplify (GuardedB gexp) =
    let simplified = map (\(a,b) -> (simplify a, simplify b)) gexp
        filtered = filter (\(a,_) -> a /= NormalG (ConE 'False)) simplified
      in case filtered of
           o@((g,expr):_) | g == NormalG (ConE 'True) -> NormalB expr
                             | otherwise -> GuardedB o
           _ -> GuardedB []
  simplify (NormalB expr) = NormalB (simplify expr)

-- | Simplify Guard recursively.
instance Simplify Guard where
  simplify (NormalG expr) = NormalG (simplify expr)
  simplify (PatG s) = PatG (simplify s)

-- | Simplify Statement recusively.
instance Simplify Stmt where
  simplify (BindS p e) = BindS p (simplify e)
  simplify (LetS decs) = LetS (simplify decs)
  simplify (NoBindS e) = NoBindS (simplify e)
  simplify (ParS e) = ParS (simplify e)

-- | Simplify Declaration recursively.
instance Simplify Dec where
  simplify (FunD f c) = FunD f (simplify c)
  simplify (ValD p b d) = ValD p (simplify b) (simplify d)
  simplify (ClassD cntxt c ty fd d) = ClassD cntxt c ty fd (simplify d)
  simplify (InstanceD cntxt ty d) = InstanceD cntxt ty (simplify d)
  simplify d = d

-- | Simplify Clause recursively.
instance Simplify Clause where
  simplify (Clause pat body decs) =  Clause pat (simplify body) (simplify decs)

-- | Simplify Range recursively.
instance Simplify Range where
  simplify (FromR e) = FromR (simplify e)
  simplify (FromThenR e1 e2) = FromThenR (simplify e1) (simplify e2)
  simplify (FromToR e1 e2) = FromToR (simplify e1) (simplify e2)
  simplify (FromThenToR e1 e2 e3) = FromThenToR (simplify e1)
                                                (simplify e2)
                                                (simplify e3)

-- | Simplify an infix binary operation.
-- It Simplifies only simple operators like >, <, >=, <=, +, -, *

-- @TODO add support for operators like ^,&&,|| etc
-- @TODO Think of a way to make it generic for any kind of binary operator
simplifyInfix :: Exp -> Exp -> Exp -> Exp
simplifyInfix (LitE lit1)
              (VarE op)
              (LitE lit2) | op == '(<) = simplifyLitOrd lit1 (<) lit2
                          | op == '(<=) = simplifyLitOrd lit1 (<=) lit2
                          | op == '(>) = simplifyLitOrd lit1 (>) lit2
                          | op == '(>=) = simplifyLitOrd lit1 (>=) lit2
                          | op == '(+) = simplifyLitNum lit1 (+) lit2
                          | op == '(-) = simplifyLitNum lit1 (-) lit2
                          | op == '(*) = simplifyLitNum lit1 (*) lit2
simplifyInfix (LitE (IntegerL 0))
              (VarE op)
              (VarE v) | op == '(+) = VarE v
                       | op == '(*) = LitE (IntegerL 0)
simplifyInfix (VarE v)
              (VarE op)
              (LitE (IntegerL 0)) | op == '(+) = VarE v
                                  | op == '(*) = LitE (IntegerL 0)
simplifyInfix (LitE (IntegerL 1)) (VarE op) (VarE v) | op == '(*) = VarE v
simplifyInfix (VarE v) (VarE op) (LitE (IntegerL 0)) | op == '(*) = VarE v
simplifyInfix a op b = UInfixE a op b

-- | We need to separate ordinal operators as their return types are different.
-- Ordinal operators on literals can be simplified at compile time.
simplifyLitOrd :: Lit -> (forall a . (Ord a) => a -> a -> Bool) -> Lit -> Exp
simplifyLitOrd (CharL c1) op (CharL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (StringL c1) op (StringL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (IntegerL c1) op (IntegerL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (RationalL c1) op (RationalL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (IntPrimL c1) op (IntPrimL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (WordPrimL c1) op (WordPrimL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (FloatPrimL c1) op (FloatPrimL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (DoublePrimL c1) op (DoublePrimL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd (StringPrimL c1) op (StringPrimL c2) = ConE $ b2n (op c1 c2)
simplifyLitOrd _ _ _ = error "Unknown operator"

-- | Simplify binary operators on literals.
simplifyLitNum :: Lit -> (forall a . (Num a) => a -> a -> a) -> Lit -> Exp
simplifyLitNum (IntegerL c1) op (IntegerL c2) = LitE $ IntegerL (op c1 c2)
simplifyLitNum (RationalL c1) op (RationalL c2) = LitE $ RationalL (op c1 c2)
simplifyLitNum (IntPrimL c1) op (IntPrimL c2) = LitE $ IntPrimL (op c1 c2)
simplifyLitNum (WordPrimL c1) op (WordPrimL c2) = LitE $ WordPrimL  (op c1 c2)
simplifyLitNum (FloatPrimL c1) op (FloatPrimL c2) = LitE $ FloatPrimL (op c1 c2)
simplifyLitNum (DoublePrimL c1) op (DoublePrimL c2) = LitE $ DoublePrimL (op c1 c2)
simplifyLitNum _ _ _ = error "Unknown error"

-- | Converts boolean to Name
b2n :: Bool -> Name
b2n True = 'True
b2n False = 'False
