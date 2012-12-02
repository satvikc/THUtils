{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.Utils.Substitute (Substitute,substitute,substitute_list) where

import Data.Set (member)
import Language.Haskell.TH

import Language.Haskell.TH.Utils.Defines

-- | Substitute a variable name by an Exp
class Substitute a where
  substitute :: Name -> Exp -> a -> a
  substitute_list :: Name -> Exp -> [a] -> [a]
  substitute_list n l = map (substitute n l)

instance Substitute a => Substitute [a] where
  substitute = substitute_list

instance Substitute Exp where
  substitute n l (VarE i) | i == n = l
                          | otherwise = (VarE i)
  substitute n l (AppE e1 e2) = AppE (substitute n l e1) (substitute n l e2)
  substitute n l (InfixE me1 e me2) = InfixE (fmap (substitute n l) me1) (substitute n l e) (fmap (substitute n l) me2)
  substitute n l (UInfixE e1 e e2) = UInfixE (substitute n l e1) (substitute n l e) (substitute n l e2)
  substitute n l (ParensE e) = ParensE (substitute n l e)
  substitute n l (LamE pat e) | member n (defines pat) = LamE pat e
                              | otherwise = LamE pat (substitute n l e)
  substitute n l (LamCaseE m) = LamCaseE (substitute n l m)
  substitute n l (TupE es) = TupE (substitute n l es)
  substitute n l (UnboxedTupE es) = UnboxedTupE (substitute n l es)
  substitute n l (CondE e1 e2 e3) = CondE (substitute n l e1) (substitute n l e2) (substitute n l e3)
  substitute n l (MultiIfE ges) = MultiIfE $ map (\(g,e) -> (substitute n l g,substitute n l e)) ges
  substitute n l (LetE decs exp) | member n (defines decs) = LetE decs exp
                                 | otherwise = LetE (substitute n l decs) (substitute n l exp)
  substitute n l (CaseE exp m) = CaseE (substitute n l exp) (substitute n l m)
  substitute n l (DoE ss) = DoE (substitute n l ss)
  substitute n l (CompE ss) = CompE (substitute n l ss)
  substitute n l (ArithSeqE as) = ArithSeqE (substitute n l as)
  substitute n l (ListE es) = ListE (map (substitute n l) es)
  substitute n l (SigE e t) = SigE (substitute n l e) t
  substitute n l (RecConE name fexps) = RecConE name (map (\(a,b) -> (a,substitute n l b)) fexps)
  substitute n l (RecUpdE exp fexps) = RecUpdE (substitute n l exp)  (map (\(a,b) -> (a,substitute n l b)) fexps)
  substitute _ _ a = a

instance Substitute Match where
  substitute n l m@(Match p b decs) | member n (defines p) = m
                                    | member n (defines decs) = m
                                    | otherwise = Match p (substitute n l b) (substitute n l decs)

instance Substitute Body where
  substitute n l (GuardedB gexp) = GuardedB $ map (\(g,e) -> (substitute n l g,substitute n l e)) gexp
  substitute n l (NormalB exp) = NormalB (substitute n l exp)

instance Substitute Guard where
  substitute n l (NormalG exp) = NormalG (substitute n l exp)
  substitute n l (PatG s) = PatG (substitute n l s)

instance Substitute Stmt where
  substitute n l (BindS p e) | member n (defines p) = BindS p e
                             | otherwise = BindS p (substitute n l e)
  substitute n l (LetS decs) = LetS (substitute n l decs)
  substitute n l (NoBindS e) = NoBindS (substitute n l e)
  substitute n l (ParS e) = ParS (substitute n l e)

instance Substitute Dec where
  substitute n l d | member n (defines d) = d
  substitute n l (FunD f c) = FunD f (substitute n l c)
  substitute n l (ValD p b d) = ValD p (substitute n l b) (substitute n l d)
  substitute n l (ClassD cxt c ty fd d) = ClassD cxt c ty fd (substitute n l d)
  substitute n l (InstanceD cxt ty d) = InstanceD cxt ty (substitute n l d)
  substitute _ _ d = d
  substitute_list n l decs | member n (defines decs) = decs
                           | otherwise = map (substitute n l) decs

instance Substitute Clause where
  substitute n l c@(Clause pat body decs) | member n (defines pat) = c
                                          | member n (defines decs) = c
                                          | otherwise = Clause pat (substitute n l body) (substitute n l decs)

instance Substitute Range where
  substitute n l (FromR e) = FromR (substitute n l e)
  substitute n l (FromThenR e1 e2) = FromThenR (substitute n l e1) (substitute n l e2)
  substitute n l (FromToR e1 e2) = FromToR (substitute n l e1) (substitute n l e2)
  substitute n l (FromThenToR e1 e2 e3) = FromThenToR (substitute n l e1) (substitute n l e2) (substitute n l e3)
