{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.Utils.Unroll where

import Language.Haskell.TH
import Data.Set (member)

import Language.Haskell.TH.Utils.Defines
import Language.Haskell.TH.Utils.Substitute
import Language.Haskell.TH.Utils.Simplify

-- | Substitute a function application
-- Argument must be a literal only then it will be substituted
-- Very similar to substitute with only one difference in AppE line

-- @TODO think of a way to combine this and substitute
class SubstituteFun a where
  substituteFun :: Name -> (Name -> Lit -> Exp) -> a -> a
  substituteFun_list :: Name -> (Name -> Lit -> Exp) -> [a] -> [a]
  substituteFun_list n l = map (substituteFun n l)

instance SubstituteFun a => SubstituteFun [a] where
  substituteFun = substituteFun_list

instance SubstituteFun Exp where
  substituteFun n l (AppE (VarE v) (LitE lit)) | v == n = l v lit
  substituteFun n l (AppE e1 e2) = AppE (substituteFun n l e1)
                                        (substituteFun n l e2)
  substituteFun n l (InfixE me1 e me2) = InfixE (fmap (substituteFun n l) me1)
                                                (substituteFun n l e)
                                                (fmap (substituteFun n l) me2)
  substituteFun n l (UInfixE e1 e e2) = UInfixE (substituteFun n l e1)
                                                (substituteFun n l e)
                                                (substituteFun n l e2)
  substituteFun n l (ParensE e) = ParensE (substituteFun n l e)
  substituteFun n l (LamE pat e) | member n (defines pat) = LamE pat e
                                 | otherwise = LamE pat (substituteFun n l e)
  substituteFun n l (LamCaseE m) = LamCaseE (substituteFun n l m)
  substituteFun n l (TupE es) = TupE (substituteFun n l es)
  substituteFun n l (UnboxedTupE es) = UnboxedTupE (substituteFun n l es)
  substituteFun n l (CondE e1 e2 e3) = CondE (substituteFun n l e1)
                                             (substituteFun n l e2)
                                             (substituteFun n l e3)
  substituteFun n l (MultiIfE ges) = MultiIfE $
                                      map (\(g,e) -> ( substituteFun n l g
                                                    , substituteFun n l e)) ges
  substituteFun n l (LetE decs expr) | member n (defines decs) = LetE decs expr
                                     | otherwise = LetE (substituteFun n l decs)
                                                       (substituteFun n l expr)
  substituteFun n l (CaseE expr m) =
    CaseE (substituteFun n l expr) (substituteFun n l m)
  substituteFun n l (DoE ss) = DoE (substituteFun n l ss)
  substituteFun n l (CompE ss) = CompE (substituteFun n l ss)
  substituteFun n l (ArithSeqE as) = ArithSeqE (substituteFun n l as)
  substituteFun n l (ListE es) = ListE (map (substituteFun n l) es)
  substituteFun n l (SigE e t) = SigE (substituteFun n l e) t
  substituteFun n l (RecConE name fexps) =
    RecConE name (map (\(a,b) -> (a,substituteFun n l b)) fexps)
  substituteFun n l (RecUpdE expr fexps) =
    RecUpdE (substituteFun n l expr) $
            map (\(a,b) -> (a,substituteFun n l b)) fexps
  substituteFun _ _ a = a

instance SubstituteFun Match where
  substituteFun n l m@(Match p b decs) | member n (defines p) = m
                                       | member n (defines decs) = m
                                       | otherwise = Match p
                                                       (substituteFun n l b)
                                                       (substituteFun n l decs)

instance SubstituteFun Body where
  substituteFun n l (GuardedB gexp) =
    GuardedB $ map (\(g,e) -> (substituteFun n l g,substituteFun n l e)) gexp
  substituteFun n l (NormalB expr) = NormalB (substituteFun n l expr)

instance SubstituteFun Guard where
  substituteFun n l (NormalG expr) = NormalG (substituteFun n l expr)
  substituteFun n l (PatG s) = PatG (substituteFun n l s)

instance SubstituteFun Stmt where
  substituteFun n l (BindS p e) | member n (defines p) = BindS p e
                                | otherwise = BindS p (substituteFun n l e)
  substituteFun n l (LetS decs) = LetS (substituteFun n l decs)
  substituteFun n l (NoBindS e) = NoBindS (substituteFun n l e)
  substituteFun n l (ParS e) = ParS (substituteFun n l e)

instance SubstituteFun Dec where
  substituteFun n _ d | member n (defines d) = d
  substituteFun n l (FunD f c) = FunD f (substituteFun n l c)
  substituteFun n l (ValD p b d) =
    ValD p (substituteFun n l b) (substituteFun n l d)
  substituteFun n l (ClassD cntxt c ty fd d) =
    ClassD cntxt c ty fd (substituteFun n l d)
  substituteFun n l (InstanceD cntxt ty d) =
    InstanceD cntxt ty (substituteFun n l d)
  substituteFun _ _ d = d
  substituteFun_list n l decs | member n (defines decs) = decs
                              | otherwise = map (substituteFun n l) decs

instance SubstituteFun Clause where
  substituteFun n l c@(Clause pat body decs) | member n (defines pat) = c
                                             | member n (defines decs) = c
                                             | otherwise = Clause pat
                                                         (substituteFun n l body)
                                                         (substituteFun n l decs)

instance SubstituteFun Range where
  substituteFun n l (FromR e) = FromR (substituteFun n l e)
  substituteFun n l (FromThenR e1 e2) = FromThenR (substituteFun n l e1)
                                                  (substituteFun n l e2)
  substituteFun n l (FromToR e1 e2) = FromToR (substituteFun n l e1)
                                              (substituteFun n l e2)
  substituteFun n l (FromThenToR e1 e2 e3) = FromThenToR (substituteFun n l e1)
                                                         (substituteFun n l e2)
                                                         (substituteFun n l e3)

-- | unroll the recursion bottom up
-- example
-- @unrollB 0 1 [d| f i = 1 |]@
-- @unrollB 2 5 [d| f i = f (i-1) + f (i-2) |]@ will produce
-- f_0 = 1
-- f_1 = 1
-- f_2 = 2
-- f_3 = 3
-- f_4 = 5
-- f_5 = 8
--

unrollB :: Int             -- ^ Lower bound
        -> Int             -- ^ Upper bound
        -> DecQ            -- ^ Recursive function body to unroll
        -> DecsQ
unrollB from to d = do
    (FunD f [(Clause ps body decs)]) <- d
    let (VarP loopVar) = head ps
    return $ map (createFun f loopVar body decs) [from .. to]
  where
    createFun f loopVar body decs i = let fname = nameBase f in
      substituteFun f (\a (IntegerL b) ->
                         VarE $ mkName $ nameBase a ++ "_" ++ show b )
                  (simplify $ ValD (VarP $ mkName (fname ++ "_" ++ show i))
                  (substitute loopVar (LitE $ integerL $ fromIntegral i) body)
                  (substitute loopVar (LitE $ integerL $ fromIntegral i) decs))