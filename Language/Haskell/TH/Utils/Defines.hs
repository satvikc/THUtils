{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.Utils.Defines (Defines,defines) where

import Data.Set (Set,union,unions)
import qualified Data.Set as S
import Language.Haskell.TH

-- | This class captures all the variables declared in this context.
class Defines a where
  defines :: a -> Set Name

-- | Variables declared in a list of contexts is just the union of
-- variables declared in each of them.
instance Defines a => Defines [a] where
  defines = unions . map defines

-- | Variables declared in a pattern due to patten matching.
instance Defines Pat where
  defines (VarP n) = S.singleton n
  defines (TupP pats) = defines pats
  defines (UnboxedTupP pats) = defines pats
  defines (ConP _ pats) = defines pats
  defines (InfixP p1 _ p2) = union (defines p1) (defines p2)
  defines (UInfixP p1 _ p2) = union (defines p1) (defines p2)
  defines (ParensP p) = defines p
  defines (TildeP p) = defines p
  defines (BangP p) = defines p
  defines (AsP n p) = union  (S.singleton n) (defines p)
  defines (RecP _ fps) = unions $ map (defines . snd) fps
  defines (ListP pats) = defines pats
  defines (SigP p _) = defines p
  defines (ViewP _ p) = defines p
  defines _ = S.empty

-- | Variables declared in a declaration.
instance Defines Dec where
  defines (FunD n _) = S.singleton n
  defines (ValD p _ _) = defines p
  defines (ClassD _ _ _ _ d) = defines d
  defines (SigD n _) = S.singleton n
  defines (ForeignD f) = defines f
  defines _ = S.empty

-- | Variables declared due to importing from foreign interface.
instance Defines Foreign where
  defines (ImportF _ _ _ n _) = S.singleton n
  defines _ = S.empty
