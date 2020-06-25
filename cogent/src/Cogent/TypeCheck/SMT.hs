
--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.TypeCheck.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.PrettyPrint (indent')
import Cogent.TypeCheck.Base
import Cogent.Surface as S

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.State
import Data.IntMap as IM
import Data.Map    as M
import Data.SBV as SMT
import Data.SBV.Dynamic as SMT
import Lens.Micro.Mtl
import Lens.Micro.TH
import Text.PrettyPrint.ANSI.Leijen (pretty)
import Prelude as P


data SmtTransState = SmtTransState { _unifs :: IntMap SVal
                                   , _vars  :: Map String SVal
                                   , _fresh :: Int
                                   }

makeLenses ''SmtTransState

type SmtTransM = StateT SmtTransState Symbolic

typeToSmt :: TCType -> SmtTransM SMT.Kind
typeToSmt (T (TCon "Bool" [] Unboxed)) = return KBool
typeToSmt (T (TCon "String" [] Unboxed)) = return KString
typeToSmt (T (TCon n [] Unboxed))
  = let w = if | n == "U8"  -> 8
               | n == "U16" -> 16
               | n == "U32" -> 32
               | n == "U64" -> 64
     in return $ KBounded False w
typeToSmt (T (TTuple ts))  = KTuple <$> mapM typeToSmt ts
typeToSmt (T (TUnit))      = return $ KTuple []
#ifdef REFINEMENT_TYPES
typeToSmt (T (TRefine _ b _)) = typeToSmt b
#endif
typeToSmt t = freshSort >>= \s -> return (KUninterpreted s (Left s))

sexprToSmt :: TCSExpr -> SmtTransM SVal
sexprToSmt (SU t x) = do
  m <- use unifs
  case IM.lookup x m of
    Nothing -> do t' <- typeToSmt t
                  sv <- mkQSymVar SMT.EX ('?':show x) t'
                  unifs %= (IM.insert x sv)
                  return sv
    Just sv -> return sv
sexprToSmt (SE t (PrimOp op [e])) = (liftA $ uopToSmt op) (sexprToSmt e)
sexprToSmt (SE t (PrimOp op [e1,e2])) = (liftA2 $ bopToSmt op) (sexprToSmt e1) (sexprToSmt e2)
sexprToSmt (SE t (Var vn)) = do
  m <- use vars
  case M.lookup vn m of
    Nothing -> do t' <- typeToSmt t
                  sv <- mkQSymVar SMT.ALL vn t'
                  vars %= (M.insert vn sv)
                  return sv
    Just sv -> return sv
  -- NOTE: For uninterpreted constants, SMT doesn't know anything about it, and they behave sort
  --       of like existentials, that if it's *possible* that something is true, then it's satisfiable.
  --       Only when it derives a contradiction it says it's unsat. / zilinc
  -- XXX | return $ svUninterpreted (typeToSmt t) vn Nothing []
-- sexprToSmt (SE t (TLApp f mts mls _)) = undefined
-- sexprToSmt (SE t (App e1 e2 _)) = undefined
sexprToSmt (SE t (IntLit i)) = svInteger <$> typeToSmt t <*> pure i
sexprToSmt (SE t (BoolLit b)) = return $ svBool b
sexprToSmt (SE t (If e _ th el)) = (liftA3 svIte) (sexprToSmt e) (sexprToSmt th) (sexprToSmt el)
sexprToSmt (SE t (Upcast e)) = sexprToSmt e
sexprToSmt (SE t (Annot e _)) = sexprToSmt e
sexprToSmt (SE t _) = freshVal >>= \f -> typeToSmt t >>= \t' -> return (svUninterpreted t' f Nothing [])

-- type SmtM a = StateT (UVars, EVars) V.Symbolic a

bopToSmt :: OpName -> (SVal -> SVal -> SVal)
bopToSmt = \case
  "+"   -> svPlus
  "-"   -> svMinus
  "*"   -> svTimes
  "/"   -> svDivide
  "%"   -> svQuot  -- NOTE: the behaviour of `svDivide` and `svQuot` here. / zilinc
                   -- http://hackage.haskell.org/package/sbv-8.5/docs/Data-SBV-Dynamic.html#v:svDivide
  "&&"  -> svAnd
  "||"  -> svOr
  ".&." -> svAnd
  ".|." -> svOr
  ".^." -> svXOr
  "<<"  -> svShiftLeft
  ">>"  -> svShiftRight
  "=="  -> svEqual
  "/="  -> svNotEqual
  ">"   -> svGreaterThan
  "<"   -> svLessThan
  ">="  -> svGreaterEq
  "<="  -> svLessEq

uopToSmt :: OpName -> (SVal -> SVal)
uopToSmt = \case
  "not"        -> svNot
  "complement" -> svNot

-- ----------------------------------------------------------------------------
-- Helpers
--

mkSymVar :: String -> SMT.Kind -> SmtTransM SVal
mkSymVar nm k = symbolicEnv >>= liftIO . svMkSymVar Nothing k (Just nm)

mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> SmtTransM SVal
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)

bvAnd :: [SVal] -> SVal
bvAnd = P.foldr (svAnd) svTrue

freshVal :: SmtTransM String
freshVal = (("_smt_val_" ++) . show) <$> (fresh <<%= succ)

freshSort :: SmtTransM String
freshSort = (("_smt_sort_" ++) . show) <$> (fresh <<%= succ)

