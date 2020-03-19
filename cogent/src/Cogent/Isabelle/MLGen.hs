--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

-- {-# OPTIONS_GHC -Werror -Wall #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Cogent.Isabelle.MLGen
  ( deepML )
where

{-
  This file generates Poly/ML deep embeddings of Cogent terms and types.
-}

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Core
import Cogent.Compiler (__cogent_root_dir)

import qualified Data.Vec as Vec
import Control.Monad ((<=<))

import qualified Text.PrettyPrint.ANSI.Leijen as L
import Text.PrettyPrint.ANSI.Leijen ((<+>))

import Data.Bifunctor

import Debug.Trace

deepML :: Show a => String -> [Definition TypedExpr a] -> L.Doc
deepML fname defns =
  let header = L.text "theory" <+> L.text fname <> L.line <>
               L.text "  imports" <+> L.dquotes (L.text $ __cogent_root_dir ++ "/isa/tac/Syntax") <> L.line <>
              --  L.text "  imports CogentTactics.Syntax" <> L.line <>
               L.text "begin" <> L.line <>
               L.line <>
               L.text "ML \\<open>"
      footer = L.text "\\<close>" <> L.line <>
               L.text "end"
      body = L.vsep $ concatMap (pure . docMLTerm <=< deepDefn) defns
   in header <> L.line <> body <> L.line <> footer

docMLTerm :: MLTerm -> L.Doc
docMLTerm (MLApp f a@MLApp{}) = docMLTerm f <+> L.parens (docMLTerm a)
docMLTerm (MLApp f a)         = docMLTerm f <+> docMLTerm a
docMLTerm (MLId s)            = L.text s
docMLTerm (MLList as)         = L.list $ map docMLTerm as
docMLTerm (MLTuple as)         = L.tupled $ map docMLTerm as
docMLTerm (MLString s)        = L.dquotes $ L.text s -- TODO,FIXME: probably need to escape
docMLTerm (MLRecord fs)       = L.encloseSep (L.lbrace <> L.space) (L.space <> L.rbrace) (L.comma <> L.space) $
                                  (\(n,tm) -> L.text n <+> L.equals <+> docMLTerm tm) <$> fs
docMLTerm (MLValBind v a)     = L.text "val" <+> L.text v <+> L.equals <+> docMLTerm a <> L.semi

-- An ad hoc datatype for generating Poly/ML
data MLTerm
  = MLApp MLTerm MLTerm
  | MLId String
  | MLList [MLTerm]
  | MLTuple [MLTerm]
  | MLString String
  | MLRecord [(String,MLTerm)]
  | MLValBind String MLTerm
  deriving (Show,Eq)

mkApp :: MLTerm -> MLTerm -> MLTerm
mkApp = MLApp

mkApp2 :: MLTerm -> MLTerm -> MLTerm -> MLTerm
mkApp2 f a b = MLApp (MLApp f a) b

mkApp3 :: MLTerm -> MLTerm -> MLTerm -> MLTerm -> MLTerm
mkApp3 f a b c = MLApp (MLApp (MLApp f a) b) c

mkRecord :: [(String,MLTerm)] -> MLTerm
mkRecord = MLRecord

mkId :: String -> MLTerm
mkId = MLId

mkInt :: Int -> MLTerm
mkInt x = MLId (show x)

mkInteger :: Integer -> MLTerm
mkInteger x = MLString (show x)

mkList :: [MLTerm] -> MLTerm
mkList = MLList

mkString :: String -> MLTerm
mkString = MLString

mkPair :: MLTerm -> MLTerm -> MLTerm
mkPair a b = MLTuple [a,b]

mkTriple :: MLTerm -> MLTerm -> MLTerm -> MLTerm
mkTriple a b c = MLTuple [a,b,c]

mkBool :: Bool -> MLTerm
mkBool True = mkId "true"
mkBool False = mkId "false"



deepTakenR :: Bool -> MLTerm
deepTakenR True = mkId "Taken"
deepTakenR False = mkId "Untaken"

deepTakenV :: Bool -> MLTerm
deepTakenV True = mkId "Checked"
deepTakenV False = mkId "Unchecked"

deepDefn :: Definition TypedExpr a -> [MLTerm]
deepDefn (FunDef attr fn ts ti to e) = [ MLValBind (fn ++ "_type") $ deepType $ TFun ti to
                                       , MLValBind (fn ++ "_expr") $ deepExpr e
                                       ]
deepDefn (AbsDecl attr fn ts ti to)  = []
deepDefn (TypeDef tn ts mtydef)      = []


deepPrimType :: PrimInt -> MLTerm
deepPrimType U8      = mkId "U8"
deepPrimType U16     = mkId "U16"
deepPrimType U32     = mkId "U32"
deepPrimType U64     = mkId "U64"
deepPrimType Boolean = mkId "Bool"

deepSigil :: Sigil l -> MLTerm
deepSigil (Boxed True _)  = mkId "WR"
deepSigil (Boxed False _) = mkId "RO"
deepSigil Unboxed         = mkId "UB"


deepType :: Type n -> MLTerm
deepType (TVar v)         = mkApp (mkId "TVar"    ) (mkInt $ Vec.finInt v)
deepType (TVarBang v)     = mkApp (mkId "TVarBang") (mkInt $ Vec.finInt v)
deepType (TVarUnboxed v)  = mkApp (mkId "TVarUnboxed") (mkInt $ Vec.finInt v)
deepType (TCon tn ts s)   = mkApp (mkId "TCon"    ) $
                              mkRecord [ ("name", mkString tn)
                                       , ("tyargs", mkList (map deepType ts))
                                       , ("sgl", deepSigil s)
                                       ]
deepType (TFun ti to)     = mkApp (mkId "TFun"    ) $ mkPair (deepType ti) (deepType to)
deepType (TPrim pt)       = mkApp (mkId "TPrim"   ) (deepPrimType pt)
deepType (TString)        = mkApp (mkId "TPrim"   ) (mkId "String")
deepType (TSum alts)      = mkApp (mkId "TSum"    ) (mkList $ map (\(n,(t,b)) -> mkTriple (mkString n) (deepType t) (deepTakenV b)) alts)
deepType (TProduct t1 t2) = mkApp (mkId "TProduct") $ mkPair (deepType t1) (deepType t2)
deepType (TRecord fs s)   = mkApp (mkId "TRecord" ) $
                              mkRecord [ ("fs", mkList (map (\(fn,(t,b)) -> mkTriple (mkString fn) (deepType t) (deepTakenR b)) fs))
                                       , ("sgl", deepSigil s)
                                       ]
deepType (TUnit)          = mkId "TUnit"

deepOp :: Op -> MLTerm
deepOp Plus       = mkId "Plus"
deepOp Minus      = mkId "Minus"
deepOp Times      = mkId "Times"
deepOp Divide     = mkId "Divide"
deepOp Mod        = mkId "Mod"
deepOp Not        = mkId "Not"
deepOp And        = mkId "And"
deepOp Or         = mkId "Or"
deepOp Gt         = mkId "Gt"
deepOp Lt         = mkId "Lt"
deepOp Le         = mkId "Le"
deepOp Ge         = mkId "Ge"
deepOp Eq         = mkId "Eq"
deepOp NEq        = mkId "NEq"
deepOp BitAnd     = mkId "BitAnd"
deepOp BitOr      = mkId "BitOr"
deepOp BitXor     = mkId "BitXor"
deepOp LShift     = mkId "LShift"
deepOp RShift     = mkId "RShift"
deepOp Complement = mkId "Complement"

deepExpr :: TypedExpr t v a -> MLTerm
deepExpr (TE _ (Variable (v, _))) = mkApp (mkId "Var") (mkInt $ Vec.finInt v)
deepExpr (TE _ (Fun n ts _)     ) = mkApp (mkId "Fun") $ mkRecord [ ("name", mkId $ unCoreFunName n)
                                                                  , ("tyargs", mkList (map deepType ts))
                                                                  ]
deepExpr (TE _ (Op op es)       ) = mkApp (mkId "Prim") $ mkRecord [ ("oper", deepOp op)
                                                                   , ("exprs", mkList (map deepExpr es))
                                                                   ]
deepExpr (TE _ (App e1 e2)      ) = mkApp (mkId "App") $ mkPair (deepExpr e1) (deepExpr e2)
deepExpr (TE _ (Con n e (TSum ts))) =
  mkApp (mkId "Con") $ mkRecord [ ("altnm", mkString n)
                                , ("vval", deepExpr e)
                                , ("vtys", mkList $ map (\(n,(t,tk)) -> mkTriple (mkString n) (deepType t) (deepTakenV tk)) ts )
                                ]
deepExpr (TE _ (Unit)          ) = mkId "Unit"
deepExpr (TE _ (ILit i U8 )    ) = mkApp (mkId "Lit") (mkApp (mkId "LU8" ) (mkInteger i))
deepExpr (TE _ (ILit i U16)    ) = mkApp (mkId "Lit") (mkApp (mkId "LU16") (mkInteger i))
deepExpr (TE _ (ILit i U32)    ) = mkApp (mkId "Lit") (mkApp (mkId "LU32") (mkInteger i))
deepExpr (TE _ (ILit i U64)    ) = mkApp (mkId "Lit") (mkApp (mkId "LU64") (mkInteger i))
-- FIXME: these booleans are not technically the cogent semantics
deepExpr (TE _ (ILit i Boolean)) = mkApp (mkId "Lit") (mkApp (mkId "LBool") $ mkBool (if i == 0 then False else True))
deepExpr (TE _ (SLit s)        ) = mkApp (mkId "Lit") (mkApp (mkId "SLit") $ mkString s)
deepExpr (TE _ (Let _ ea ek)   ) = mkApp (mkId "Let") $ mkRecord [ ("ev", deepExpr ea)
                                                                 , ("ek", deepExpr ek)
                                                                 ]
deepExpr (TE _ (LetBang bs _ ea ek)) = mkApp (mkId "LetBang") $ mkRecord [ ("idxs", mkList $ map (mkInt . Vec.finInt . fst) bs)
                                                                         , ("ev", deepExpr ea)
                                                                         , ("ek", deepExpr ek)
                                                                         ]
deepExpr (TE _ (Tuple e1 e2)    ) = mkApp (mkId "Tuple") $ mkPair (deepExpr e1) (deepExpr e2)
deepExpr (TE _ (Struct fs)      ) = mkApp (mkId "Struct") $
                                      mkPair
                                        (mkList $ map (deepType . exprType . snd) fs)
                                        (mkList $ map (deepExpr . snd) fs)
deepExpr (TE _ (If ec ektt ekff)) = mkApp (mkId "If") $ mkRecord [ ("econd", deepExpr ec)
                                                                 , ("ektt", deepExpr ektt)
                                                                 , ("ekff", deepExpr ekff)
                                                                 ]
deepExpr (TE _ (Case ev n (_,_,ekm) (_,_,eknm))) = mkApp (mkId "Case") $ mkRecord [ ("eval", deepExpr ev)
                                                                                  , ("altnm", mkString n)
                                                                                  , ("ematch", deepExpr ekm)
                                                                                  , ("enomatch", deepExpr eknm)
                                                                                  ]
deepExpr (TE _ (Esac e)            ) = mkApp (mkId "Esac") $ deepExpr e
deepExpr (TE _ (Split (_,_) e1 e2) ) = mkApp (mkId "Split") $ mkRecord [ ("ep", deepExpr e1)
                                                                       , ("ek", deepExpr e2)
                                                                       ]
deepExpr (TE _ (Member e i)        ) = mkApp (mkId "Member") $ mkRecord [ ("er", deepExpr e)
                                                                        , ("idx", mkInt i)
                                                                        ]
deepExpr (TE _ (Take (_,_) ev i ek)) = mkApp (mkId "Take") $ mkRecord [ ("erec", deepExpr ev)
                                                                      , ("idx", mkInt i)
                                                                      , ("ek", deepExpr ek)
                                                                      ]
deepExpr (TE _ (Put er i ev)) = mkApp (mkId "Put") $ mkRecord [ ("er", deepExpr er)
                                                              , ("idx", mkInt i)
                                                              , ("ev", deepExpr ev)
                                                              ]
deepExpr (TE _ (Promote t e)) = mkApp (mkId "Promote") $ mkPair (deepType t) (deepExpr e)
deepExpr (TE _ (Cast t e)   ) = mkApp (mkId "Cast") $ mkPair (deepType t) (deepExpr e)
