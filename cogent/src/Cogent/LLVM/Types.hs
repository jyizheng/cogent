module Cogent.LLVM.Types where

import Cogent.Common.Types
import Cogent.Core as Core

import LLVM.AST
import qualified LLVM.AST as AST


-- suppose that we know the size of all the types at compile time / zshang
to_llvm_type :: Core.Type a -> AST.Type
to_llvm_type (TPrim prim_int) = case prim_int of
                                   Boolean -> AST.IntegerType 1
                                   U8 -> AST.IntegerType 8
                                   U16 -> AST.IntegerType 16
                                   U32 -> AST.IntegerType 32
                                   U64 -> AST.IntegerType 64
to_llvm_type (TFun t1 t2) = let
  t_arg = to_llvm_type t1
  t_ret = to_llvm_type t2 in
  AST.FunctionType { resultType = t_ret
                   , argumentTypes = [t_arg]
                   , isVarArg = False
                   }
to_llvm_type TUnit = AST.VoidType
to_llvm_type _ = AST.VoidType
