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

module Cogent.Dargent.Util where

import Cogent.Compiler
import Cogent.Common.Syntax
import Cogent.Common.Types

import Text.Parsec.Pos (SourcePos)

wordSizeBits :: Size
wordSizeBits = case architecture of
                 X86_32 -> 32
                 X86_64 -> 64
                 ARM32  -> 32

byteSizeBits :: Size
byteSizeBits = 8

architecture :: Architecture
architecture = __cogent_arch

pointerSizeBits :: Size
pointerSizeBits = wordSizeBits

primIntSizeBits :: PrimInt -> Size
primIntSizeBits U8      = 8
primIntSizeBits U16     = 16
primIntSizeBits U32     = 32
primIntSizeBits U64     = 64
primIntSizeBits Boolean = 8


-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Size -> a -> a

-- | Allows errors messages to pinpoint the exact location where the error occurred in a DataLayoutExpr/Decl
data DataLayoutPath
  = InField FieldName SourcePos DataLayoutPath
  | InTag   DataLayoutPath
  | InAlt   TagName SourcePos DataLayoutPath
#ifdef REFINEMENT_TYPES
  | InElmt  SourcePos DataLayoutPath
#endif
  | InDecl  DataLayoutName DataLayoutPath
  | PathEnd
  deriving (Eq, Show, Ord)

