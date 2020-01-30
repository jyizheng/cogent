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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver.Simplify where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Dargent.Surface
import           Cogent.Dargent.TypeCheck
import           Cogent.Dargent.Util
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.LRow as LRow
import qualified Cogent.TypeCheck.Row as Row
import           Cogent.TypeCheck.Row (Entry)
#ifdef BUILTIN_ARRAYS
import           Cogent.TypeCheck.Solver.SMT (smtSat)
#endif
import           Cogent.TypeCheck.Solver.Goal
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import           Cogent.Surface
import           Cogent.Util (hoistMaybe)

import           Control.Applicative
import           Control.Monad
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Class (lift)
import qualified Data.Foldable as F (any)
import qualified Data.IntMap as IM (null)
import qualified Data.Map as M
import           Data.Maybe
import           Data.List as L (elemIndex, null)
import qualified Data.Set as S
import           Data.Word (Word32)
import           Lens.Micro

import           Debug.Trace

type TCSigil = Either (Sigil (Maybe TCDataLayout)) Int  -- local synonym

onGoal :: (Monad m) => (Constraint -> MaybeT m [Constraint]) -> Goal -> MaybeT m [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

unsat :: (Monad m) => TypeError -> MaybeT m [Constraint]
unsat x = hoistMaybe $ Just [Unsat x]

elseDie :: (Monad m) => Bool -> TypeError -> MaybeT m [Constraint]
elseDie b e = (hoistMaybe $ guard b >> Just []) <|> unsat e

liftTcSolvM :: Rewrite.RewriteT IO a -> Rewrite.RewriteT TcSolvM a
liftTcSolvM (Rewrite.RewriteT m) = Rewrite.RewriteT (\a -> MaybeT $ liftIO $ runMaybeT (m a))

simplify :: [(TyVarName, Kind)] -> [(DLVarName, TCType)] -> Rewrite.RewriteT IO [Goal]
simplify ks ts = Rewrite.pickOne' $ onGoal $ \case
  Sat      -> hoistMaybe $ Just []
  c1 :& c2 -> hoistMaybe $ Just [c1,c2]

  Drop   t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
        canDiscard k `elseDie` TypeNotDiscardable t m
  Share  t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
        canShare k   `elseDie` TypeNotShareable t m
  Escape t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
        canEscape k  `elseDie` TypeNotEscapable t m

  Drop     (T (TVar v b u)) m | b || u -> hoistMaybe $ Just []
  Share    (T (TVar v b u)) m | b || u -> hoistMaybe $ Just []
  Escape t@(T (TVar v True False)) m -> unsat (TypeNotEscapable t m)

  Drop   t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotDiscardable t m
  Share  t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotShareable t m
  Escape t@(T (TCon n ts s)) m ->
    not (readonly s) `elseDie` TypeNotEscapable t m

  Drop   (T (TFun {})) _ -> hoistMaybe $ Just []
  Share  (T (TFun {})) _ -> hoistMaybe $ Just []
  Escape (T (TFun {})) _ -> hoistMaybe $ Just []

  Drop   (T TUnit) _ -> hoistMaybe $ Just []
  Share  (T TUnit) _ -> hoistMaybe $ Just []
  Escape (T TUnit) _ -> hoistMaybe $ Just []

  Drop   (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Drop   m) xs)
  Share  (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Share  m) xs)
  Escape (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Escape m) xs)

  Share  (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Escape m) (Row.untakenTypes r))

  Share  (R _ r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> hoistMaybe $ Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (R _ r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> hoistMaybe $ Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (R _ r (Left s)) m
    | isNothing (Row.var r)
    , not (readonly s) -> hoistMaybe $ Just (map (flip Escape m) (Row.untakenTypes r))

#ifdef BUILTIN_ARRAYS
  Share  (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Share  t m]  -- TODO: deal with the taken fields!!! / zilinc
  Drop   (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Drop   t m]  -- TODO
  Escape (A t _ (Left s) _) m | not (readonly s) -> hoistMaybe $ Just [Escape t m]  -- TODO
#endif

  Exhaustive t ps | any isIrrefutable ps -> hoistMaybe $ Just []
  Exhaustive (V r) []
    | isNothing (Row.var r) ->
      L.null (Row.untakenTypes r)
        `elseDie` PatternsNotExhaustive (V r) (Row.untakenLabels r)
  Exhaustive (V r) (RP (PCon t _):ps)
    | isNothing (Row.var r) ->
      hoistMaybe $ Just [Exhaustive (V (Row.take t r)) ps]

  Exhaustive tau@(T (TCon "Bool" [] Unboxed)) [RP (PBoolLit t), RP (PBoolLit f)]
    -> (not (t && f) && (t || f)) `elseDie` PatternsNotExhaustive tau []

  Upcastable (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
    | Just n' <- elemIndex n primTypeCons
    , Just m' <- elemIndex m primTypeCons
    , n' <= m' , not (m `elem` ["String","Bool"]) -> hoistMaybe $ Just []

  -- Dropping for recPars
  -- TODO: Share? Escape?
  Drop (T (TRPar _ True _)) m -> Just []

  -- [amos] New simplify rule:
  -- If both sides of an equality constraint are equal, we can't completely discharge it;
  -- we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u -> hoistMaybe $ if isSolved t then Just [] else Just [Solved t]

  Solved t | isSolved t -> hoistMaybe $ Just []

  IsPrimType (T (TCon x _ Unboxed)) | x `elem` primTypeCons -> hoistMaybe $ Just []

  TLVar n        :~ tau | Just t <- lookup n ts
                        -> hoistMaybe $ Just [tau :~~ t]
  TLRepRef _ _   :~ _ -> hoistMaybe Nothing
  TLRecord fs    :~ R _ (Left (Boxed _ (Just l))) -> hoistMaybe $ Just [l :~< TLRecord fs]
  TLRecord fs    :~ R r (Left (Boxed _ Nothing))
    | ls <- LRow.entries $ LRow.fromList $ (\(a,b,c) -> (a,c,())) <$> fs
    , rs <- Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\((_,e,_),(_,(t,_))) -> e :~ toBoxedType t) <$> M.elems cs
  TLRecord _     :~ R _ (Right _) -> __todo "TLRecord fs :~ R r1 (Right n) => is this possible?"
  TLVariant _ fs :~ V r
    | ls <- LRow.entries $ LRow.fromList $ (\(a,b,c,d) -> (a,d,c)) <$> fs
    , rs <- Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\((_,e,_),(_,(t,_))) -> e :~ toBoxedType t) <$> M.elems cs
#ifdef BUILTIN_ARRAYS
  TLArray e _    :~ A _ _ (Left (Boxed _ (Just l))) _ -> hoistMaybe $ Just [l :~< e]
  TLArray e _    :~ A t _ (Left (Boxed _ Nothing)) _ -> hoistMaybe $ Just [e :~ t]
  TLArray e _    :~ A _ _ (Right _) _ -> __todo "TLArray e p :~ A t l (Right n) h => is this possible?"
#endif
  TLOffset e _   :~ tau -> hoistMaybe $ Just [e :~ tau]
  TLPrim n       :~ tau
    | isPrimType tau
    , primTypeSize tau <= evalSize n
    -> hoistMaybe $ Just []
    | isBoxedType tau
    , evalSize n == pointerSizeBits
    -> hoistMaybe $ Just []
  TLPtr          :~ tau
    | isBoxedType tau -> hoistMaybe $ Just []
  l              :~ T (TBang tau)    -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TTake _ tau)  -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TPut  _ tau)  -> hoistMaybe $ Just [l :~ tau]
#ifdef BUILTIN_ARRAYS
  l              :~ T (TATake _ tau) -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TAPut  _ tau) -> hoistMaybe $ Just [l :~ tau]
#endif
  _              :~ Synonym _ _      -> hoistMaybe Nothing
  l              :~ tau | TLU _ <- l -> hoistMaybe Nothing
                        | otherwise  -> unsat $ LayoutDoesNotMatchType l tau

  TLRepRef _ _     :~< TLRepRef _ _  -> hoistMaybe Nothing
  TLRepRef _ _     :~< _             -> hoistMaybe Nothing
  _                :~< TLRepRef _ _  -> hoistMaybe Nothing
  TLVar v1         :~< TLVar v2      | v1 == v2 -> hoistMaybe $ Just []
  TLPrim n1        :~< TLPrim n2     | n1 <= n2 -> hoistMaybe $ Just []
  TLOffset e1 _    :~< TLOffset e2 _ -> hoistMaybe $ Just [e1 :~< e2]
  TLRecord fs1     :~< TLRecord fs2
    | r1 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs2
    , r1 `LRow.isSubRow` r2
    -> hoistMaybe $ Just $ (\((_,l1,_),(_,l2,_)) -> l1 :~< l2) <$> LRow.common r1 r2
  TLVariant e1 fs1 :~< TLVariant e2 fs2
    | r1 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs2
    , r1 `LRow.isSubRow` r2
    -> hoistMaybe $ Just $ ((\((_,l1,_),(_,l2,_)) -> l1 :~< l2) <$> LRow.common r1 r2) <> [e1 :~< e2]
#ifdef BUILTIN_ARRAYS
  TLArray e1 _     :~< TLArray e2 _ -> hoistMaybe $ Just [e1 :~< e2]
#endif
  l1               :~< l2 | TLU _ <- l1 -> hoistMaybe Nothing
                          | TLU _ <- l2 -> hoistMaybe Nothing
                          | otherwise   -> do
    traceM ("l1: " ++ show l1 ++ "\nl2: " ++ show l2 ++ "\n")
    unsat $ LayoutsNotCompatible l1 l2

  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []
  Synonym _ _     :~~ _               -> hoistMaybe Nothing
  _               :~~ Synonym _ _     -> hoistMaybe Nothing

  R r1 s1 :~~ R r2 s2 | Row.null r1, (Just c) <- doSigilMatch (rmF s1) (rmF s2) -> hoistMaybe $ Just c
                      | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [R r1' s1 :~~ R r2' s2]
                      | otherwise -> do
    let commons  = Row.common r1 r2
    guard (not (L.null commons))
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :~~ fst e') commons
        c  = R r1' s1 :~~ R r2' s2
    hoistMaybe $ Just (c:cs)
  V r1 :~~ V r2 | Row.null r1 -> hoistMaybe $ Just []
                | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [V r1' :~~ V r2']
                | otherwise -> do
    let commons = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    let (r1', r2') = Row.withoutCommon r1 r2
        cs = map (\((_,e), (_,e')) -> fst e :~~ fst e') commons
        c = V r1' :~~ V r2'
    hoistMaybe $ Just (c:cs)
#ifdef BUILTIN_ARRAYS
  A t1 _ s1 _ :~~ A t2 _ s2 _ | (Just c) <- doSigilMatch (rmF s1) (rmF s2)
                              -> hoistMaybe $ Just ((t1 :~~ t2):c)
                              | otherwise -> hoistMaybe Nothing
#endif
  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []
  t1 :~~ t2 | t1 == t2 -> hoistMaybe $ Just []
            | isPrimType t1 && isPrimType t2
            , primTypeSize t1 <= primTypeSize t2
            -> hoistMaybe $ Just []
            | otherwise -> unsat $ TypesNotFit t1 t2

  T (TLayout l1 t1) :=: T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~< l2, t1 :=: t2, l1 :~ t1, l2 :~ t2]
  T (TLayout l1 t1) :<  T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~< l2, t1 :<  t2, l1 :~ t1, l2 :~ t2]

  T (TFun t1 t2) :=: T (TFun r1 r2) -> hoistMaybe $ Just [r1 :=: t1, t2 :=: r2]
  T (TFun t1 t2) :<  T (TFun r1 r2) -> hoistMaybe $ Just [r1 :<  t1, t2 :<  r2]

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:=:) ts us)

  V r1 :< V r2 | Row.null r1 && Row.null r2 -> hoistMaybe $ Just []
               | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [V r1' :=: V r2']
               | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet ls `S.isSubsetOf` untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        c   = V r1' :< V r2'
    hoistMaybe $ Just (c:cs)

  V r1 :=: V r2 | Row.null r1 && Row.null r2 -> hoistMaybe $ Just []
                | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet ls == untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
        c   = V r1' :=: V r2'
    hoistMaybe $ Just (c:cs)

  R rp1 r1 s1 :< R rp2 r2 s2
    | Row.null r1 && Row.null r2, (Just c) <- doSigilMatch s1 s2, sameRecursive rp1 rp2 -> hoistMaybe $ Just c
    | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [R r1' s1 :=: R r2' s2]
    | otherwise -> do
      let commons  = Row.common r1 r2
          (ls, rs) = unzip commons
      guard (not (L.null commons))
      guard (untakenLabelsSet rs `S.isSubsetOf` untakenLabelsSet ls)
      let (r1',r2') = Row.withoutCommon r1 r2
          cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
          ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
          c  = R rp1 r1' s1 :< R rp2 r2' s2
      hoistMaybe $ Just (c:cs ++ ds)

  R rp1 r1 s1 :=: R rp2 r2 s2
    | Row.null r1 && Row.null r2, (Just c) <- doSigilMatch s1 s2, sameRecursive rp1 rp2 -> hoistMaybe $ Just c
    | otherwise -> do
      let commons  = Row.common r1 r2
          (ls, rs) = unzip commons
      guard (not (L.null commons))
      guard (untakenLabelsSet rs == untakenLabelsSet ls)
      let (r1',r2') = Row.withoutCommon r1 r2
          cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
          ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
          c  = R rp1 r1' s1 :=: R rp2 r2' s2
      hoistMaybe $ Just (c:cs ++ ds)

#ifdef BUILTIN_ARRAYS
  -- See [NOTE: solving 'A' types] in Cogent.Solver.Unify
  A t1 l1 s1 (Left r1) :<  A t2 l2 s2 (Left r2) | (Just c) <- doSigilMatch s1 s2 -> do
    guard (not $ isJust r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Nothing, Just i2) -> Drop t1 ImplicitlyTaken
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :< t2, drop] <> c)

  A t1 l1 s1 (Left r1) :=: A t2 l2 s2 (Left r2) | (Just c) <- doSigilMatch s1 s2 -> do
    guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :=: t2, drop] <> c)

  a :-> b -> __fixme $ hoistMaybe $ Just [b]  -- FIXME: cuerently we ignore the impls. / zilinc
  
  -- Recursive types
  RPar v1 m1 :<  RPar v2 m2 -> guard (m1 M.! v1 == m2 M.! v2) >> hoistMaybe $ Just []
  RPar v1 m1 :=: RPar v2 m2 -> guard (m1 M.! v1 == m2 M.! v2) >> hoistMaybe $ Just []

  RPar v m :< x  -> hoistMaybe $ Just [unroll v m :< x]
  x :< RPar v m  -> hoistMaybe $ Just [x :< unroll v m]
  x :=: RPar v m -> hoistMaybe $ Just [x :=: unroll v m]
  RPar v m :=: x -> hoistMaybe $ Just [unroll v m :=: x]

  -- TODO: Remaining cases

  UnboxedNotRecursive (R None _ (Left Unboxed))     -> hoistMaybe $ Just []
  UnboxedNotRecursive (R _ _    (Left (Boxed _ _))) -> hoistMaybe $ Just []

  -- TODO: Here we will call a SMT procedure to simplify all the Arith constraints.
  -- The only things left will be non-trivial predicates. / zilinc
  Arith e | isTrivialSE e -> do
              r <- lift $ smtSat e
              if r then hoistMaybe $ Just []
                   else hoistMaybe $ Nothing
          | otherwise -> hoistMaybe $ Nothing
#endif

  T t1 :< x | unorderedType t1 -> hoistMaybe $ Just [T t1 :=: x]
  x :< T t2 | unorderedType t2 -> hoistMaybe $ Just [x :=: T t2]

  T (TCon n ts s) :=: T (TCon n' us s')
    | s == s', n == n' -> hoistMaybe $ Just (zipWith (:=:) ts us)

  -- Recursive types

  T (TRPar v1 b1 (Just m1)) :<  T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :< ifBang b2 (m2 M.! v2) ]
  T (TRPar v1 b1 (Just m1)) :=: T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :=: ifBang b2 (m2 M.! v2) ]

  T (TRPar v1 b1 Nothing) :<  T (TRPar v2 b2 Nothing) | b1 == b2 -> hoistMaybe $ Just []
  T (TRPar v1 b1 Nothing) :=: T (TRPar v2 b2 Nothing) | b1 == b2 -> hoistMaybe $ Just []

  T (TRPar v b m) :< x  -> hoistMaybe $ Just [unroll v b m :< x]
  x :< T (TRPar v b m)  -> hoistMaybe $ Just [x :< unroll v b m]
  x :=: T (TRPar v b m) -> hoistMaybe $ Just [x :=: unroll v b m]
  T (TRPar v b m) :=: x -> hoistMaybe $ Just [unroll v b m :=: x]

  UnboxedNotRecursive (R None _ (Left Unboxed))     -> hoistMaybe $ Just []
  UnboxedNotRecursive (R _ _    (Left (Boxed _ _))) -> hoistMaybe $ Just []

  t -> hoistMaybe $ Nothing

-- | Returns 'True' iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
unorderedType :: Type e l t -> Bool
unorderedType (TCon {}) = True
unorderedType (TVar {}) = True
unorderedType (TUnit)   = True
unorderedType _ = False

untakenLabelsSet :: [Entry TCType] -> S.Set FieldName
untakenLabelsSet = S.fromList . mapMaybe (\(l, (_,t)) -> guard (either not (const False) t) >> pure l)

isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

-- | Check if the variable parts must be equal.
--   Returns true iff the two rows have the same keys, but one of the variables
--   is Nothing and the other is a Just
extractVariableEquality :: Row.Row t -> Row.Row t -> Maybe (Row.Row t, Row.Row t)
extractVariableEquality (Row.Row m1 v1) (Row.Row m2 v2)
 | (isJust v1 && isNothing v2) || (isNothing v1 && isJust v2)
 , M.null m1
 , M.null m2
 = Just (Row.Row M.empty v1, Row.Row M.empty v2)
 | otherwise
 = Nothing

isSolved :: TCType -> Bool
isSolved t = L.null (unifVars t) && L.null (unifLVarsT t)
#ifdef BUILTIN_ARRAYS
          && L.null (unknowns t)
#endif

isPrimType :: TCType -> Bool
isPrimType (T (TCon n [] Unboxed))
  | n `elem` primTypeCons = True
  | otherwise = False
isPrimType (T (TBang t)) = isPrimType t
isPrimType (T (TUnbox t)) = isPrimType t
isPrimType _ = False

isBoxedType :: TCType -> Bool
isBoxedType (R _ (Left (Boxed _ _))) = True
#ifdef BUILTIN_ARRAYS
isBoxedType (A _ _ (Left (Boxed _ _)) _) = True
#endif
isBoxedType _ = False

toBoxedType :: TCType -> TCType
toBoxedType (R r (Left Unboxed)) = R r (Left (Boxed undefined Nothing))
#ifdef BUILTIN_ARRAYS
toBoxedType (A t l (Left Unboxed) h) = A t l (Left (Boxed undefined Nothing)) h
#endif
toBoxedType (T (TUnbox t)) = toBoxedType t
toBoxedType t = t

primTypeSize :: TCType -> Size
primTypeSize (T (TCon "U8"   [] Unboxed)) = 8
primTypeSize (T (TCon "U16"  [] Unboxed)) = 16
primTypeSize (T (TCon "U32"  [] Unboxed)) = 32
primTypeSize (T (TCon "U64"  [] Unboxed)) = 64
primTypeSize (T (TCon "Bool" [] Unboxed)) = 1
primTypeSize (T (TBang t))                = primTypeSize t
primTypeSize (T (TUnbox t))               = primTypeSize t
primTypeSize _                            = __impossible "call primTypeSize on non-prim types"

rmF :: TCSigil -> TCSigil
rmF (Left (Boxed _ l)) = Left (Boxed True l)
rmF s = s

doSigilMatch :: TCSigil -> TCSigil -> Maybe [Constraint]
doSigilMatch s1 s2
  | Left (Boxed _ (Just l1)) <- s1
  , Left (Boxed _ (Just l2)) <- s2
  = Just [l1 :~< l2]
  | s1 == s2
  = Just []
  | otherwise = trace ("s1: " ++ show s1 ++ "\ns2: " ++ show s2) Nothing

