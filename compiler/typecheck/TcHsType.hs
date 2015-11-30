{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section[TcMonoType]{Typechecking user-specified @MonoTypes@}
-}

{-# LANGUAGE CPP, TupleSections, MultiWayIf #-}

module TcHsType (
        tcHsSigType, tcTopHsSigType, tcHsDeriv, tcHsVectInst,
        tcHsInstHead,
        UserTypeCtxt(..),

                -- Type checking type and class decls
        kcLookupKind, tcTyClTyVars,
        tcHsConArgType, tcDataKindSig,
        tcClassSigType,

                -- Kind-checking types
                -- No kind generalisation, no checkValidType
        tcWildcardBinders,
        kcHsTyVarBndrs, tcHsTyVarBndrs,
        tcHsLiftedType, tcHsOpenType,
        tcLHsType, tcCheckLHsType,
        tcHsContext, tcInferApps,
        tcInferArgs,

        kindGeneralize,

                -- Sort-checking kinds
        tcLHsKind,

                -- Pattern type signatures
        tcHsPatSigType, tcPatSig,

            -- Error messages
        funAppCtxt
   ) where

#include "HsVersions.h"

import HsSyn
import TcRnMonad
import TcEvidence
import TcEnv
import TcMType
import TcValidity
import TcUnify
import TcIface
import TcSimplify ( solveEqualities )
import TcType
import TcHsSyn
import Type
import Kind
import RdrName( lookupLocalRdrOcc )
import Var
import VarSet
import TyCon
import ConLike
import DataCon
import TysPrim ( tYPE )
import Class
import Name
import NameEnv
import NameSet
import VarEnv
import TysWiredIn
import BasicTypes
import SrcLoc
import DynFlags ( ExtensionFlag( Opt_DataKinds, Opt_MonoLocalBinds
                               , Opt_TypeInType ) )
import Constants ( mAX_CTUPLE_SIZE )
import ErrUtils( MsgDoc )
import Unique
import Util
import UniqSupply
import Outputable
import FastString
import PrelNames hiding ( wildCardName )
import Pair

import Data.Maybe
import Control.Monad

{-
        ----------------------------
                General notes
        ----------------------------

Unlike with expressions, type-checking types both does some checking and
desugars at the same time. This is necessary because we often want to perform
equality checks on the types right away, and it would be incredibly painful
to do this on un-desugared types. Luckily, desugared types are close enough
to HsTypes to make the error messages sane.

During type-checking, we perform as little validity checking as possible.
This is because some type-checking is done in a mutually-recursive knot, and
if we look too closely at the tycons, we'll loop. This is why we always must
use mkNakedTyConApp and mkNakedAppTys, etc., which never look at a tycon.
The mkNamed... functions don't uphold Type invariants, but zonkTcTypeToType
will repair this for us. Note that zonkTcType *is* safe within a knot, and
can be done repeatedly with no ill effect: it just squeezes out metavariables.

Generally, after type-checking, you will want to do validity checking, say
with TcValidity.checkValidType.

Validity checking
~~~~~~~~~~~~~~~~~
Some of the validity check could in principle be done by the kind checker,
but not all:

- During desugaring, we normalise by expanding type synonyms.  Only
  after this step can we check things like type-synonym saturation
  e.g.  type T k = k Int
        type S a = a
  Then (T S) is ok, because T is saturated; (T S) expands to (S Int);
  and then S is saturated.  This is a GHC extension.

- Similarly, also a GHC extension, we look through synonyms before complaining
  about the form of a class or instance declaration

- Ambiguity checks involve functional dependencies, and it's easier to wait
  until knots have been resolved before poking into them

Also, in a mutually recursive group of types, we can't look at the TyCon until we've
finished building the loop.  So to keep things simple, we postpone most validity
checking until step (3).

Knot tying
~~~~~~~~~~
During step (1) we might fault in a TyCon defined in another module, and it might
(via a loop) refer back to a TyCon defined in this module. So when we tie a big
knot around type declarations with ARecThing, so that the fault-in code can get
the TyCon being defined.

%************************************************************************
%*                                                                      *
              Check types AND do validity checking
*                                                                      *
************************************************************************
-}

tcHsSigType, tcTopHsSigType :: UserTypeCtxt -> LHsType Name -> TcM Type
  -- NB: it's important that the foralls that come from the top-level
  --     HsForAllTy in hs_ty occur *first* in the returned type.
  --     See Note [Scoped] with TcSigInfo
tcHsSigType ctxt (L loc hs_ty)
  = setSrcSpan loc $
    addErrCtxt (pprSigCtxt ctxt empty (ppr hs_ty)) $
    do  { kind <- case expectedKindInCtxt ctxt of
                    AnythingKind -> newMetaKindVar
                    TheKind k    -> return k
                    OpenKind     -> do { lev <- newFlexiTyVarTy levityTy
                                       ; return $ tYPE lev }
          -- The kind is checked by checkValidType, and isn't necessarily
          -- of kind * in a Template Haskell quote eg [t| Maybe |]

          -- Generalise here: see Note [Kind generalisation]
        ; ty <- tcCheckHsTypeAndMaybeGen hs_ty kind
          -- ty is already zonked

        ; checkValidType ctxt ty
        ; return ty }

-- Like 'tcHsSigType', but works only for top-level declarations that
-- never see the desugarer
tcTopHsSigType ctxt hs_ty = solveEqualities $ tcHsSigType ctxt hs_ty

-----------------
tcHsInstHead :: UserTypeCtxt -> LHsType Name -> TcM ([TyVar], ThetaType, Class, [Type])
-- Like tcHsSigType, but for an instance head.
tcHsInstHead user_ctxt lhs_ty@(L loc hs_ty)
  = setSrcSpan loc $    -- The "In the type..." context comes from the caller
    do { inst_ty <- solveEqualities $ tc_inst_head hs_ty
       ; kvs     <- kindGeneralize (tyCoVarsOfType inst_ty)
       ; inst_ty <- zonkTcTypeToType emptyZonkEnv $ mkInvForAllTys kvs inst_ty
       ; checkValidInstance user_ctxt lhs_ty inst_ty }

tc_inst_head :: HsType Name -> TcM TcType
tc_inst_head (HsForAllTy expflag _ hs_tvs hs_ctxt hs_ty)
  = do { (tvs, (ctxt, ty)) <- tcHsTyVarBndrs expflag hs_tvs $
         do { ctxt <- tcHsContext hs_ctxt
            ; ty   <- tc_lhs_type typeLevelMode hs_ty constraintKind
            ; return (ctxt, ty) }
                  -- Body for forall has kind Constraint
       ; return (mkInvSigmaTy tvs ctxt ty) }

tc_inst_head hs_ty
  = tc_hs_type typeLevelMode hs_ty constraintKind

-----------------
tcHsDeriv :: HsType Name -> TcM ([TyVar], Class, [Type], Kind)
-- Like tcHsSigType, but for the ...deriving( C t1 ty2 ) clause
-- Returns the C, [ty1, ty2, and the kind of C's *next* argument
-- E.g.    class C (a::*) (b::k->k)
--         data T a b = ... deriving( C Int )
--    returns ([k], C, [k, Int],  k->k)
-- Also checks that (C ty1 ty2 arg) :: Constraint
-- if arg has a suitable kind
tcHsDeriv hs_ty
  = do { arg_kind <- newMetaKindVar
                    -- always safe to kind-generalize, because there
                    -- can be no covars in an outer scope
       ; ty <- tcCheckHsTypeAndGen hs_ty $
               mkFunTy arg_kind constraintKind
          -- ty is already zonked
       ; arg_kind <- zonkTcTypeToType emptyZonkEnv arg_kind
       ; let (tvs, pred) = splitNamedForAllTys ty
       ; case getClassPredTys_maybe pred of
           Just (cls, tys) -> return (tvs, cls, tys, arg_kind)
           Nothing -> failWithTc (ptext (sLit "Illegal deriving item") <+> quotes (ppr hs_ty)) }

-- Used for 'VECTORISE [SCALAR] instance' declarations
--
tcHsVectInst :: LHsType Name -> TcM (Class, [Type])
tcHsVectInst ty
  | Just (L _ cls_name, tys) <- splitLHsClassTy_maybe ty
  = do { (cls, cls_kind) <- tcClass cls_name
       ; (applied_class, _res_kind)
           <- tcInferApps typeLevelMode cls_name (mkClassPred cls []) cls_kind tys
       ; case tcSplitTyConApp_maybe applied_class of
           Just (_tc, args) -> ASSERT( _tc == classTyCon cls )
                               return (cls, args)
           _ -> failWithTc (text "Too many arguments passed to" <+> ppr cls_name) }
  | otherwise
  = failWithTc $ ptext (sLit "Malformed instance type")

{-
        These functions are used during knot-tying in
        type and class declarations, when we have to
        separate kind-checking, desugaring, and validity checking


************************************************************************
*                                                                      *
            The main kind checker: no validity checks here
%*                                                                      *
%************************************************************************

        First a couple of simple wrappers for kcHsType
-}

tcClassSigType :: LHsType Name -> TcM Type
tcClassSigType lhs_ty@(L loc hs_ty)
  = addTypeCtxt lhs_ty $
    setSrcSpan loc $
    tcCheckHsTypeAndGen hs_ty liftedTypeKind

tcHsConArgType :: NewOrData ->  LHsType Name -> TcM Type
-- Permit a bang, but discard it
tcHsConArgType NewType  bty = tcHsLiftedType (getBangType bty)
  -- Newtypes can't have bangs, but we don't check that
  -- until checkValidDataCon, so do not want to crash here

tcHsConArgType DataType bty = tcHsOpenType (getBangType bty)
  -- Can't allow an unlifted type for newtypes, because we're effectively
  -- going to remove the constructor while coercing it to a lifted type.
  -- And newtypes can't be bang'd

---------------------------
tcHsOpenType, tcHsLiftedType :: LHsType Name -> TcM TcType
-- Used for type signatures
-- Do not do validity checking
tcHsOpenType ty
  = addTypeCtxt ty $
    do { ek <- ekOpen
       ; tc_lhs_type typeLevelMode ty ek }
tcHsLiftedType ty = addTypeCtxt ty $ tc_lhs_type typeLevelMode ty liftedTypeKind

-- Like tcHsType, but takes an expected kind
tcCheckLHsType :: LHsType Name -> Kind -> TcM Type
tcCheckLHsType hs_ty exp_kind
  = addTypeCtxt hs_ty $
    tc_lhs_type typeLevelMode hs_ty exp_kind

tcLHsType :: LHsType Name -> TcM (TcType, TcKind)
-- Called from outside: set the context
tcLHsType ty = addTypeCtxt ty (tc_infer_lhs_type typeLevelMode ty)

---------------------------
-- | Check an LHsType, and generalize if appropriate.
-- The result is zonked, but not checked for validity
-- May emit constraints.
tcCheckHsTypeAndMaybeGen :: HsType Name -> Kind -> TcM Type
tcCheckHsTypeAndMaybeGen hs_ty kind
  = do { should_gen <- decideKindGeneralisationPlan hs_ty
       ; check_and_gen should_gen hs_ty kind }

-- | Should we generalise the kind of this type?
-- We *should* generalise if the type is closed or if NoMonoLocalBinds
-- is set. Otherwise, nope.
decideKindGeneralisationPlan :: HsType Name -> TcM Bool
decideKindGeneralisationPlan hs_ty
  = do { mono_locals <- xoptM Opt_MonoLocalBinds
       ; let fvs = ftvHsType hs_ty
             should_gen = not mono_locals || isEmptyNameSet fvs
       ; traceTc "decideKindGeneralisationPlan"
           (vcat [ text "type:" <+> ppr hs_ty
                 , text "ftvs:" <+> ppr fvs
                 , text "should gen?" <+> ppr should_gen ])
       ; return should_gen }

tcCheckHsTypeAndGen :: HsType Name -> Kind -> TcM Type
-- Input type is HsType, not LHsType; the caller adds the context
-- Output is fully zonked, but not checked for validity
tcCheckHsTypeAndGen = check_and_gen True

check_and_gen :: Bool   -- should generalize?
              -> HsType Name
              -> Kind
              -> TcM Type
check_and_gen should_gen hs_ty kind
  = do { traceTc "tcCheckHsTypeAndGen" (ppr should_gen $$ ppr hs_ty $$ ppr kind)
       ; ty <- solveEqualities $
               tc_hs_type typeLevelMode hs_ty kind
       ; traceTc "tcCheckHsTypeAndGen" (ppr hs_ty)
       ; kvs <- if should_gen
                then kindGeneralize (tyCoVarsOfType ty)
                else return []
       ; zonkTcTypeToType emptyZonkEnv (mkInvForAllTys kvs ty) }

{-
************************************************************************
*                                                                      *
      Type-checking modes
*                                                                      *
************************************************************************

The kind-checker is parameterised by a TcTyMode, which contains some
information about where we're checking a type.

The renamer issues errors about what it can. All errors issued here must
concern things that the renamer can't handle.

-}

data TcTyMode
  = TcTyMode { mode_level :: TypeOrKind  -- True <=> type, False <=> kind
                                         -- used only for -XNoTypeInType errors
             }

typeLevelMode :: TcTyMode
typeLevelMode = TcTyMode { mode_level = TypeLevel }

kindLevelMode :: TcTyMode
kindLevelMode = TcTyMode { mode_level = KindLevel }

-- switch to kind level
kindLevel :: TcTyMode -> TcTyMode
kindLevel mode = mode { mode_level = KindLevel }

{-
Note [Bidirectional type checking]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In expressions, whenever we see a polymorphic identifier, say `id`, we are
free to instantiate it with metavariables, knowing that we can always
re-generalize with type-lambdas when necessary. For example:

  rank2 :: (forall a. a -> a) -> ()
  x = rank2 id

When checking the body of `x`, we can instantiate `id` with a metavariable.
Then, when we're checking the application of `rank2`, we notice that we really
need a polymorphic `id`, and then re-generalize over the unconstrained
metavariable.

In types, however, we're not so lucky, because *we cannot re-generalize*!
There is no lambda. So, we must be careful only to instantiate at the last
possible moment, when we're sure we're never going to want the lost polymorphism
again. This is done in calls to tcInstBinders and tcInstBindersX.

To implement this behavior, we use bidirectional type checking, where we
explicitly think about whether we know the kind of the type we're checking
or not. Note that there is a difference between not knowing a kind and
knowing a metavariable kind: the metavariables are TauTvs, and cannot become
forall-quantified kinds. Previously (before dependent types), there were
no higher-rank kinds, and so we could instantiate early and be sure that
no types would have polymorphic kinds, and so we could always assume that
the kind of a type was a fresh metavariable. Not so anymore, thus the
need for two algorithms.

For HsType forms that can never be kind-polymorphic, we implement only the
"down" direction, where we safely assume a metavariable kind. For HsType forms
that *can* be kind-polymorphic, we implement just the "up" (functions with
"infer" in their name) version, as we gain nothing by also implementing the
"down" version.

Note [Future-proofing the type checker]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As discussed in Note [Bidirectional type checking], each HsType form is
handled in *either* tc_infer_hs_type *or* tc_hs_type. These functions
are mutually recursive, so that either one can work for any type former.
But, we want to make sure that our pattern-matches are complete. So,
we have a bunch of repetitive code just so that we get warnings if we're
missing any patterns.
-}

-- | Check and desugar a type, returning the core type and its
-- possibly-polymorphic kind. Much like 'tcInferRho' at the expression
-- level.
tc_infer_lhs_type :: TcTyMode -> LHsType Name -> TcM (TcType, TcKind)
tc_infer_lhs_type mode (L span ty)
  = setSrcSpan span $
    do { traceTc "tc_infer_lhs_type:" (ppr ty)
       ; tc_infer_hs_type mode ty }

-- | Infer the kind of a type and desugar. This is the "up" type-checker,
-- as described in Note [Bidirectional type checking]
tc_infer_hs_type :: TcTyMode -> HsType Name -> TcM (TcType, TcKind)
tc_infer_hs_type mode (HsTyVar tv)    = tcTyVar mode tv
tc_infer_hs_type mode (HsAppTy ty1 ty2)
  = do { let (fun_ty, arg_tys) = splitHsAppTys ty1 [ty2]
       ; (fun_ty', fun_kind) <- tc_infer_lhs_type mode fun_ty
       ; fun_kind' <- zonkTcType fun_kind
       ; tcInferApps mode fun_ty fun_ty' fun_kind' arg_tys }
tc_infer_hs_type mode (HsParTy t)     = tc_infer_lhs_type mode t
tc_infer_hs_type mode (HsOpTy lhs (L _ op) rhs)
  | not (op `hasKey` funTyConKey)
  = do { (op', op_kind) <- tcTyVar mode op
       ; op_kind' <- zonkTcType op_kind
       ; tcInferApps mode op op' op_kind' [lhs, rhs] }
tc_infer_hs_type mode (HsKindSig ty sig)
  = do { sig' <- tc_lhs_kind (kindLevel mode) sig
       ; ty' <- tc_lhs_type mode ty sig'
       ; return (ty', sig') }
tc_infer_hs_type mode (HsDocTy ty _) = tc_infer_lhs_type mode ty
tc_infer_hs_type _    (HsCoreTy ty)  = return (ty, typeKind ty)
tc_infer_hs_type mode other_ty
  = do { kv <- newMetaKindVar
       ; ty' <- tc_hs_type mode other_ty kv
       ; return (ty', kv) }

tc_lhs_type :: TcTyMode -> LHsType Name -> TcKind -> TcM TcType
tc_lhs_type mode (L span ty) exp_kind
  = setSrcSpan span $
    do { traceTc "tc_lhs_type:" (ppr ty $$ ppr exp_kind)
       ; tc_hs_type mode ty exp_kind }

------------------------------------------
tc_fun_type :: TcTyMode -> LHsType Name -> LHsType Name -> TcKind -> TcM TcType
tc_fun_type mode ty1 ty2 exp_kind
  = do { arg_lev <- newFlexiTyVarTy levityTy
       ; res_lev <- newFlexiTyVarTy levityTy
       ; ty1' <- tc_lhs_type mode ty1 (tYPE arg_lev)
       ; ty2' <- tc_lhs_type mode ty2 (tYPE res_lev)
       ; checkExpectedKind (mkNakedFunTy ty1' ty2') liftedTypeKind exp_kind }

------------------------------------------
-- See also Note [Bidirectional type checking]
tc_hs_type :: TcTyMode -> HsType Name -> TcKind -> TcM TcType
tc_hs_type mode (HsParTy ty)   exp_kind = tc_lhs_type mode ty exp_kind
tc_hs_type mode (HsDocTy ty _) exp_kind = tc_lhs_type mode ty exp_kind
tc_hs_type _ ty@(HsBangTy {}) _
    -- While top-level bangs at this point are eliminated (eg !(Maybe Int)),
    -- other kinds of bangs are not (eg ((!Maybe) Int)). These kinds of
    -- bangs are invalid, so fail. (#7210)
    = failWithTc (ptext (sLit "Unexpected strictness annotation:") <+> ppr ty)
tc_hs_type _ (HsRecTy _) _ = panic "tc_hs_type: record" -- Unwrapped by con decls
      -- Record types (which only show up temporarily in constructor
      -- signatures) should have been removed by now

-- This should never happen; type splices are expanded by the renamer
tc_hs_type _ ty@(HsSpliceTy {}) _exp_kind
  = failWithTc (ptext (sLit "Unexpected type splice:") <+> ppr ty)

---------- Functions and applications
tc_hs_type mode (HsFunTy ty1 ty2) exp_kind
  = tc_fun_type mode ty1 ty2 exp_kind

tc_hs_type mode (HsOpTy ty1 (L _ op) ty2) exp_kind
  | op `hasKey` funTyConKey
  = tc_fun_type mode ty1 ty2 exp_kind

--------- Foralls
tc_hs_type mode hs_ty@(HsForAllTy expflag _ hs_tvs context ty) exp_kind
    -- Do not kind-generalise here!  See Note [Kind generalisation]

  | isConstraintKind exp_kind
  = failWithTc (hang (ptext (sLit "Illegal constraint:")) 2 (ppr hs_ty))

  | null (unLoc context)
  = do { (tvs', ty') <- tcHsTyVarBndrs expflag hs_tvs $
                        tc_lhs_type mode ty exp_kind
                          -- Why exp_kind?  See Note [Body kind of forall]
       ; return (mkNakedInvSigmaTy tvs' [] ty') }

  | otherwise
           -- If there is a context, then this forall is really a
           -- _function_, so the kind of the result really is *
           -- The body kind (result of the function) can be * or #, hence ekOpen
  = do { (tvs', (ctxt', ty')) <- tcHsTyVarBndrs expflag hs_tvs $
         do { ctxt' <- tc_hs_context mode context
            ; ek  <- ekOpen
            ; ty' <- tc_lhs_type mode ty ek
            ; return (ctxt', ty') }

       ; checkExpectedKind (mkNakedInvSigmaTy tvs' ctxt' ty')
                           liftedTypeKind exp_kind }

--------- Lists, arrays, and tuples
tc_hs_type mode (HsListTy elt_ty) exp_kind
  = do { tau_ty <- tc_lhs_type mode elt_ty liftedTypeKind
       ; checkWiredInTyCon listTyCon
       ; checkExpectedKind (mkListTy tau_ty) liftedTypeKind exp_kind }

tc_hs_type mode (HsPArrTy elt_ty) exp_kind
  = do { MASSERT( isTypeLevel (mode_level mode) )
       ; tau_ty <- tc_lhs_type mode elt_ty liftedTypeKind
       ; checkWiredInTyCon parrTyCon
       ; checkExpectedKind (mkPArrTy tau_ty) liftedTypeKind exp_kind }

-- See Note [Distinguishing tuple kinds] in HsTypes
-- See Note [Inferring tuple kinds]
tc_hs_type mode (HsTupleTy HsBoxedOrConstraintTuple hs_tys) exp_kind
     -- (NB: not zonking before looking at exp_k, to avoid left-right bias)
  | Just tup_sort <- tupKindSort_maybe exp_kind
  = traceTc "tc_hs_type tuple" (ppr hs_tys) >>
    tc_tuple mode tup_sort hs_tys exp_kind
  | otherwise
  = do { traceTc "tc_hs_type tuple 2" (ppr hs_tys)
       ; (tys, kinds) <- mapAndUnzipM (tc_infer_lhs_type mode) hs_tys
       ; kinds <- mapM zonkTcType kinds
           -- Infer each arg type separately, because errors can be
           -- confusing if we give them a shared kind.  Eg Trac #7410
           -- (Either Int, Int), we do not want to get an error saying
           -- "the second argument of a tuple should have kind *->*"

       ; let (arg_kind, tup_sort)
               = case [ (k,s) | k <- kinds
                              , Just s <- [tupKindSort_maybe k] ] of
                    ((k,s) : _) -> (k,s)
                    [] -> (liftedTypeKind, BoxedTuple)
         -- In the [] case, it's not clear what the kind is, so guess *

       ; tys' <- sequence [ setSrcSpan loc $
                            checkExpectedKind ty kind arg_kind
                          | ((L loc _),ty,kind) <- zip3 hs_tys tys kinds ]

       ; finish_tuple tup_sort tys' (map (const arg_kind) tys') exp_kind }


tc_hs_type mode (HsTupleTy hs_tup_sort tys) exp_kind
  = tc_tuple mode tup_sort tys exp_kind
  where
    tup_sort = case hs_tup_sort of  -- Fourth case dealt with above
                  HsUnboxedTuple    -> UnboxedTuple
                  HsBoxedTuple      -> BoxedTuple
                  HsConstraintTuple -> ConstraintTuple
                  _                 -> panic "tc_hs_type HsTupleTy"


--------- Promoted lists and tuples
tc_hs_type mode (HsExplicitListTy _k tys) exp_kind
  = do { tks <- mapM (tc_infer_lhs_type mode) tys
       ; (taus', kind) <- unifyKinds tks
       ; let ty = (foldr (mk_cons kind) (mk_nil kind) taus')
       ; checkExpectedKind ty (mkListTy kind) exp_kind }
  where
    mk_cons k a b = mkTyConApp (promoteDataCon consDataCon) [k, a, b]
    mk_nil  k     = mkTyConApp (promoteDataCon nilDataCon) [k]

tc_hs_type mode (HsExplicitTupleTy _ tys) exp_kind
  = do { tks <- mapM (tc_infer_lhs_type mode) tys
       ; let n          = length tys
             kind_con   = tupleTyCon           Boxed n
             ty_con     = promotedTupleDataCon Boxed n
             (taus, ks) = unzip tks
             tup_k      = mkTyConApp kind_con ks
       ; checkExpectedKind (mkTyConApp ty_con (ks ++ taus)) tup_k exp_kind }

--------- Constraint types
tc_hs_type mode (HsIParamTy n ty) exp_kind
  = do { MASSERT( isTypeLevel (mode_level mode) )
       ; ty' <- tc_lhs_type mode ty liftedTypeKind
       ; let n' = mkStrLitTy $ hsIPNameFS n
       ; checkExpectedKind (mkClassPred ipClass [n',ty'])
           constraintKind exp_kind }

tc_hs_type mode (HsEqTy ty1 ty2) exp_kind
  = do { (ty1', kind1) <- tc_infer_lhs_type mode ty1
       ; (ty2', kind2) <- tc_infer_lhs_type mode ty2
       ; ty2'' <- checkExpectedKind ty2' kind2 kind1
       ; eq_tc <- tcLookupTyCon eqTyConName
       ; let ty' = mkNakedTyConApp eq_tc [kind1, ty1', ty2'']
       ; checkExpectedKind ty' constraintKind exp_kind }

--------- Literals
tc_hs_type _ (HsTyLit (HsNumTy _ n)) exp_kind
  = do { checkWiredInTyCon typeNatKindCon
       ; checkExpectedKind (mkNumLitTy n) typeNatKind exp_kind }

tc_hs_type _ (HsTyLit (HsStrTy _ s)) exp_kind
  = do { checkWiredInTyCon typeSymbolKindCon
       ; checkExpectedKind (mkStrLitTy s) typeSymbolKind exp_kind }

--------- Potentially kind-polymorphic types: call the "up" checker
-- See Note [Future-proofing the type checker]
tc_hs_type mode ty@(HsTyVar {})   ek = tc_infer_hs_type_ek mode ty ek
tc_hs_type mode ty@(HsAppTy {})   ek = tc_infer_hs_type_ek mode ty ek
tc_hs_type mode ty@(HsOpTy {})    ek = tc_infer_hs_type_ek mode ty ek
tc_hs_type mode ty@(HsKindSig {}) ek = tc_infer_hs_type_ek mode ty ek
tc_hs_type mode ty@(HsCoreTy {})  ek = tc_infer_hs_type_ek mode ty ek

tc_hs_type mode (HsWildCardTy wc) exp_kind
  = do { let name = wildCardName wc
       ; (ty, k) <- tcTyVar mode name
       ; checkExpectedKind ty k exp_kind }

-- disposed of by renamer
tc_hs_type _ ty@(HsAppsTy {}) _
  = pprPanic "tc_hs_tyep HsAppsTy" (ppr ty)

---------------------------
-- | Call 'tc_infer_hs_type' and check its result against an expected kind.
tc_infer_hs_type_ek :: TcTyMode -> HsType Name -> TcKind -> TcM TcType
tc_infer_hs_type_ek mode ty ek
  = do { (ty', k) <- tc_infer_hs_type mode ty
       ; checkExpectedKind ty' k ek }

---------------------------
tupKindSort_maybe :: TcKind -> Maybe TupleSort
tupKindSort_maybe k
  | isConstraintKind k = Just ConstraintTuple
  | isLiftedTypeKind k = Just BoxedTuple
  | otherwise          = Nothing

tc_tuple :: TcTyMode -> TupleSort -> [LHsType Name] -> TcKind -> TcM TcType
tc_tuple mode tup_sort tys exp_kind
  = do { arg_kinds <- case tup_sort of
           BoxedTuple      -> return (nOfThem arity liftedTypeKind)
           UnboxedTuple    -> do { levs <- newFlexiTyVarTys arity levityTy
                                 ; return $ map tYPE levs }
           ConstraintTuple -> return (nOfThem arity constraintKind)
       ; tau_tys <- zipWithM (tc_lhs_type mode) tys arg_kinds
       ; finish_tuple tup_sort tau_tys arg_kinds exp_kind }
  where
    arity   = length tys

finish_tuple :: TupleSort
             -> [TcType]    -- ^ argument types
             -> [TcKind]    -- ^ of these kinds
             -> TcKind      -- ^ expected kind of the whole tuple
             -> TcM TcType
finish_tuple tup_sort tau_tys tau_kinds exp_kind
  = do { traceTc "finish_tuple" (ppr res_kind $$ ppr tau_kinds $$ ppr exp_kind)
       ; let arg_tys  = case tup_sort of
                   -- See also Note [Unboxed tuple levity vars] in TyCon
                 UnboxedTuple    -> map (getLevityFromKind "finish_tuple") tau_kinds
                                    ++ tau_tys
                 BoxedTuple      -> tau_tys
                 ConstraintTuple -> tau_tys
       ; tycon <- case tup_sort of
           ConstraintTuple
             | arity > mAX_CTUPLE_SIZE
                         -> failWith (bigConstraintTuple arity)
             | otherwise -> tcLookupTyCon (cTupleTyConName arity)
           BoxedTuple    -> do { let tc = tupleTyCon Boxed arity
                               ; checkWiredInTyCon tc
                               ; return tc }
           UnboxedTuple  -> return (tupleTyCon Unboxed arity)
       ; checkExpectedKind (mkTyConApp tycon arg_tys) res_kind exp_kind }
  where
    arity = length tau_tys
    res_kind = case tup_sort of
                 UnboxedTuple    -> unliftedTypeKind
                 BoxedTuple      -> liftedTypeKind
                 ConstraintTuple -> constraintKind

bigConstraintTuple :: Arity -> MsgDoc
bigConstraintTuple arity
  = hang (ptext (sLit "Constraint tuple arity too large:") <+> int arity
          <+> parens (ptext (sLit "max arity =") <+> int mAX_CTUPLE_SIZE))
       2 (ptext (sLit "Instead, use a nested tuple"))

---------------------------
-- | Apply a type of a given kind to a list of arguments. This instantiates
-- invisible parameters as necessary. However, it does *not* necessarily
-- apply all the arguments, if the kind runs out of binders.
-- This takes an optional @VarEnv Kind@ which maps kind variables to kinds.
-- These kinds should be used to instantiate invisible kind variables;
-- they come from an enclosing class for an associated type/data family.
tcInferArgs :: Outputable fun
            => Bool                     -- ^ True => inst. all invis. args
            -> fun                      -- ^ the function
            -> TcKind                   -- ^ function kind (zonked)
            -> Maybe (VarEnv Kind)      -- ^ possibly, kind info (see above)
            -> [LHsType Name]           -- ^ args
            -> Int                      -- ^ number to start arg counter at
            -> TcM (TcKind, [TcType], [LHsType Name], Int)
               -- ^ (result kind, typechecked args, untypechecked args, n)
tcInferArgs keep_insting = tc_infer_args keep_insting typeLevelMode

-- | See comments for 'tcInferArgs'
tc_infer_args :: Outputable fun
              => Bool                     -- ^ True => inst. all invis. args
              -> TcTyMode
              -> fun                      -- ^ the function
              -> TcKind                   -- ^ function kind (zonked)
              -> Maybe (VarEnv Kind)      -- ^ possibly, kind info (see above)
              -> [LHsType Name]           -- ^ args
              -> Int                      -- ^ number to start arg counter at
              -> TcM (TcKind, [TcType], [LHsType Name], Int)
tc_infer_args keep_insting mode orig_ty ki mb_kind_info args n0
    -- TODO (RAE): move keep_insting behavior to a separate
    -- function, called from tc_fam_ty_pats.
    -- This could just be checkExpectedKind
  = do { traceTc "tcInferApps" (ppr ki $$ ppr args)
       ; go emptyTCvSubst ki args n0 [] }
  where
    go subst fun_kind []   n acc
      | not keep_insting
      = return ( substTy subst fun_kind, reverse acc, [], n )
    -- when we call this when checking type family patterns, we really
    -- do want to instantiate all invisible arguments. During other
    -- typechecking, we don't.

    go subst fun_kind (arg:args) n acc
      | Just (bndr, res_k) <- splitForAllTy_maybe fun_kind
      , isVisibleBinder bndr
      = do { let mode' | isNamedBinder bndr = kindLevel mode
                       | otherwise          = mode
           ; arg' <- addErrCtxt (funAppCtxt orig_ty arg n) $
                     tc_lhs_type mode' arg (substTy subst $ binderType bndr)
           ; let subst' = case binderVar_maybe bndr of
                   Just tv -> extendTCvSubst subst tv arg'
                   Nothing -> subst
           ; go subst' res_k args (n+1) (arg' : acc) }

    -- TODO (RAE): move tcView case to the top
    go subst fun_kind args n acc
      | Just fun_kind' <- tcView fun_kind
      = go subst fun_kind' args n acc

       -- TODO (RAE): Move up.
      | Just tv <- getTyVar_maybe fun_kind
      , Just fun_kind' <- lookupTyVar subst tv
      = go subst fun_kind' args n acc

      | (inv_bndrs, res_k) <- splitForAllTysInvisible fun_kind
      , not (null inv_bndrs)
      = do { (subst', args') <- tcInstBindersX subst mb_kind_info inv_bndrs
           ; go subst' res_k args n (reverse args' ++ acc) }

      | otherwise
      = return (substTy subst fun_kind, reverse acc, args, n)

-- | Applies a type to a list of arguments. Always consumes all the
-- arguments.
tcInferApps :: Outputable fun
             => TcTyMode
             -> fun                  -- ^ Function (for printing only)
             -> TcType               -- ^ Function (could be knot-tied)
             -> TcKind               -- ^ Function kind (zonked)
             -> [LHsType Name]       -- ^ Args
             -> TcM (TcType, TcKind) -- ^ (f args, result kind)
tcInferApps mode orig_ty ty ki args = go ty ki args 1
  where
    go fun fun_kind []   _ = return (fun, fun_kind)
    go fun fun_kind args n
      | Just fun_kind' <- tcView fun_kind
      = go fun fun_kind' args n

      | isForAllTy fun_kind
      = do { (res_kind, args', leftover_args, n')
                <- tc_infer_args False mode orig_ty fun_kind Nothing args n
           ; go (mkNakedAppTys fun args') res_kind leftover_args n' }

    go fun fun_kind all_args@(arg:args) n
      = do { (co, arg_k, res_k) <- matchExpectedFunKind (length all_args)
                                                        fun fun_kind
           ; arg' <- addErrCtxt (funAppCtxt orig_ty arg n) $
                     tc_lhs_type mode arg arg_k
           ; go (mkNakedAppTy (fun `mkNakedCastTy` co) arg')
                res_k args (n+1) }

---------------------------
-- | This is used to instantiate binders when type-checking *types* only.
-- Precondition: all binders are invisible. See also Note [Bidirectional type checking]
tcInstBinders :: [Binder] -> TcM (TCvSubst, [TcType])
tcInstBinders = tcInstBindersX emptyTCvSubst Nothing

-- | This is used to instantiate binders when type-checking *types* only.
-- Precondition: all binders are invisible.
-- The @VarEnv Kind@ gives some known instantiations.
-- See also Note [Bidirectional type checking]
tcInstBindersX :: TCvSubst -> Maybe (VarEnv Kind)
               -> [Binder] -> TcM (TCvSubst, [TcType])
tcInstBindersX subst mb_kind_info bndrs
  = do { (subst, args) <- mapAccumLM (tcInstBinderX mb_kind_info) subst bndrs
       ; traceTc "instantiating implicit dependent vars:"
           (vcat $ zipWith (\bndr arg -> ppr bndr <+> text ":=" <+> ppr arg)
                           bndrs args)
       ; return (subst, args) }

-- | Used only in *types*
tcInstBinderX :: Maybe (VarEnv Kind)
              -> TCvSubst -> Binder -> TcM (TCvSubst, TcType)
tcInstBinderX mb_kind_info subst binder
  | Just tv <- binderVar_maybe binder
  = case lookup_tv tv of
      Just ki -> return (extendTCvSubst subst tv ki, ki)
      Nothing -> do { (subst', tv') <- tcInstTyVarX subst tv
                    ; return (subst', mkTyVarTy tv') }

     -- This is the *only* constraint currently handled in types.
  | let ty = substTy subst (binderType binder)
  , Just (mk, role, k1, k2) <- get_pred_tys_maybe ty
  = do { let origin = TypeEqOrigin { uo_actual   = k1
                                   , uo_expected = k2
                                   , uo_thing    = Nothing }
       ; co <- case role of
                 Nominal          -> unifyKind noThing k1 k2
                 Representational -> emitWantedEq origin KindLevel role k1 k2
                 Phantom          -> pprPanic "tcInstBinderX Phantom" (ppr binder)
       ; arg' <- mk co k1 k2
       ; return (subst, arg') }

  | otherwise -- TODO (RAE): I don't think this should be a panic.
              -- Try inst'ing a type with a silly kind.
  = pprPanic "visible binder in tcInstBinderX" (ppr binder)

  where
    lookup_tv tv = do { env <- mb_kind_info   -- `Maybe` monad
                      ; lookupVarEnv env tv }

      -- handle boxed equality constraints, because it's so easy
    get_pred_tys_maybe ty
      | Just (r, k1, k2) <- getEqPredTys_maybe ty
      = Just (\co _ _ -> return $ mkCoercionTy co, r, k1, k2)
      | Just (tc, [_, _, k1, k2]) <- splitTyConApp_maybe ty
      = if | tc `hasKey` heqTyConKey
             -> Just (mkHEqBoxTy, Nominal, k1, k2)
           | otherwise
             -> Nothing
      | Just (tc, [_, k1, k2]) <- splitTyConApp_maybe ty
      = if | tc `hasKey` eqTyConKey
             -> Just (mkEqBoxTy, Nominal, k1, k2)
           | tc `hasKey` coercibleTyConKey
             -> Just (mkCoercibleBoxTy, Representational, k1, k2)
           | otherwise
             -> Nothing
      | otherwise
      = Nothing

-------------------------------
-- | This takes @a ~# b@ and returns @a ~~ b@.
mkHEqBoxTy :: TcCoercion -> Type -> Type -> TcM Type
-- monadic just for convenience with mkEqBoxTy
mkHEqBoxTy co ty1 ty2
  = return $
    mkTyConApp (promoteDataCon heqDataCon) [k1, k2, ty1, ty2, mkCoercionTy co]
  where k1 = typeKind ty1
        k2 = typeKind ty2

-- | This takes @a ~# b@ and returns @a ~ b@.
mkEqBoxTy :: TcCoercion -> Type -> Type -> TcM Type
mkEqBoxTy co ty1 ty2
  = do { eq_tc <- tcLookupTyCon eqTyConName
       ; let [datacon] = tyConDataCons eq_tc
       ; hetero <- mkHEqBoxTy co ty1 ty2
       ; return $ mkTyConApp (promoteDataCon datacon) [k, ty1, ty2, hetero] }
  where k = typeKind ty1

-- | This takes @a ~R# b@ and returns @Coercible a b@.
mkCoercibleBoxTy :: TcCoercion -> Type -> Type -> TcM Type
-- monadic just for convenience with mkEqBoxTy
mkCoercibleBoxTy co ty1 ty2
  = do { return $
         mkTyConApp (promoteDataCon coercibleDataCon)
                    [k, ty1, ty2, mkCoercionTy co] }
  where k = typeKind ty1


--------------------------
checkExpectedKind :: TcType               -- the type whose kind we're checking
                  -> TcKind               -- the known kind of that type, k
                  -> TcKind               -- the expected kind, exp_kind
                  -> TcM TcType    -- a possibly-inst'ed, casted type :: exp_kind
-- Instantiate a kind (if necessary) and then call unifyType
--      (checkExpectedKind ty act_kind exp_kind)
-- checks that the actual kind act_kind is compatible
--      with the expected kind exp_kind
checkExpectedKind ty act_kind exp_kind
 = do { (ty', act_kind') <- instantiate ty act_kind exp_kind
      ; let origin = TypeEqOrigin { uo_actual   = act_kind'
                                  , uo_expected = exp_kind
                                  , uo_thing    = Just $ mkTypeErrorThing ty'
                                  }
      ; co_k <- uType origin KindLevel act_kind' exp_kind
      ; traceTc "checkExpectedKind" (vcat [ ppr act_kind
                                          , ppr exp_kind
                                          , ppr co_k ])
      ; let result_ty = ty' `mkNakedCastTy` co_k
      ; return result_ty }
  where
    -- we need to make sure that both kinds have the same number of implicit
    -- foralls out front. If the actual kind has more, instantiate accordingly.
    -- Otherwise, just pass the type & kind through -- the errors are caught
    -- in unifyType.
    instantiate :: TcType    -- the type
                -> TcKind    -- of this kind
                -> TcKind   -- but expected to be of this one
                -> TcM ( TcType   -- the inst'ed type
                       , TcKind ) -- its new kind
    instantiate ty act_ki exp_ki
      = let (exp_bndrs, _) = splitForAllTysInvisible exp_ki in
        instantiateTyN (length exp_bndrs) ty act_ki

-- | Instantiate a type to have at most @n@ invisible arguments.
instantiateTyN :: Int    -- ^ @n@
               -> TcType -- ^ the type
               -> TcKind -- ^ its kind
               -> TcM (TcType, TcKind)   -- ^ The inst'ed type with kind
instantiateTyN n ty ki
  = let (bndrs, inner_ki)            = splitForAllTysInvisible ki
        num_to_inst                  = length bndrs - n
           -- NB: splitAt is forgiving with invalid numbers
        (inst_bndrs, leftover_bndrs) = splitAt num_to_inst bndrs
    in
    if num_to_inst <= 0 then return (ty, ki) else
    do { (subst, inst_args) <- tcInstBinders inst_bndrs
       ; let rebuilt_ki = mkForAllTys leftover_bndrs inner_ki
             ki'        = substTy subst rebuilt_ki
       ; return (mkNakedAppTys ty inst_args, ki') }

---------------------------
tcHsContext :: LHsContext Name -> TcM [PredType]
tcHsContext = tc_hs_context typeLevelMode

tc_hs_context :: TcTyMode -> LHsContext Name -> TcM [PredType]
tc_hs_context mode ctxt = mapM (tc_hs_lpred mode) (unLoc ctxt)

tc_hs_lpred :: TcTyMode -> LHsType Name -> TcM PredType
tc_hs_lpred mode pred = tc_lhs_type mode pred constraintKind

---------------------------
tcTyVar :: TcTyMode -> Name -> TcM (TcType, TcKind)
-- See Note [Type checking recursive type and class declarations]
-- in TcTyClsDecls
tcTyVar mode name         -- Could be a tyvar, a tycon, or a datacon
  = do { traceTc "lk1" (ppr name)
       ; thing <- tcLookup name
       ; case thing of
           ATyVar _ tv -> return (mkTyVarTy tv, tyVarKind tv)

           AThing kind -> do { data_kinds <- xoptM Opt_DataKinds
                             ; unless (isTypeLevel (mode_level mode) ||
                                       data_kinds) $
                               promotionErr name NoDataKinds
                             ; tc <- get_loopy_tc name
                             ; return (mkNakedTyConApp tc [], kind) }
                             -- mkNakedTyConApp: see Note [Type-checking inside the knot]
                 -- NB: we really should check if we're at the kind level
                 -- and if the tycon is promotable if -XNoTypeInType is set.
                 -- But this is a terribly large amount of work! Not worth it.

           AGlobal (ATyCon tc)
             -> do { type_in_type <- xoptM Opt_TypeInType
                   ; data_kinds   <- xoptM Opt_DataKinds
                   ; unless (isTypeLevel (mode_level mode) ||
                             data_kinds ||
                             isKindTyCon tc) $
                       promotionErr name NoDataKinds
                   ; unless (isTypeLevel (mode_level mode) ||
                             type_in_type ||
                             isLegacyPromotableTyCon tc) $
                       promotionErr name NoTypeInTypeTC
                   ; return (mkTyConApp tc [], tyConKind tc) }

           AGlobal (AConLike (RealDataCon dc))
             -> do { data_kinds <- xoptM Opt_DataKinds
                   ; unless (data_kinds || specialPromotedDc dc) $
                       promotionErr name NoDataKinds
                   ; type_in_type <- xoptM Opt_TypeInType
                   ; unless ( type_in_type ||
                              ( isTypeLevel (mode_level mode) &&
                                isLegacyPromotableDataCon dc ) ||
                              ( isKindLevel (mode_level mode) &&
                                specialPromotedDc dc ) ) $
                       promotionErr name NoTypeInTypeDC
                   ; let tc = promoteDataCon dc
                   ; return (mkNakedTyConApp tc [], tyConKind tc) }

           APromotionErr err -> promotionErr name err

           _  -> wrongThingErr "type" thing name }
  where
    get_loopy_tc name
      = do { env <- getGblEnv
           ; case lookupNameEnv (tcg_type_env env) name of
                Just (ATyCon tc) -> return tc
                _                -> return (aThingErr "tcTyVar" name) }

tcClass :: Name -> TcM (Class, TcKind)
tcClass cls     -- Must be a class
  = do { thing <- tcLookup cls
       ; case thing of
           AThing kind -> return (aThingErr "tcClass" cls, kind)
           AGlobal (ATyCon tc)
             | Just cls <- tyConClass_maybe tc
             -> return (cls, tyConKind tc)
           _ -> wrongThingErr "class" thing cls }


aThingErr :: String -> Name -> b
-- The type checker for types is sometimes called simply to
-- do *kind* checking; and in that case it ignores the type
-- returned. Which is a good thing since it may not be available yet!
aThingErr str x = pprPanic "AThing evaluated unexpectedly" (text str <+> ppr x)

{-
Note [Type-checking inside the knot]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we are checking the argument types of a data constructor.  We
must zonk the types before making the DataCon, because once built we
can't change it.  So we must traverse the type.

BUT the parent TyCon is knot-tied, so we can't look at it yet.

So we must be careful not to use "smart constructors" for types that
look at the TyCon or Class involved.

  * Hence the use of mkNakedXXX functions. These do *not* enforce
    the invariants (for example that we use (ForAllTy (Anon s) t) rather
    than (TyConApp (->) [s,t])).

  * The zonking functions establish invariants (even zonkTcType, a change from
    previous behaviour). So we must never inspect the result of a
    zonk that might mention a knot-tied TyCon. This is generally OK
    because we zonk *kinds* while kind-checking types. And the TyCons
    in kinds shouldn't be knot-tied, because they come from a previous
    mutually recursive group.

  * TcHsSyn.zonkTcTypeToType also can safely check/establish
    invariants.

This is horribly delicate.  I hate it.  A good example of how
delicate it is can be seen in Trac #7903.

Note [Body kind of a forall]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The body of a forall is usually a type, but in principle
there's no reason to prohibit *unlifted* types.
In fact, GHC can itself construct a function with an
unboxed tuple inside a for-all (via CPR analyis; see
typecheck/should_compile/tc170).

Moreover in instance heads we get forall-types with
kind Constraint.

Moreover if we have a signature
   f :: Int#
then we represent it as (HsForAll Implicit [] [] Int#).  And this must
be legal!  We can't drop the empty forall until *after* typechecking
the body because of kind polymorphism:
   Typeable :: forall k. k -> Constraint
   data Apply f t = Apply (f t)
   -- Apply :: forall k. (k -> *) -> k -> *
   instance Typeable Apply where ...
Then the dfun has type
   df :: forall k. Typeable ((k->*) -> k -> *) (Apply k)

   f :: Typeable Apply

   f :: forall (t:k->*) (a:k).  t a -> t a

   class C a b where
      op :: a b -> Typeable Apply

   data T a = MkT (Typeable Apply)
            | T2 a
      T :: * -> *
      MkT :: forall k. (Typeable ((k->*) -> k -> *) (Apply k)) -> T a

   f :: (forall (k:*). forall (t:: k->*) (a:k). t a -> t a) -> Int
   f :: (forall a. a -> Typeable Apply) -> Int

So we *must* keep the HsForAll on the instance type
   HsForAll Implicit [] [] (Typeable Apply)
so that we do kind generalisation on it.

It's tempting to check that the body kind is either * or #. But this is
wrong. For example:

  class C a b
  newtype N = Mk Foo deriving (C a)

We're doing newtype-deriving for C. But notice how `a` isn't in scope in
the predicate `C a`. So we quantify, yielding `forall a. C a` even though
`C a` has kind `* -> Constraint`. The `forall a. C a` is a bit cheeky, but
convenient. Bottom line: don't check for * or # here.

Note [Inferring tuple kinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Give a tuple type (a,b,c), which the parser labels as HsBoxedOrConstraintTuple,
we try to figure out whether it's a tuple of kind * or Constraint.
  Step 1: look at the expected kind
  Step 2: infer argument kinds

If after Step 2 it's not clear from the arguments that it's
Constraint, then it must be *.  Once having decided that we re-check
the Check the arguments again to give good error messages
in eg. `(Maybe, Maybe)`

Note that we will still fail to infer the correct kind in this case:

  type T a = ((a,a), D a)
  type family D :: Constraint -> Constraint

While kind checking T, we do not yet know the kind of D, so we will default the
kind of T to * -> *. It works if we annotate `a` with kind `Constraint`.

Note [Desugaring types]
~~~~~~~~~~~~~~~~~~~~~~~
The type desugarer is phase 2 of dealing with HsTypes.  Specifically:

  * It transforms from HsType to Type

  * It zonks any kinds.  The returned type should have no mutable kind
    or type variables (hence returning Type not TcType):
      - any unconstrained kind variables are defaulted to (Any *) just
        as in TcHsSyn.
      - there are no mutable type variables because we are
        kind-checking a type
    Reason: the returned type may be put in a TyCon or DataCon where
    it will never subsequently be zonked.

You might worry about nested scopes:
        ..a:kappa in scope..
            let f :: forall b. T '[a,b] -> Int
In this case, f's type could have a mutable kind variable kappa in it;
and we might then default it to (Any *) when dealing with f's type
signature.  But we don't expect this to happen because we can't get a
lexically scoped type variable with a mutable kind variable in it.  A
delicate point, this.  If it becomes an issue we might need to
distinguish top-level from nested uses.

Moreover
  * it cannot fail,
  * it does no unifications
  * it does no validity checking, except for structural matters, such as
        (a) spurious ! annotations.
        (b) a class used as a type

Note [Kind of a type splice]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider these terms, each with TH type splice inside:
     [| e1 :: Maybe $(..blah..) |]
     [| e2 :: $(..blah..) |]
When kind-checking the type signature, we'll kind-check the splice
$(..blah..); we want to give it a kind that can fit in any context,
as if $(..blah..) :: forall k. k.

In the e1 example, the context of the splice fixes kappa to *.  But
in the e2 example, we'll desugar the type, zonking the kind unification
variables as we go.  When we encounter the unconstrained kappa, we
want to default it to '*', not to (Any *).


Help functions for type applications
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-}

addTypeCtxt :: LHsType Name -> TcM a -> TcM a
        -- Wrap a context around only if we want to show that contexts.
        -- Omit invisble ones and ones user's won't grok
addTypeCtxt (L _ ty) thing
  = addErrCtxt doc thing
  where
    doc = ptext (sLit "In the type") <+> quotes (ppr ty)

{-
************************************************************************
*                                                                      *
                Type-variable binders
%*                                                                      *
%************************************************************************
-}

tcWildcardBinders :: [Name]
                  -> ([(Name,TcTyVar)] -> TcM a)
                  -> TcM a
tcWildcardBinders wcs thing_inside
  = do { wc_prs <- mapM new_wildcard wcs
       ; tcExtendTyVarEnv2 wc_prs $
         thing_inside wc_prs }
  where
   new_wildcard :: Name -> TcM (Name, TcTyVar)
   new_wildcard name = do { kind <- newMetaKindVar
                          ; tv   <- newFlexiTyVar kind
                          ; return (name, tv) }

-- | Kind-check a 'LHsTyVarBndrs'. If the decl under consideration has a complete,
-- user-supplied kind signature (CUSK), generalise the result.
-- Used in 'getInitialKind' (for tycon kinds and other kinds)
-- and in kind-checking (but not for tycon kinds, which are checked with
-- tcTyClDecls). See also Note [Complete user-supplied kind signatures] in
-- HsDecls.
--
-- You probably want to call checkValidTelescope after kind-checking any
-- scope these binders include, as this function does not do telescope
-- checking.
kcHsTyVarBndrs :: Bool    -- ^ True <=> the decl being checked has a CUSK
               -> LHsTyVarBndrs Name
               -> ([TyVar] -> [TyVar] -> TcM (Kind, r))
                                  -- ^ the result kind, possibly with other info
                                  -- ^ args are implicit vars, explicit vars
               -> TcM (Kind, r)   -- ^ The full kind of the thing being declared,
                                  -- with the other info
kcHsTyVarBndrs cusk (HsQTvs { hsq_implicit = kv_ns
                            , hsq_explicit = hs_tvs }) thing_inside
  = do { meta_kvs <- mapM (const newMetaKindVar) kv_ns
       ; kvs <- if cusk
                then return $ zipWith new_skolem_tv kv_ns meta_kvs
                     -- the names must line up in splitTelescopeTvs
                else zipWithM newSigTyVar kv_ns meta_kvs
       ; tcExtendTyVarEnv2 (kv_ns `zip` kvs) $
    do { (full_kind, _, stuff) <- bind_telescope hs_tvs (thing_inside kvs)
       ; let qkvs = filter (not . isMetaTyVar) $
                    varSetElemsWellScoped $ tyCoVarsOfType full_kind

                -- the free non-meta variables in the returned kind will
                -- contain both *mentioned* kind vars and *unmentioned* kind
                -- vars (See case (1) under Note [Typechecking telescopes])
             gen_kind  = if cusk
                         then mkInvForAllTys qkvs $ full_kind
                         else full_kind
       ; return (gen_kind, stuff) } }
  where
      -- there may be dependency between the explicit "ty" vars. So, we have
      -- to handle them one at a time. We also need to build up a full kind
      -- here, because this is the place we know whether to use a FunTy or a
      -- ForAllTy. We prefer using an anonymous binder over a trivial named
      -- binder. If a user wants a trivial named one, use an explicit kind
      -- signature.
    bind_telescope :: [LHsTyVarBndr Name]
                   -> ([TyVar] -> TcM (Kind, r))
                   -> TcM (Kind, VarSet, r)
    bind_telescope [] thing
      = do { (res_kind, stuff) <- thing []
           ; return (res_kind, tyCoVarsOfType res_kind, stuff) }
    bind_telescope (L _ hs_tv : hs_tvs) thing
      = do { (n,k) <- kc_hs_tv hs_tv
           ; let tv = new_skolem_tv n k
           ; (res_kind, fvs, stuff) <- tcExtendTyVarEnv2 [(n,tv)] $
                                       bind_telescope hs_tvs $ \tvs ->
                                       thing (tv:tvs)
              -- we must be *lazy* in res_kind and fvs (assuming that the
              -- caller of kcHsTyVarBndrs is, too), as sometimes these hold
              -- panics. See kcConDecl.
           ; let m_kv = lookupVarSetByName fvs n
                 (bndr, fvs') = case m_kv of
                   Just kv -> ( mkNamedBinder kv Visible
                              , fvs `delVarSet` kv
                                    `unionVarSet` tyCoVarsOfType k )
                   Nothing -> ( mkAnonBinder k
                              , fvs `unionVarSet` tyCoVarsOfType k )

           ; return ( mkForAllTy bndr res_kind, fvs', stuff ) }

    kc_hs_tv :: HsTyVarBndr Name -> TcM (Name, TcKind)
    kc_hs_tv (UserTyVar n)
      = do { mb_thing <- tcLookupLcl_maybe n
           ; kind <- case mb_thing of
                       Just (ATyVar _ tv) -> return (tyVarKind tv)
                       _ | cusk           -> return liftedTypeKind
                         | otherwise      -> newMetaKindVar
           ; return (n, kind) }
    kc_hs_tv (KindedTyVar (L _ n) k)
      = do { kind <- tcLHsKind k
               -- In an associated type decl, the type variable may already
               -- be in scope; in that case we want to make sure its kind
               -- matches the one declared here
           ; mb_thing <- tcLookupLcl_maybe n
           ; case mb_thing of
               Nothing            -> return ()
                                     -- we only need the side effects;
                                     -- no need for coercion
               Just (ATyVar _ tv) -> discardResult $
                                     unifyKind (Just (mkTyVarTy tv)) kind
                                               (tyVarKind tv)
               Just thing         -> pprPanic "check_in_scope" (ppr thing)
           ; kind <- zonkTcType kind
           ; return (n, kind) }

tcHsTyVarBndrs :: HsExplicitFlag      -- ^ did the user choose the ordering of tvs?
               -> LHsTyVarBndrs Name
               -> TcM r               -- ^ kind-check the body
               -> TcM ([TcTyVar], r)  -- ^ zonked tyvars, with the body result
                                      -- (NB: not zonked *fully*)
-- Bind the kind variables to fresh skolem variables
-- and type variables to skolems, each with a meta-kind variable kind
tcHsTyVarBndrs expflag
               qtvs@(HsQTvs { hsq_implicit = kv_ns, hsq_explicit = hs_tvs })
               thing_inside
  | null kv_ns && null hs_tvs
  = do { traceTc "empty tcHsTyVarBndrs" empty
       ; ([], ) <$> thing_inside }

  | otherwise
  = go (map UserTyVar kv_ns) $ \kvs -> go (map unLoc hs_tvs) $ \tvs ->
    do { traceTc "tcHsTyVarBndrs {" $
           vcat [ text "Hs implicit vars:" <+> ppr kv_ns
                , text "Hs explicit vars:" <+> ppr hs_tvs
                , text "kvs:" <+> sep (map pprTvBndr kvs)
                , text "tvs:" <+> sep (map pprTvBndr tvs) ]

       ; result <- thing_inside

       ; kvs <- mapM zonkTyCoVarKind kvs
       ; tvs <- mapM zonkTyCoVarKind tvs

         -- If the ordering of the variables is user-specified, issue an error
         -- if the ordering is bogus. See Note [Bad telescopes] in TcValidity.
         -- Otherwise, reorder as necessary.
       ; when (expflag == Explicit) $ checkValidTelescope qtvs kvs tvs

       ; let final_tvs = toposortTyVars (kvs ++ tvs)

       ; traceTc "tcHsTyVarBndrs }" $
           vcat [ text "Hs implicit vars:" <+> ppr kv_ns
                , text "Hs explicit vars:" <+> ppr hs_tvs
                , text "kvs:" <+> sep (map pprTvBndr kvs)
                , text "tvs:" <+> sep (map pprTvBndr tvs)
                , text "final_tvs:" <+> sep (map pprTvBndr final_tvs) ]

       ; return (final_tvs, result) }

  where go [] thing = thing []
        go (hs_tv : hs_tvs) thing
          = tcHsTyVarBndr hs_tv $ \tv ->
            tcExtendTyVarEnv [tv] $
            go hs_tvs $ \tvs ->
            thing (tv : tvs)

tcHsTyVarBndr :: HsTyVarBndr Name -> (TcTyVar -> TcM r) -> TcM r
-- Bind a new type variable for thing_inside. This type variable
-- is given a meta-kind variable (for UserTyVar) or the type-checked kind
-- (for KindedTyVar)
--
-- If the variable is already in scope, use that one, instead of introducing a new
-- one. This can occur in
--   instance C (a,b) where
--     type F (a,b) c = ...
-- Here a,b will be in scope when processing the associated type instance for F.
-- See Note [Associated type tyvar names] in Class
tcHsTyVarBndr hs_tv thing_inside
  = do { let name = hsTyVarName hs_tv
       ; mb_tv <- tcLookupLcl_maybe name
       ; case mb_tv of {
           Just (ATyVar _ tv) -> thing_inside tv ;
           _ -> do
       { kind <- case hs_tv of
                   UserTyVar {}       -> newMetaKindVar
                   KindedTyVar _ kind -> tcLHsKind kind
       ; thing_inside $ new_skolem_tv name kind } } }

-- makes a new skolem tv
new_skolem_tv :: Name -> Kind -> TcTyVar
new_skolem_tv n k = mkTcTyVar n k vanillaSkolemTv

------------------
kindGeneralize :: TyVarSet -> TcM [KindVar]
kindGeneralize tkvs
  = do { gbl_tvs <- tcGetGlobalTyCoVars -- Already zonked
       ; quantifyTyVars gbl_tvs (Pair tkvs emptyVarSet) }

{-
Note [Kind generalisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~
We do kind generalisation only at the outer level of a type signature.
For example, consider
  T :: forall k. k -> *
  f :: (forall a. T a -> Int) -> Int
When kind-checking f's type signature we generalise the kind at
the outermost level, thus:
  f1 :: forall k. (forall (a:k). T k a -> Int) -> Int  -- YES!
and *not* at the inner forall:
  f2 :: (forall k. forall (a:k). T k a -> Int) -> Int  -- NO!
Reason: same as for HM inference on value level declarations,
we want to infer the most general type.  The f2 type signature
would be *less applicable* than f1, because it requires a more
polymorphic argument.

Note [Kinds of quantified type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
tcTyVarBndrsGen quantifies over a specified list of type variables,
*and* over the kind variables mentioned in the kinds of those tyvars.

Note that we must zonk those kinds (obviously) but less obviously, we
must return type variables whose kinds are zonked too. Example
    (a :: k7)  where  k7 := k9 -> k9
We must return
    [k9, a:k9->k9]
and NOT
    [k9, a:k7]
Reason: we're going to turn this into a for-all type,
   forall k9. forall (a:k7). blah
which the type checker will then instantiate, and instantiate does not
look through unification variables!

Hence using zonked_kinds when forming tvs'.

Note [Typechecking telescopes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The function tcTyClTyVars has to bind the scoped type and kind
variables in a telescope. For example:

class Foo k (t :: Proxy k -> k2) where ...

By the time [kt]cTyClTyVars is called, we know *something* about the kind of Foo,
at least that it has the form

  Foo :: forall (k2 :: mk2). forall (k :: mk1) -> (Proxy mk1 k -> k2) -> Constraint

if it has a CUSK (Foo does not, in point of fact) or

  Foo :: forall (k :: mk1) -> (Proxy mk1 k -> k2) -> Constraint

if it does not, where mk1 and mk2 are meta-kind variables (mk1, mk2 :: *).

When calling tcTyClTyVars, this kind is further generalized w.r.t. any
free variables appearing in mk1 or mk2. So, mk_tvs must handle
that possibility. Perhaps we discover that mk1 := Maybe k3 and mk2 := *,
so we have

Foo :: forall (k3 :: *). forall (k2 :: *). forall (k :: Maybe k3) ->
       (Proxy (Maybe k3) k -> k2) -> Constraint

We now have several sorts of variables to think about:
1) The variable k3 is not mentioned in the source at all. It is neither
   explicitly bound nor ever used. It is *not* a scoped kind variable,
   and should not be bound when type-checking the scope of the telescope.

2) The variable k2 is mentioned in the source, but it is not explicitly
   bound. It *is* a scoped kind variable, and will appear in the
   hsq_implicit field of a LHsTyVarBndrs.

3) The variable k is mentioned in the source with an explicit binding.
   It *is* a scoped type variable, and will appear in the
   hsq_explicit field of a LHsTyVarBndrs.

4) The variable t is bound in the source, but it is never mentioned later
   in the kind. It *is* a scoped variable (it can appear in the telescope
   scope, even though it is non-dependent), and will appear in the
   hsq_explicit field of a LHsTyVarBndrs.

splitTelescopeTvs walks through the output of a splitForAllTys on the
telescope head's kind (Foo, in our example), creating a list of tyvars
to be bound within the telescope scope. It must simultaneously walk
through the hsq_implicit and hsq_explicit fields of a LHsTyVarBndrs.
Comments in the code refer back to the cases in this Note.

Cases (1) and (2) can be mixed together, but these cases must appear before
cases (3) and (4) (the implicitly bound vars always precede the explicitly
bound ones). So, we handle the lists in two stages (mk_tvs and
mk_tvs2).

As a further wrinkle, it's possible that the variables in case (2) have
been reordered. This is because hsq_implicit is ordered by the renamer,
but there may be dependency among the variables. Of course, the order in
the kind must take dependency into account. So we use a NameSet to keep
these straightened out.

-}

--------------------
-- getInitialKind has made a suitably-shaped kind for the type or class
-- Unpack it, and attribute those kinds to the type variables
-- Extend the env with bindings for the tyvars, taken from
-- the kind of the tycon/class.  Give it to the thing inside, and
-- check the result kind matches
kcLookupKind :: Name -> TcM Kind
kcLookupKind nm
  = do { tc_ty_thing <- tcLookup nm
       ; case tc_ty_thing of
           AThing k            -> return k
           AGlobal (ATyCon tc) -> return (tyConKind tc)
           _                   -> pprPanic "kcLookupKind" (ppr tc_ty_thing) }

-- See Note [Typechecking telescopes]
splitTelescopeTvs :: Kind         -- of the head of the telescope
                  -> LHsTyVarBndrs Name
                  -> ( [TyVar]    -- *scoped* type variables
                     , [TyVar]    -- *implicit* type variables (cases 1 & 2)
                     , [TyVar]    -- *explicit* type variables (cases 3 & 4)
                     , Kind )     -- result kind
splitTelescopeTvs kind tvbs@(HsQTvs { hsq_implicit = hs_kvs
                                    , hsq_explicit = hs_tvs })
  = let (bndrs, inner_ki) = splitForAllTys kind
        (scoped_tvs, imp_tvs, exp_tvs, mk_kind)
          = mk_tvs [] [] bndrs (mkNameSet hs_kvs) hs_tvs
    in
    (scoped_tvs, imp_tvs, exp_tvs, mk_kind inner_ki)
  where
    mk_tvs :: [TyVar]    -- scoped tv accum (reversed)
           -> [TyVar]    -- implicit tv accum (reversed)
           -> [Binder]
           -> NameSet             -- implicit variables
           -> [LHsTyVarBndr Name] -- explicit variables
           -> ( [TyVar]           -- the tyvars to be lexically bound
              , [TyVar]           -- implicit tyvars
              , [TyVar]           -- explicit tyvars
              , Type -> Type )    -- a function to create the result k
    mk_tvs scoped_tv_acc imp_tv_acc (bndr : bndrs) all_hs_kvs all_hs_tvs
      | Just tv <- binderVar_maybe bndr
      , isInvisibleBinder bndr
      , let tv_name = getName tv
      , tv_name `elemNameSet` all_hs_kvs
      = mk_tvs (tv : scoped_tv_acc) (tv : imp_tv_acc)
               bndrs (all_hs_kvs `delFromNameSet` tv_name) all_hs_tvs      -- Case (2)

      | Just tv <- binderVar_maybe bndr
      , isInvisibleBinder bndr
      = mk_tvs scoped_tv_acc (tv : imp_tv_acc)
               bndrs all_hs_kvs all_hs_tvs  -- Case (1)

     -- there may actually still be some hs_kvs, if we're kind checking
     -- a non-CUSK. The kinds *aren't* generalized, so we won't see them
     -- here.
    mk_tvs scoped_tv_acc imp_tv_acc all_bndrs _all_hs_kvs all_hs_tvs
      = let (scoped, exp_tvs, mk_kind)
              = mk_tvs2 scoped_tv_acc [] all_bndrs all_hs_tvs in
        (scoped, reverse imp_tv_acc, exp_tvs, mk_kind)
           -- no more Case (1) or (2)

    -- This can't handle Case (1) or Case (2) from [Typechecking telescopes]
    mk_tvs2 :: [TyVar]
            -> [TyVar]   -- new parameter: explicit tv accum (reversed)
            -> [Binder]
            -> [LHsTyVarBndr Name]
            -> ( [TyVar]
               , [TyVar]   -- explicit tvs only
               , Type -> Type )
    mk_tvs2 scoped_tv_acc exp_tv_acc (bndr : bndrs) (hs_tv : hs_tvs)
      | Just tv <- binderVar_maybe bndr
      = ASSERT2( isVisibleBinder bndr, err_doc )
        ASSERT( getName tv == hsLTyVarName hs_tv )
        mk_tvs2 (tv : scoped_tv_acc) (tv : exp_tv_acc) bndrs hs_tvs   -- Case (3)

      | otherwise
      = ASSERT( isVisibleBinder bndr )
        let tv = mkTyVar (hsLTyVarName hs_tv) (binderType bndr) in
        mk_tvs2 (tv : scoped_tv_acc) (tv : exp_tv_acc) bndrs hs_tvs   -- Case (4)
      where
        err_doc = vcat [ ppr (bndr : bndrs)
                       , ppr (hs_tv : hs_tvs)
                       , ppr kind
                       , ppr tvbs ]

    mk_tvs2 scoped_tv_acc exp_tv_acc all_bndrs [] -- All done!
      = ( reverse scoped_tv_acc
        , reverse exp_tv_acc
        , mkForAllTys all_bndrs )

    mk_tvs2 _ _ all_bndrs all_hs_tvs
      = pprPanic "splitTelescopeTvs 2" (vcat [ ppr all_bndrs
                                             , ppr all_hs_tvs ])


-----------------------
tcTyClTyVars :: Name -> LHsTyVarBndrs Name      -- LHS of the type or class decl
             -> ([TyVar] -> [TyVar] -> Kind -> Kind -> TcM a) -> TcM a
-- Used for the type variables of a type or class decl
-- on both the first and second full passes in TcTyClDecls.
-- *Not* used in the initial-kind run.
--
-- (tcTyClTyVars T [a,b] thing_inside)
--   where T : forall k1 k2 (a:k1 -> *) (b:k1). k2 -> *
--   calls thing_inside with arguments
--      [k1,k2] [a,b] (forall (k1:*) (k2:*) (a:k1 -> *) (b:k1). k2 -> *) (k2 -> *)
--   having also extended the type environment with bindings
--   for k1,k2,a,b
--
-- No need to freshen the k's because they are just skolem
-- constants here, and we are at top level anyway.
--
-- Never emits constraints.
--
-- The LHsTyVarBndrs is always user-written, and the kind of the tycon
-- is available in the local env.
tcTyClTyVars tycon hs_tvs thing_inside
  = do { kind <- kcLookupKind tycon
       ; let (scoped_tvs, all_kvs, all_tvs, res_k) = splitTelescopeTvs kind hs_tvs
       ; traceTc "tcTyClTyVars splitTelescopeTvs:"
           (vcat [ text "Tycon:" <+> ppr tycon
                 , text "Kind:" <+> ppr kind
                 , text "hs_tvs:" <+> ppr hs_tvs
                 , text "scoped tvs:" <+> pprWithCommas pprTvBndr scoped_tvs
                 , text "implicit tvs:" <+> pprWithCommas pprTvBndr all_kvs
                 , text "explicit tvs:" <+> pprWithCommas pprTvBndr all_tvs
                 , text "res_k:" <+> ppr res_k] )

       ; tcExtendTyVarEnv scoped_tvs $ thing_inside all_kvs all_tvs kind res_k }

-----------------------------------
tcDataKindSig :: Kind -> TcM [TyVar]
-- GADT decls can have a (perhaps partial) kind signature
--      e.g.  data T :: * -> * -> * where ...
-- This function makes up suitable (kinded) type variables for
-- the argument kinds, and checks that the result kind is indeed *.
-- We use it also to make up argument type variables for for data instances.
-- Never emits constraints.
tcDataKindSig kind
  = do  { checkTc (isLiftedTypeKind res_kind) (badKindSig kind)
        ; span <- getSrcSpanM
        ; us   <- newUniqueSupply
        ; rdr_env <- getLocalRdrEnv
        ; let uniqs = uniqsFromSupply us
              occs  = [ occ | str <- allNameStrings
                            , let occ = mkOccName tvName str
                            , isNothing (lookupLocalRdrOcc rdr_env occ) ]
                 -- Note [Avoid name clashes for associated data types]

        ; return [ mk_tv span uniq occ kind
                 | ((kind, occ), uniq) <- arg_kinds `zip` occs `zip` uniqs ] }
  where
    (bndrs, res_kind) = splitForAllTys kind
    arg_kinds         = map binderType bndrs
    mk_tv loc uniq occ kind
      = mkTyVar (mkInternalName uniq occ loc) kind

badKindSig :: Kind -> SDoc
badKindSig kind
 = hang (ptext (sLit "Kind signature on data type declaration has non-* return kind"))
        2 (ppr kind)

{-
Note [Avoid name clashes for associated data types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider    class C a b where
               data D b :: * -> *
When typechecking the decl for D, we'll invent an extra type variable
for D, to fill out its kind.  Ideally we don't want this type variable
to be 'a', because when pretty printing we'll get
            class C a b where
               data D b a0
(NB: the tidying happens in the conversion to IfaceSyn, which happens
as part of pretty-printing a TyThing.)

That's why we look in the LocalRdrEnv to see what's in scope. This is
important only to get nice-looking output when doing ":info C" in GHCi.
It isn't essential for correctness.


************************************************************************
*                                                                      *
                Scoped type variables
*                                                                      *
************************************************************************


tcAddScopedTyVars is used for scoped type variables added by pattern
type signatures
        e.g.  \ ((x::a), (y::a)) -> x+y
They never have explicit kinds (because this is source-code only)
They are mutable (because they can get bound to a more specific type).

Usually we kind-infer and expand type splices, and then
tupecheck/desugar the type.  That doesn't work well for scoped type
variables, because they scope left-right in patterns.  (e.g. in the
example above, the 'a' in (y::a) is bound by the 'a' in (x::a).

The current not-very-good plan is to
  * find all the types in the patterns
  * find their free tyvars
  * do kind inference
  * bring the kinded type vars into scope
  * BUT throw away the kind-checked type
        (we'll kind-check it again when we type-check the pattern)

This is bad because throwing away the kind checked type throws away
its splices.  But too bad for now.  [July 03]

Historical note:
    We no longer specify that these type variables must be universally
    quantified (lots of email on the subject).  If you want to put that
    back in, you need to
        a) Do a checkSigTyVars after thing_inside
        b) More insidiously, don't pass in expected_ty, else
           we unify with it too early and checkSigTyVars barfs
           Instead you have to pass in a fresh ty var, and unify
           it with expected_ty afterwards
-}

tcHsPatSigType :: UserTypeCtxt
               -> HsWithBndrs Name (LHsType Name) -- The type signature
               -> TcM ( Type                      -- The signature
                      , [(Name, TcTyVar)]     -- The new bit of type environment, binding
                                              -- the scoped type variables
                      , [(Name, TcTyVar)] )   -- The wildcards
-- Used for type-checking type signatures in
-- (a) patterns           e.g  f (x::Int) = e
-- (b) result signatures  e.g. g x :: Int = e
-- (c) RULE forall bndrs  e.g. forall (x::Int). f x = x

tcHsPatSigType ctxt (HsWB { hswb_cts = hs_ty, hswb_vars = sig_vars
                          , hswb_wcs = sig_wcs })
  = addErrCtxt (pprSigCtxt ctxt empty (ppr hs_ty)) $
    tcWildcardBinders sig_wcs $ \ nwc_binds ->
    do  { emitWildcardHoleConstraints nwc_binds
        ; vars <- mapM new_tv sig_vars
        ; let ktv_binds = sig_vars `zip` vars
        ; sig_ty <- solveEqualities $
                    tcExtendTyVarEnv2 ktv_binds $
                    tcHsLiftedType hs_ty
        ; sig_ty <- zonkTcTypeToType emptyZonkEnv sig_ty
        ; checkValidType ctxt sig_ty
        ; return (sig_ty, ktv_binds, nwc_binds) }
  where
    new_tv name = do { kind <- newMetaKindVar
                     ; new_tkv name kind }

    new_tkv name kind  -- See Note [Pattern signature binders]
      = case ctxt of
          RuleSigCtxt {} -> return $ new_skolem_tv name kind
          _              -> newSigTyVar name kind -- See Note [Unifying SigTvs]

tcPatSig :: Bool                    -- True <=> pattern binding
         -> HsWithBndrs Name (LHsType Name)
         -> TcSigmaType
         -> TcM (TcType,            -- The type to use for "inside" the signature
                 [(Name, TcTyVar)], -- The new bit of type environment, binding
                                    -- the scoped type variables
                 [(Name, TcTyVar)], -- The wildcards
                 HsWrapper)         -- Coercion due to unification with actual ty
                                    -- Of shape:  res_ty ~ sig_ty
tcPatSig in_pat_bind sig res_ty
  = do  { (sig_ty, sig_tvs, sig_nwcs) <- tcHsPatSigType PatSigCtxt sig
        -- sig_tvs are the type variables free in 'sig',
        -- and not already in scope. These are the ones
        -- that should be brought into scope

        ; if null sig_tvs then do {
                -- Just do the subsumption check and return
                  wrap <- addErrCtxtM (mk_msg sig_ty) $
                          tcSubType_NC PatSigCtxt res_ty sig_ty
                ; return (sig_ty, [], sig_nwcs, wrap)
        } else do
                -- Type signature binds at least one scoped type variable

                -- A pattern binding cannot bind scoped type variables
                -- It is more convenient to make the test here
                -- than in the renamer
        { when in_pat_bind (addErr (patBindSigErr sig_tvs))

                -- Check that all newly-in-scope tyvars are in fact
                -- constrained by the pattern.  This catches tiresome
                -- cases like
                --      type T a = Int
                --      f :: Int -> Int
                --      f (x :: T a) = ...
                -- Here 'a' doesn't get a binding.  Sigh
        ; let bad_tvs = [ tv | (_, tv) <- sig_tvs
                             , not (tv `elemVarSet` exactTyCoVarsOfType sig_ty) ]
        ; checkTc (null bad_tvs) (badPatSigTvs sig_ty bad_tvs)

        -- Now do a subsumption check of the pattern signature against res_ty
        ; wrap <- addErrCtxtM (mk_msg sig_ty) $
                  tcSubType_NC PatSigCtxt res_ty sig_ty

        -- Phew!
        ; return (sig_ty, sig_tvs, sig_nwcs, wrap)
        } }
  where
    mk_msg sig_ty tidy_env
       = do { (tidy_env, sig_ty) <- zonkTidyTcType tidy_env sig_ty
            ; (tidy_env, res_ty) <- zonkTidyTcType tidy_env res_ty
            ; let msg = vcat [ hang (ptext (sLit "When checking that the pattern signature:"))
                                  4 (ppr sig_ty)
                             , nest 2 (hang (ptext (sLit "fits the type of its context:"))
                                          2 (ppr res_ty)) ]
            ; return (tidy_env, msg) }

patBindSigErr :: [(Name, TcTyVar)] -> SDoc
patBindSigErr sig_tvs
  = hang (ptext (sLit "You cannot bind scoped type variable") <> plural sig_tvs
          <+> pprQuotedList (map fst sig_tvs))
       2 (ptext (sLit "in a pattern binding signature"))

{-
Note [Pattern signature binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
   data T = forall a. T a (a->Int)
   f (T x (f :: a->Int) = blah)

Here
 * The pattern (T p1 p2) creates a *skolem* type variable 'a_sk',
   It must be a skolem so that that it retains its identity, and
   TcErrors.getSkolemInfo can thereby find the binding site for the skolem.

 * The type signature pattern (f :: a->Int) binds "a" -> a_sig in the envt

 * Then unificaiton makes a_sig := a_sk

That's why we must make a_sig a MetaTv (albeit a SigTv),
not a SkolemTv, so that it can unify to a_sk.

For RULE binders, though, things are a bit different (yuk).
  RULE "foo" forall (x::a) (y::[a]).  f x y = ...
Here this really is the binding site of the type variable so we'd like
to use a skolem, so that we get a complaint if we unify two of them
together.

Note [Unifying SigTvs]
~~~~~~~~~~~~~~~~~~~~~~
ALAS we have no decent way of avoiding two SigTvs getting unified.
Consider
  f (x::(a,b)) (y::c)) = [fst x, y]
Here we'd really like to complain that 'a' and 'c' are unified. But
for the reasons above we can't make a,b,c into skolems, so they
are just SigTvs that can unify.  And indeed, this would be ok,
  f x (y::c) = case x of
                 (x1 :: a1, True) -> [x,y]
                 (x1 :: a2, False) -> [x,y,y]
Here the type of x's first component is called 'a1' in one branch and
'a2' in the other.  We could try insisting on the same OccName, but
they definitely won't have the sane lexical Name.

I think we could solve this by recording in a SigTv a list of all the
in-scope variables that it should not unify with, but it's fiddly.


************************************************************************
*                                                                      *
        Checking kinds
*                                                                      *
************************************************************************

-}

-- | Produce an 'TcKind' suitable for a checking a type that can be * or #.
ekOpen :: TcM TcKind
ekOpen = do { lev <- newFlexiTyVarTy levityTy
            ; return (tYPE lev) }

unifyKinds :: [(TcType, TcKind)] -> TcM ([TcType], TcKind)
unifyKinds act_kinds
  = do { kind <- newMetaKindVar
       ; let check (ty, act_kind) = checkExpectedKind ty act_kind kind
       ; tys' <- mapM check act_kinds
       ; return (tys', kind) }

{-
************************************************************************
*                                                                      *
        Sort checking kinds
*                                                                      *
************************************************************************

tcLHsKind converts a user-written kind to an internal, sort-checked kind.
It does sort checking and desugaring at the same time, in one single pass.
-}

tcLHsKind :: LHsKind Name -> TcM Kind
tcLHsKind = tc_lhs_kind kindLevelMode

tc_lhs_kind :: TcTyMode -> LHsKind Name -> TcM Kind
tc_lhs_kind mode k
  = addErrCtxt (ptext (sLit "In the kind") <+> quotes (ppr k)) $
    tc_lhs_type (kindLevel mode) k liftedTypeKind

promotionErr :: Name -> PromotionErr -> TcM a
promotionErr name err
  = failWithTc (hang (pprPECategory err <+> quotes (ppr name) <+> ptext (sLit "cannot be used here"))
                   2 (parens reason))
  where
    reason = case err of
               FamDataConPE   -> text "it comes from a data family instance"
               NoDataKinds    -> text "Perhaps you intended to use DataKinds"
               NoTypeInTypeTC -> text "Perhaps you intended to use TypeInType"
               NoTypeInTypeDC -> text "Perhaps you intended to use TypeInType"
               _ -> text "it is defined and used in the same recursive group"

{-
************************************************************************
*                                                                      *
                Scoped type variables
*                                                                      *
************************************************************************
-}

badPatSigTvs :: TcType -> [TyVar] -> SDoc
badPatSigTvs sig_ty bad_tvs
  = vcat [ fsep [ptext (sLit "The type variable") <> plural bad_tvs,
                 quotes (pprWithCommas ppr bad_tvs),
                 ptext (sLit "should be bound by the pattern signature") <+> quotes (ppr sig_ty),
                 ptext (sLit "but are actually discarded by a type synonym") ]
         , ptext (sLit "To fix this, expand the type synonym")
         , ptext (sLit "[Note: I hope to lift this restriction in due course]") ]

{-
************************************************************************
*                                                                      *
          Error messages and such
*                                                                      *
************************************************************************
-}

-- | Make an appropriate message for an error in a function argument.
-- Used for both expressions and types.
funAppCtxt :: (Outputable fun, Outputable arg) => fun -> arg -> Int -> SDoc
funAppCtxt fun arg arg_no
  = hang (hsep [ ptext (sLit "In the"), speakNth arg_no, ptext (sLit "argument of"),
                    quotes (ppr fun) <> text ", namely"])
       2 (quotes (ppr arg))
