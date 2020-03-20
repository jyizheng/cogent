theory Syntax
  imports "../Cogent"
begin

ML \<open>

type index = int;
type name = string;
type field = int;
type fnname = string;

datatype sigil = RO | WR | UB;

datatype prim_type = U8 | U16 | U32 | U64 | Bool | Str;

datatype prim_op
  = Plus | Minus
  | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge
  | Eq | NEq
  | BitAnd | BitOr | BitXor
  | LShift | RShift
  | Complement;

datatype lit = LBool of bool
             | LU8 of string
             | LU16 of string
             | LU32 of string
             | LU64 of string;

datatype record_state = Taken | Untaken;
datatype variant_state = Checked | Unchecked;

datatype cogent_ty
  = TVar of index
  | TVarBang of index
  | TCon of { name: name, tyargs: cogent_ty list, sgl: sigil }
  | TFun of cogent_ty * cogent_ty
  | TPrim of prim_type
  | TSum of (name * cogent_ty * variant_state) list
  | TProduct of cogent_ty * cogent_ty
  | TRecord of { fs: (name * cogent_ty * record_state) list, sgl: sigil }
  | TUnit;

datatype cogent_expr
  = Var of index
  | Fun of { name: string, tyargs: cogent_ty list }
  | Prim of { oper: prim_op, es: cogent_expr list }
  | App of cogent_expr * cogent_expr
  | Con of { altnm: name, vval: cogent_expr, vtys: (name * cogent_ty * variant_state) list }
  | Struct of cogent_ty list * cogent_expr list
  | Member of { er: cogent_expr, idx: field }
  | Unit
  | Lit of lit
  | SLit of string
  | Cast of prim_type * cogent_expr
  | Tuple of cogent_expr * cogent_expr
  | Put of { er: cogent_expr, idx: field, ev: cogent_expr }
  | Let of { ev: cogent_expr, ek: cogent_expr }
  | LetBang of { idxs: int list, ev: cogent_expr, ek: cogent_expr }
  | Case of { eval: cogent_expr, altnm: name, ematch: cogent_expr, enomatch: cogent_expr }
  | Esac of cogent_expr
  | If of { econd: cogent_expr, ektt: cogent_expr, ekff: cogent_expr }
  | Take of { erec: cogent_expr, idx: field, ek: cogent_expr }
  | Split of { ep: cogent_expr, ek: cogent_expr }
  | Promote of cogent_ty * cogent_expr;
\<close>

ML \<open>
val deep_expr =  @{typ "string expr"};
\<close>

thm
  typing_var
  typing_afun
  typing_fun
  typing_app
  typing_cast
  typing_tuple
  typing_split
  typing_let
  typing_letb
  typing_con
  typing_case
  typing_esac
  typing_if
  typing_prim
  typing_lit
  typing_slit
  typing_unit
  typing_struct
  typing_member
  typing_take
  typing_put
  typing_promote
  typing_all_empty
  typing_all_cons

thm typing_fun
  typing_afun

ML \<open>

fun mk_sigil RO = @{term "Boxed ReadOnly todo"}
  | mk_sigil WR = @{term "Boxed Writable todo"}
  | mk_sigil UB = @{term "Unboxed"}

fun mk_prim_type U8   = @{term "Num U8"}
  | mk_prim_type U16  = @{term "Num U16"}
  | mk_prim_type U32  = @{term "Num U32"}
  | mk_prim_type U64  = @{term "Num U64"}
  | mk_prim_type Bool = @{term Bool}
  | mk_prim_type Str  = @{term String}

fun mk_record_state Taken = @{term Taken}
  | mk_record_state Untaken = @{term Present}

fun mk_variant_state Checked = @{term Checked}
  | mk_variant_state Unchecked = @{term Unchecked}

fun cogent_ty_to_hol (TVar i) = Term.list_comb (@{term TVar}, [HOLogic.mk_nat i])
  | cogent_ty_to_hol (TVarBang i) = Term.list_comb (@{term TVarBang}, [HOLogic.mk_nat i])
  | cogent_ty_to_hol (TCon { name, tyargs, sgl }) = Term.list_comb (@{term TCon}, [ HOLogic.mk_string name
                                                                                  , HOLogic.mk_list @{typ type} (map cogent_ty_to_hol tyargs)
                                                                                  , mk_sigil sgl
                                                                                  ])
  | cogent_ty_to_hol (TFun (t, u)) = Term.list_comb (@{term TFun}, [ cogent_ty_to_hol t
                                                                   , cogent_ty_to_hol u
                                                                   ])
  | cogent_ty_to_hol (TPrim pt) = Term.list_comb (@{term Prim}, [mk_prim_type pt])
  | cogent_ty_to_hol (TSum ts) = Term.list_comb (@{term TSum}, [ HOLogic.mk_list @{typ type} (map mk_variant_fields_elem ts) ])
  | cogent_ty_to_hol (TProduct (t1, t2)) = Term.list_comb (@{term TProduct}, [ cogent_ty_to_hol t1
                                                                             , cogent_ty_to_hol t2
                                                                             ])
  | cogent_ty_to_hol (TRecord { fs, sgl }) = Term.list_comb (@{term TRecord}, [ HOLogic.mk_list @{typ type} (map mk_record_fields_elem fs)
                                                                              , mk_sigil sgl
                                                                              ])
  | cogent_ty_to_hol (TUnit) = @{term TUnit}
and mk_record_fields_elem (n,t,tk) = HOLogic.mk_tuple [HOLogic.mk_string n, cogent_ty_to_hol t, mk_record_state tk]
and mk_variant_fields_elem (n,t,tk) = HOLogic.mk_tuple [HOLogic.mk_string n, cogent_ty_to_hol t, mk_variant_state tk]

fun typing_tac _ (ctxt : Proof.context) (Var i) =
      let val ci = Thm.cterm_of ctxt (HOLogic.mk_nat i)
       in Thm.instantiate ([],[((("i",0), HOLogic.natT),ci)]) @{thm typing_var}
      end
  | typing_tac fntable ctxt (Fun { name, tyargs }) =
      let val cts = Thm.cterm_of ctxt (HOLogic.mk_list deep_expr (map cogent_ty_to_hol tyargs))
       in case Symtab.lookup fntable name of
            SOME e => Thm.instantiate ([],[((("ts",0), @{typ "string expr list"}),cts),((("f",0), deep_expr),e)]) @{thm typing_fun}
          | NONE => let val cn = Thm.cterm_of ctxt (HOLogic.mk_string name)
                     in Thm.instantiate ([((("f",0),Type.defaultS Type.empty_tsig),Thm.ctyp_of ctxt HOLogic.stringT)],[((("ts",0), @{typ "string expr list"}),cts),((("f",0), HOLogic.stringT),cn)]) @{thm typing_afun}
                        (* TODO: this; Type.empty_tsig? *)
                    end
      end
  | typing_tac _ ctxt (Prim { oper, es })                      = undefined()
  | typing_tac _ ctxt (App (a, b))                             = undefined()
  | typing_tac _ ctxt (Con { altnm, vval, vtys })              = undefined()
  | typing_tac _ ctxt (Struct (ts, es))                        = undefined()
  | typing_tac _ ctxt (Member { er, idx })                     = undefined()
  | typing_tac _ ctxt (Unit)                                   = @{thm typing_unit}
  | typing_tac _ ctxt (Lit lit)                                = undefined()
  | typing_tac _ ctxt (SLit s)                                 = undefined()
  | typing_tac _ ctxt (Cast (pt, e))                           = undefined()
  | typing_tac _ ctxt (Tuple (e1,e2))                          = undefined()
  | typing_tac _ ctxt (Put { er, idx, ev })                    = undefined()
  | typing_tac _ ctxt (Let { ev, ek })                         = undefined()
  | typing_tac _ ctxt (LetBang { idxs, ev, ek })               = undefined()
  | typing_tac _ ctxt (Case { eval, altnm, ematch, enomatch }) = undefined()
  | typing_tac _ ctxt (Esac e)                                 = undefined()
  | typing_tac _ ctxt (If { econd, ektt, ekff })               = undefined()
  | typing_tac _ ctxt (Take { erec, idx, ek })                 = undefined()
  | typing_tac _ ctxt (Split { ep, ek })                       = undefined()
  | typing_tac _ ctxt (Promote (t, e))                         = undefined();
\<close>

ML \<open>
val x = typing_tac Symtab.empty @{context} (Fun { name = "foo", tyargs = [] });
\<close>

thm typing_fun

end