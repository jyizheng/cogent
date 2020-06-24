(*
This file is generated by Cogent

*)

theory Generated_MonoProof
imports "Cogent.Mono_Tac"
"Generated_TypeProof"
"Generated_Deep_Normal"
begin

definition
  rename__assocs :: "(( string \<times>  Cogent.type list) \<times>  string) list"
where
  "rename__assocs \<equiv> [((''dec'', Nil), ''dec''), ((''dec_arr'', Nil), ''dec_arr''), ((''inc'', Nil), ''inc''), ((''inc_arr'', Nil), ''inc_arr''), ((''mul'', Nil), ''mul''), ((''mul_arr'', Nil), ''mul_arr''), ((''sum'', Nil), ''sum''), ((''sum_arr'', Nil), ''sum_arr''), ((''wordarray_fold_no_break'', [TPrim (Num U32), TPrim (Num U32), TUnit]), ''wordarray_fold_no_break_0''), ((''wordarray_get'', [TPrim (Num U32)]), ''wordarray_get_0''), ((''wordarray_get_u32'', Nil), ''wordarray_get_u32''), ((''wordarray_length'', [TPrim (Num U32)]), ''wordarray_length_0''), ((''wordarray_length_u32'', Nil), ''wordarray_length_u32''), ((''wordarray_map_no_break'', [TPrim (Num U32), TUnit, TUnit]), ''wordarray_map_no_break_0''), ((''wordarray_put2'', [TPrim (Num U32)]), ''wordarray_put2_0''), ((''wordarray_put2_u32'', Nil), ''wordarray_put2_u32'')]"

local_setup \<open>
gen_mono_rename Cogent_functions @{thm rename__assocs_def} "rename"
\<close>


context value_sem begin

ML \<open>
local
  (* Get mono-to-poly mapping from the assoc-list for @{term rename} *)
  val rename_inverse =
    Thm.prop_of @{thm rename__assocs_def}
    |> Logic.dest_equals |> snd
    |> HOLogic.dest_list
    |> map (HOLogic.dest_prod #> apfst HOLogic.dest_prod)
    |> map (fn ((poly_f, typs), mono_f) => (HOLogic.dest_string mono_f, (HOLogic.dest_string poly_f, typs)))
    |> Symtab.make
  val poly_thy = "Generated_Deep_Normal"
  val mono_thy = "Generated_TypeProof"
  val abbrev_defs = maps (fn thy => Proof_Context.get_thms @{context} (thy ^ ".abbreviated_type_defs"))
                      [poly_thy, mono_thy]
  val rename_simps = Proof_Context.get_thms @{context} "rename_simps"
                     handle ERROR _ => []
in
val monoexpr_thms =
  fold (fn f => fn callees =>
          gen_monoexpr_thm poly_thy mono_thy @{term rename} rename_inverse callees f
                           (abbrev_defs @ rename_simps) @{context}
          :: callees)
       (* NB: here "Cogent_functions" must refer to the list of *monomorphic* Cogent functions.
        *     Obtain it by importing the TypeProof theory before the Deep_Normal theory.
        * FIXME: we should assign the poly and mono function lists to distinct names. *)
       Cogent_functions []
  |> (fn thms => Symtab.make (Cogent_functions ~~ rev thms))
end
\<close>


end

end
