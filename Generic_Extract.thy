(*  Title:      Generic_Extract.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

theory Generic_Extract imports
  Generic_Interpretation SingleInstruction_CFG
begin

(* Actually write the file to disk *)

export_code open
  set sorted_list_of_set RBT.fold
  si_wf_disj_cfg_wf gen_ssa_cfg_wf gen_wf_var gen_ssa_wf_notriv_substAll' gen_ssa_wf_ssa_defs
  in OCaml module_name BraunSSA file "compcertSSA/midend/SSA/BraunSSA.ml"

end
