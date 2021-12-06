let __coq_plugin_name = "tuto1_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_tuto1.mlg"
 

(* If we forget this line and include our own tactic definition using
  TACTIC EXTEND, as below, then we get the strange error message
  no implementation available for Tacentries, only when compiling
  theories/Loader.v
*)
(* open Ltac_plugin *)
open Pp
(* This module defines the types of arguments to be used in the
   EXTEND directives below, for example the string one. *)
open Stdarg



let () = Vernacextend.vernac_extend ~command:"ExploreProof" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.VtReadProof (
                                                          
# 20 "src/g_tuto1.mlg"
    fun ~pstate ->
    (* let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) *)
   (* ; *)
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) ;

    let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
    Feedback.msg_notice (strbrk "State: " ++ debug sigma) ;

    let p: Proof.t = Declare.Proof.get pstate in
    Feedback.msg_notice (strbrk "Proof: " ++ (Proof.pr_proof p))


    (* let pprf = Proof.partial_proof (Declare.Proof.get_open_goals pstate) in *)
    (* let Declare.Proof.{ goals; stack; sigma } = Declare.Proof.data pstate in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) goals) *)
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                    Vernacextend.TyTerminal ("intro", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                    Vernacextend.TyNil))), (let coqpp_body i
                                                           () = Vernacextend.VtReadProof (
                                                                
# 44 "src/g_tuto1.mlg"
    fun ~pstate ->
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) ;

    let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
    Feedback.msg_notice (strbrk "State: " ++ debug sigma) ;

    let p: Proof.t = Declare.Proof.get pstate in
    Feedback.msg_notice (strbrk "Proof: " ++ (Proof.pr_proof p))
  
                                                                ) in fun i
                                                           ?loc ~atts ()
                                                           -> coqpp_body i
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                    Vernacextend.TyTerminal ("exists", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_nat), 
                                    Vernacextend.TyNil))), (let coqpp_body n
                                                           () = Vernacextend.VtReadProof (
                                                                
# 57 "src/g_tuto1.mlg"
    fun ~pstate ->
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) ;

    let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
    Feedback.msg_notice (strbrk "State: " ++ debug sigma) ;

    let p: Proof.t = Declare.Proof.get pstate in
    Feedback.msg_notice (strbrk "Proof: " ++ (Proof.pr_proof p))
  
                                                                ) in fun n
                                                           ?loc ~atts ()
                                                           -> coqpp_body n
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                    Vernacextend.TyTerminal ("unfold", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                    Vernacextend.TyNil))), (let coqpp_body i
                                                           () = Vernacextend.VtReadProof (
                                                                
# 70 "src/g_tuto1.mlg"
    fun ~pstate ->
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) ;

    let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
    Feedback.msg_notice (strbrk "State: " ++ debug sigma) ;

    let p: Proof.t = Declare.Proof.get pstate in
    Feedback.msg_notice (strbrk "Proof: " ++ (Proof.pr_proof p))
  
                                                                ) in fun i
                                                           ?loc ~atts ()
                                                           -> coqpp_body i
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                    Vernacextend.TyTerminal ("ring", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.VtReadProof (
                                                          
# 83 "src/g_tuto1.mlg"
    fun ~pstate ->
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf) ;

    let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
    Feedback.msg_notice (strbrk "State: " ++ debug sigma) ;

    let p: Proof.t = Declare.Proof.get pstate in
    Feedback.msg_notice (strbrk "Proof: " ++ (Proof.pr_proof p))
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

