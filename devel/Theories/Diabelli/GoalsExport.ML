(*  Title:      GoalsExport.ML
    Author:     Matej Urbas

GoalsExport: exports (and imports) current proof goals using the XML format.
*)

signature GOALS_EXPORT =
sig
  (* Indicates that a general error occurred.

     The string describes the error in english. *)
  exception SD_ERROR of string

  (* Indicates a general error (also containing some other cause exceptions).

     The string describes the error in english. *)
  exception SD_GERROR of (string * exn list)


(*==============================================================================
  = Utility functions
  ============================================================================*)
  (* Returns a list of terms (corresponding to current subgoals in the current
     proof).
     
     @returns (terms, state)
     
       terms - the list of terms that correspond to the current subgoals.
       
       state - the proof state from which we have obtained the terms (this one
               itself has been obtained via `Toplevel.proof_of (Isar.state ())`).
               You can get the context from it via `Proof.context_of state`.
     
     @throws SD_ERROR if we cannot obtain the list of terms for any reason
                      (e.g.: not being in a proof etc.). *)
  val get_goal_terms: unit -> (term list * Proof.state)



(*==============================================================================
  = I3P Communication Routines
  ============================================================================*)

  (* Translates the current goals into spider diagrams and writes the
     translations to the common output via the `tracing` function.
     
     If a subgoal is successfully converted to a spider diagram, the following
     two lines will be printed through the `tracing` function:

        Line 1: < SNF | MLSNF >
        Line 2: [the string representation of the spider diagram]

     The first line indicates the original form of the formula. The second line
     is the actual string representation of the spider diagram.

     If the subgoal is not successfully converted, then only a single line is
     printed and it will contain the string "INVALID".

     *)
  val i3p_write_sds_goals: unit -> unit
  
  val replace_subgoal_tac: string -> Proof.context -> int -> tactic
  
  (* Replaces a subgoal with an arbitrary term.

     @param  1 the arbitrary formula with which to replace sugoal '@param 2'.

     @param  2 the subgoal (its number) we would like to replace.

     @param  3 the theorem. This argument is provided by the 'apply'
               mechanism (omit it when using apply), e.g.:

         apply (tactic {* MixR.make_subgoal_tac @{term "Trueprop True"} 1 *})
  *)
  val make_subgoal_tac: string -> Proof.context -> int -> thm -> thm Seq.seq
end




structure GoalsExport: GOALS_EXPORT =
struct




exception SD_ERROR of string;
exception SD_GERROR of (string * exn list);




(*==============================================================================
  = Utility functions
  ============================================================================*)

fun get_goal_terms _ =
  let
      val state = Isar.state ()
      val _ = if Toplevel.is_proof state then () else raise (SD_ERROR "Not inside a proof.")
      val proof = Toplevel.proof_of state
      val terms = Unsynchronized.ref []
      
      val _ = Seq.hd (Proof.apply
                         (Method.Basic
                             (fn ctx =>
                                SIMPLE_METHOD (fn thm => let val _ = (terms := Thm.prems_of thm) in all_tac thm end))
                         ) proof)
  in
      (!terms, proof)
  end;



(*==============================================================================
  = I3P Communication Routines
  ============================================================================*)
  
val _ = tracing "Something...";


val mixr_response_prefix   = "MixRResponse: ";
val mixr_response_goal     = "Goal: ";
val mixr_response_goal_str = "Goal string: ";
val mixr_response_no_goals = "No Goals: ";

fun i3p_write_sds_goals _ =
  let
      val (terms, proof_state) = get_goal_terms ();
      val context = Proof.context_of proof_state;
      (* This YXML shit works... But I have problems making it work for XML. *)
      fun print_yxml_term t = (PolyML.makestring (Term_XML.Decode.term [(YXML.parse (YXML.string_of (hd (Term_XML.Encode.term t))))]))
      fun print_term t = YXML.string_of_body (Term_XML.Encode.term t) |> YXML.embed_controls
      fun print_terms [] = ()
        | print_terms ((t:term) :: (ts:term list)) =
          let 
              val _ = tracing (mixr_response_prefix ^ mixr_response_goal ^ (print_term t));
              val _ = tracing (Syntax.string_of_term context t);
          in
              print_terms ts
          end;
  in
      case terms of
          [] => tracing (mixr_response_prefix ^ mixr_response_no_goals)
        | t => print_terms terms
  end;

fun mk_trueprop_if (t as (Const ("HOL.Trueprop", _) $ _)) = t
  | mk_trueprop_if (t as (Const ("==>", _) $ _ $ _)) = t
  | mk_trueprop_if (t as (Const ("all", _) $ _)) = t
  | mk_trueprop_if (t as (Const ("==", _) $ _ $ _)) = t
  | mk_trueprop_if t = HOLogic.mk_Trueprop t

fun replace_subgoal_tac formula ctxt i st = SUBGOAL (fn (subgoal, _) =>
   let

       val thy = Proof_Context.theory_of ctxt;
       val formulaTerm = Syntax.read_term_global thy formula
       val intert = Logic.mk_implies (mk_trueprop_if formulaTerm, subgoal)
       val _ = tracing ("Have " ^ Syntax.string_of_term @{context} intert)
       val intert_cterm = Thm.cterm_of thy intert
       val interThm = Goal.prove_internal [] intert_cterm (K ((auto_tac ctxt) THEN (ALLGOALS (Intuitionistic.prover_tac ctxt NONE))))
       val _ = tracing ("Interm: " ^ Display.string_of_thm @{context} interThm)
   in
       compose_tac (false, interThm, 1) i
   end) i st

(*==============================================================================
  = make_subgoal_tac
  ============================================================================*)

fun make_subgoal_tac formula ctxt i st = SUBGOAL (fn (subgoal, _) =>
   let
     val thy = Proof_Context.theory_of ctxt;
     val formulaTerm = Syntax.read_term_global thy formula
     val intert = Logic.mk_implies (mk_trueprop_if formulaTerm, subgoal)
     (*val thy = Thm.theory_of_thm st;*)
     val adhoc_rule = Skip_Proof.make_thm thy intert;
   in
     compose_tac (false, adhoc_rule, 1) i
   end) i st;


end