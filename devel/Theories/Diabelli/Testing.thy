theory Testing
imports
  Main
uses
  ("diabelli.ML")
begin

use "diabelli.ML"


lemma testA: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply auto
  ML_prf {* Diabelli.get_goal_terms () *}

lemma l1: "\<lbrakk> P \<longrightarrow> Q; P \<rbrakk> \<Longrightarrow> Q \<and> P"
  apply (rule conjI)
  ML_prf {* Diabelli.get_goal_terms () *}
  ML_prf {* Diabelli.get_goal_terms () *}
ML_prf {* Isar_Cmd.diag_state () *}
(*ML_prf {*
let
  val ctx = @{context}
  val ctxt = (case (Context.thread_data ()) of
                  SOME (Context.Proof pctx) => pctx
                | _ => raise (ERROR  "Could not get the proof context. Are you inside a proof?"))
  val _ = tracing "is this tracing? or is this love?"
  val proof = Proof.begin_notepad ctx;
  val _ = tracing (PolyML.makestring (proof))
  val res = Unsynchronized.ref (Free("NOT_SET",dummyT))
  open Method
  (* Proof.get_goal is private in Isabelle2011 - work around this *)
  val _ = Seq.hd (Proof.apply (Basic (fn ctx =>
                                        SIMPLE_METHOD (SUBGOAL (fn (t,i) => (res := t; all_tac)) 1))) proof)
  in
               tracing (Pretty.string_of (Pretty.chunks
                        [ Pretty.str "quick display of first goal",
                          Pretty.str "",
                          Syntax.pretty_term ctx (!res) ]))
  end *}*)
pr
ML_prf {*
           val state = Isar.state ();
           if Toplevel.is_proof state then
             let
               val _ = tracing "SHIIIIIT!"
               val proof = Toplevel.proof_of state
               val ctx = Proof.context_of proof
               val res = Unsynchronized.ref NONE
               open Method
               (* Proof.get_goal is private in Isabelle2011 - work around this *)
               val _ = Seq.hd (Proof.apply (Basic (fn ctx =>
                               SIMPLE_METHOD (SUBGOAL (fn (t,i) => (res := (SOME t);
                               all_tac)) 1))) proof)
               val sgoal = case !res of NONE => raise (ERROR "Could not get the subgoal") | SOME t => t;
               val _ = tracing (PolyML.makestring (sgoal));
             in
               tracing (Pretty.string_of (Pretty.chunks
                        [ Pretty.str "quick display of first goal",
                          Pretty.str "",
                          Syntax.pretty_term ctx (sgoal) ]))
             end
             handle exn =>
               if Exn.is_interrupt exn
               then reraise exn
               else Toplevel.print_state false state
           else tracing "SHIIIIIT NO PROOF!"
           *}
  by simp

end
