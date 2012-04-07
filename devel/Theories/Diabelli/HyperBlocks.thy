theory HyperBlocks
imports
  Main
uses
  "$ISABELLE_HOME/src/Pure/Concurrent/bash_sequential.ML"
  "diabelli.ML"
begin

method_setup sd_tac = {*
(fn xs => let
              fun get_option ((oname, _), oval) = (oname, oval)
              fun get_sdi xs = ((Args.$$$ "sdi" -- Args.colon -- Parse.number) >> get_option) xs
              fun get_sp xs = ((Args.$$$ "sp" -- Args.colon -- Parse.string) >> get_option) xs
              fun get_r xs = ((Args.$$$ "r" -- Args.colon -- Parse.string) >> get_option) xs
              fun get_args xs = (Scan.repeat (Scan.first [get_sdi, get_sp, get_r])) xs
              fun get_rule_and_args xs = (Parse.short_ident -- get_args >> (fn (rule, args) => ("ir", rule)::args)) xs
          in
              ((Scan.lift (get_rule_and_args)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (Diabelli.sd_tac args ctxt))))) xs
          end)
*} "A no-op tactic for testing the translation from SNF to spider diagrams and communication with Speedith."

lemma our: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
  apply (rule impI)
  apply (rule conjI)
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac idempotency sdi: 1)
  apply (sd_tac implication_tautology sdi: 0)
  by auto

lemma "Diabelli(''hyperblocks'', ''data'') \<Longrightarrow> Tet(a)"
  apply (tactic {* Diabelli.make_subgoal_tac @{term "Tet(a) \<Longrightarrow> Tet(a)"} 1 *})
  by auto
end