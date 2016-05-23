theory HyperBlocks
imports
  Main
uses
  "GoalsExport.ML"
begin

lemma "\<And> B a b. \<lbrakk> A; B; MixR(''hyperblocks'', ''data''); C \<rbrakk> \<Longrightarrow> Tet(a) \<and> Tet(b)"
  apply (inference conjI)
  ML_prf {* GoalsExport.get_goal_terms () *}
  ML_prf {* GoalsExport.i3p_write_sds_goals () *}
  (*apply (tactic {* GoalsExport.make_subgoal_tac @{term "Tet(a) \<Longrightarrow> Tet(a)"} 1 *})*)
  oops



lemma our: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
(*apply auto*)
(*  apply (auto simp del: distinct.simps)*)
  apply (inference impI)
  apply (inference conjI)
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac idempotency sdi: 1)
  apply (sd_tac implication_tautology sdi: 0)
  by auto

end
