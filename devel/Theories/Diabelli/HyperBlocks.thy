theory HyperBlocks
imports
  Main
uses
  "GoalsExport.ML"
begin

lemma "Diabelli(''hyperblocks'', ''data'') \<Longrightarrow> Tet(a) \<and> Tet(b)"
  apply (rule conjI)
  ML_prf {* GoalsExport.get_goal_terms () *}
  ML_prf {* GoalsExport.i3p_write_sds_goals () *}
  apply (tactic {* Diabelli.make_subgoal_tac @{term "Tet(a) \<Longrightarrow> Tet(a)"} 1 *})
  by auto
end