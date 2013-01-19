theory IsaDia
imports Main
uses
  "GoalsExport.ML"
begin

method_setup mixr = {*
(fn xs => let
          in
              ((Scan.lift (Parse.string)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (GoalsExport.replace_subgoal_tac args ctxt))))) xs
          end)
*} "This tactic takes the subgoal 'A' (the only argument), tries to prove 'A ==> B', where 'B' is the first goal, and replaces 'A' with 'B'."

method_setup mixrOracle = {*
(fn xs => let
          in
              ((Scan.lift (Parse.string)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (GoalsExport.make_subgoal_tac args ctxt))))) xs
          end)
*} "This tactic takes the subgoal 'A' (the only argument), and replaces 'A' with 'B'."

typedecl mixr_var
consts
  About :: "'a list \<Rightarrow> mixr_var"

consts
  MixRVars :: "mixr_var list \<Rightarrow> string \<Rightarrow> bool"
  MixR :: "string \<Rightarrow> bool"

end