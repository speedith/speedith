theory IsaDia
imports Main
uses
  "GoalsExport.ML"
begin

method_setup diabelli = {*
(fn xs => let
          in
              ((Scan.lift (Parse.string)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (GoalsExport.replace_subgoal_tac args ctxt))))) xs
          end)
*} "This tactic takes the subgoal 'A' (the only argument), tries to prove 'A ==> B', where 'B' is the first goal, and replaces 'A' with 'B'."

method_setup diabelliOracle = {*
(fn xs => let
          in
              ((Scan.lift (Parse.string)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (GoalsExport.make_subgoal_tac args ctxt))))) xs
          end)
*} "This tactic takes the subgoal 'A' (the only argument), and replaces 'A' with 'B'."

typedecl diabelli_var
consts
  About :: "'a list \<Rightarrow> diabelli_var"

consts
  DiabelliVars :: "diabelli_var list \<Rightarrow> string \<Rightarrow> bool"
  Diabelli :: "string \<Rightarrow> bool"

end