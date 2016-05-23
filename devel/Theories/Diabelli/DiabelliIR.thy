(*
     Title:   MixRIR.ML
    Author:   Matej Urbas

MixRIR:   provides a formalisation of the data structure used as the
              intermediate represenation.

              This record is fed the diagrammatic reasoner on the ML level. The
              external diagrammatic reasoner returns a transformed record,
              which can be directly translated to Isabelle formulae via the
              provided interpretation functions (these are named
              'sd_<name>_sem').
*)

theory MixRIR
imports
  Main
  "~~/src/HOL/Library/Permutation"
uses
  ("mixr.ML")
  "$ISABELLE_HOME/src/Pure/Concurrent/bash_sequential.ML"
  "GoalsExport.ML"
begin




(*==============================================================================
DATATYPE DEFINITIONS
==============================================================================*)


(*
  sd_zone and sd_region are the types used to encode zones and regions as
  defined in the theory of spider diagarms.
*)
type_synonym 'e sd_zone = "'e set set * 'e set set"
type_synonym 'e sd_region = "'e sd_zone set"


(*
  'sd' is the main data structure. It describes any compound spider diagram.
  It serves as the formalisation of the intermediate represenatition for
  communicating formulae between the external diagrammatic reasoner and
  Isabelle.

  A record of this data structure is interpreted by functions
  'sd_<name>_sem'.
*)
datatype ('s)sd =
    PrimarySD "'s sd_region list" "'s sd_zone set"
  | UnarySD "bool \<Rightarrow> bool" "('s)sd"
  | BinarySD "bool \<Rightarrow> bool \<Rightarrow> bool" "('s)sd" "('s)sd"
  | NullSD




(*==============================================================================
INTERPRETATION FUNCTIONS
==============================================================================*)


(*
  sd_zone_sem defines the semantics of a zone (an interpretation of
  'sd_zone').
*)
fun sd_zone_sem :: "'e sd_zone \<Rightarrow> 'e set"
  where
  "sd_zone_sem (in_sets, out_sets) = (\<Inter> in_sets) - (\<Union> out_sets)"


(*
  sd_region_sem defines the semantics of a region (an interpretation of
  'sd_region').
*)
fun sd_region_sem :: "'e sd_region \<Rightarrow> 'e set"
  where
  "sd_region_sem zones = (\<Union> z \<in> zones. sd_zone_sem z)"


(*
  The following function defines the base-case of the interpretation function
  for the primary spider diagram. It says that all the mentioned spiders are
  distinct and that shaded zones can contain only spiders. If the shaded zones
  actually contain spiders is determined by the spiders' habitats (defined in
  psd_sem_impl).
*)
fun psd_sem_impl_base :: "'s sd_zone set \<Rightarrow> 's list \<Rightarrow> bool"
  where
  "psd_sem_impl_base sh_zones spiders = (distinct spiders \<and> (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> set spiders. s = el))"


(*
  The helper implementation =of the primary spider diagram interpretation
  function. The reason for this additional function (instead of having just a
  single one) is that it accumulates spiders as it recurses down habitats. This
  means that it has an additional parameter, which should be empty when called
  from the user-facing main function.
*)
fun psd_sem_impl :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> 's list \<Rightarrow> bool"
  where
  "psd_sem_impl [] sh_zones spiders = psd_sem_impl_base sh_zones spiders"
  | "psd_sem_impl (h#hs) sh_zones spiders = (\<exists>s. s \<in> sd_region_sem h \<and> psd_sem_impl hs sh_zones (s#spiders))"


(*
  The main interpretation function for the primary (unitary) spider diagram.
*)
fun psd_sem :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> bool"
  where
  "psd_sem habitats sh_zones = psd_sem_impl habitats sh_zones []"


(*
  The main interpretation function for the primary (unitary) spider diagram.
*)
fun usd_sem :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> 's list \<Rightarrow> bool"
  where
  "usd_sem [] sh_zones spiders = (distinct spiders \<and> (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> set spiders. s = el))"
  | "usd_sem (h#hs) sh_zones spiders = (\<exists>s. s \<in> sd_region_sem h \<and> usd_sem hs sh_zones (s#spiders))"


(*
  sd_sem provides an interpretation of the main data structure 'sd'. In
  fact, this function provides the semantic of the entire language of spider
  diagrams (as encoded by the 'sd' data type).
*)
fun sd_sem :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem (PrimarySD habitats sh_zones) = psd_sem habitats sh_zones"
  | "sd_sem (UnarySD P sd) = (P (sd_sem sd))"
  | "sd_sem (BinarySD P sdl sdh) = (P (sd_sem sdl) (sd_sem sdh))"
  | "sd_sem NullSD = True"




(*==============================================================================
LEMMATA SUPPORTING THE INTERPRETATION FUNCTIONS
==============================================================================*)


(*
  Show that the base case of the PSD interpretation function implies that shaded
  zones are actually subsets of spiders.
*)
lemma psd_base_sh_zones_subsets: "psd_sem_impl_base sh_zones spiders \<Longrightarrow>
                                  (\<forall>z \<in> sh_zones. sd_zone_sem z \<subseteq> set spiders)"
  by auto


(*
    Also provide an equivalent definition of the base case of the PSD
    interpretation using the built-in subset relation.
*)
lemma psd_base_sh_zones_subsets_eq: "psd_sem_impl_base sh_zones spiders =
                                     ((\<forall>z \<in> sh_zones. sd_zone_sem z \<subseteq> set spiders) \<and> distinct spiders)"
  by auto


(*
    Say we are given a list of distinct spiders (with arbitrary habitats) and
    some shaded zones. Then the corresponding primary spider diagram entails
    a primary spider diagram with another fresh spider.
*)
lemma psd_base_insert_spider: "psd_sem_impl_base sh_zones spiders \<Longrightarrow>
                               psd_sem_impl_base sh_zones (List.insert sp spiders)"
  by fastsimp


(*
    We can remove spiders if there are no shaded zones in the primary diagram.
*)
lemma psd_remove_spiders: "\<And>f. psd_sem_impl habs {} spiders \<Longrightarrow>
                               psd_sem_impl habs {} (sublist spiders f)"
proof (induct habs arbitrary: spiders f)
  case Nil thus ?case by force
next
  case (Cons hab habs f spiders) note ind_hyp = Cons(1) and prem = Cons(2)
  then obtain s f' where s_in: "s \<in> sd_region_sem hab"
    and psd: "psd_sem_impl habs {} (s # spiders)"
    and new_f: "f' = {j. j > 0 \<longrightarrow> (j - 1) \<in> f}"
    by auto
  have new_sub_lists: "s # (sublist spiders f) = sublist (s # spiders) f'" using new_f
    by (auto simp add: sublist_Cons)
  thus ?case using s_in psd prem ind_hyp
    by auto
qed


(*
    Part of the inference inference: remove shaded zone

    If we remove a shaded zone from a primary spider diagram \<phi>, we get a new
    PSD \<psi>, where \<phi> entails \<psi>.
*)
lemma psd_base_remove_sh_zone: "psd_sem_impl_base (insert z sh_zones) spiders \<Longrightarrow>
                                psd_sem_impl_base sh_zones spiders"
  by fastsimp


(*
    An empty spider diagram is a tautology.
*)
lemma psd_empty: "psd_sem [] {} = True"
  by force


(*
    We can change the order of spiders without changing the meaning of the
    primary diagram.
*)
lemma psd_permute_spiders: "\<lbrakk> perm spiders spiders' \<rbrakk> \<Longrightarrow>
                            (psd_sem_impl habs sh_zones spiders =
                            psd_sem_impl habs sh_zones spiders')"
proof (induct habs arbitrary: spiders spiders')
  case Nil thus ?case by (simp add: perm_set_eq perm_distinct_iff)
next
  case (Cons h habs)
  note ind_hyp = Cons(1)
  note perm = Cons(2)
  (*from perm have "\<And>s. s # spiders <~~> s # spiders'" by fast*)
  with ind_hyp have "\<And>s. psd_sem_impl habs sh_zones (s # spiders) =
            psd_sem_impl habs sh_zones (s # spiders')"
    by simp
  thus ?case by force
qed


(*
    The order of habitats in the list also does not matter.
*)
lemma psd_permute_habs: "\<lbrakk> perm habs habs'; psd_sem_impl habs sh_zones spiders \<rbrakk> \<Longrightarrow>
                           psd_sem_impl habs' sh_zones spiders"
proof (induct arbitrary: spiders pred: perm)
  case Nil thus ?case by fast
next
  case trans thus ?case by fast
next
  case (swap h h' habs)
  then obtain s s' where s_in: "s \<in> sd_region_sem h"
                     and s'_in: "s' \<in> sd_region_sem h'"
                     and psd: "psd_sem_impl habs sh_zones (s' # s # spiders)" 
     by auto

  have "(s' # s # spiders) <~~> (s # s' # spiders)" by fast
  with psd have psd': "psd_sem_impl habs sh_zones (s # s' # spiders)"
    using psd_permute_spiders by fast

  from s_in s'_in psd' show ?case by auto
next
  case (Cons habs habs' hab)
  thus ?case by auto
qed


(*
    Finally, we show the above for the main psd_sem interpretation function.
*)
lemma psd_permute_habitats: "\<lbrakk> perm habs habs'; psd_sem habs sh_zones \<rbrakk> \<Longrightarrow>
         psd_sem habs' sh_zones"
  by (simp add: psd_permute_habs)


(*
    We can remove arbitrary habitats and/or spiders if there are no shaded zones.
*)
lemma psd_remove_habitat_spider: "psd_sem_impl habs {} spiders \<Longrightarrow>
                                  psd_sem_impl (sublist habs f) {} (sublist spiders g)"
proof (induct habs arbitrary: spiders f g)
  case Nil thus ?case by force
next
  case (Cons hab habs spiders f g) note ind_hyp = Cons(1) and prem = Cons(2)
  thus ?case
  proof (case_tac "0 \<in> f")
    assume "0 \<in> f"
    hence f_sublist: "sublist (hab # habs) f = hab # sublist habs {i. Suc i \<in> f}"
      by (auto simp add: sublist_Cons)
    then obtain s g' where s_in: "s \<in> sd_region_sem hab"
      and psd: "psd_sem_impl habs {} (s # spiders)"
      and new_g: "g' = {j. j > 0 \<longrightarrow> (j - 1) \<in> g}"
      using prem ind_hyp by auto
    have "s # (sublist spiders g) = sublist (s # spiders) g'" using new_g
      by (auto simp add: sublist_Cons)
    thus ?thesis using ind_hyp prem s_in psd f_sublist
      by auto
  next
    assume "0 \<notin> f"
    hence f_sublist: "sublist (hab # habs) f = sublist habs {i. Suc i \<in> f}"
      by (auto simp add: sublist_Cons)
    then obtain s g' where s_in: "s \<in> sd_region_sem hab"
      and psd: "psd_sem_impl habs {} (s # spiders)"
      and new_g: "g' = {j. if j = 0 then False else j - 1 \<in> g}"
      using prem ind_hyp by auto
    hence "sublist spiders g = sublist (s # spiders) g'"
      by (auto simp add: sublist_Cons)
    thus ?thesis using ind_hyp prem psd f_sublist new_g s_in
      by force
  qed
qed




(*==============================================================================
SPIDER DIAGRAMMATIC INFERENCE RULES FORMALISATION
==============================================================================*)


(*
    Inference inference: Remove habitat

    If there are no shaded zones, then we can remove arbitrary habitats.
*)
lemma psd_remove_habitats: "psd_sem habs {} \<Longrightarrow>
                           psd_sem (sublist habs f) {}"
  by (simp, drule psd_remove_habitat_spider[of habs Nil f g], auto)


(*
    Inference inference: Add feet
*)
lemma psd_add_feet: "\<lbrakk> psd_sem (h#habs) sh_zones; h \<subset> h' \<rbrakk> \<Longrightarrow> psd_sem (h'#habs) sh_zones"
  by auto


(*
    A formalisation of the first version of the 'add feet' inference inference (i.e.:
    t(A) \<longrightarrow> \<psi> \<turnstile> A \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (PrimarySD (h'#hs) shzs) \<psi>) \<rbrakk> \<Longrightarrow>
                         sd_sem (BinarySD (op -->) (PrimarySD (h#hs) shzs) \<psi>)"
  by auto


(*
    A formalisation of the second version of the 'add feet' inference inference (i.e.:
    t(A) \<and> \<phi> \<longrightarrow> \<psi> \<turnstile> A \<and> \<phi> \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet_con: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (BinarySD (op &) (PrimarySD (h'#hs) shzs) \<phi>) \<psi>) \<rbrakk> \<Longrightarrow>
                             sd_sem (BinarySD (op -->) (BinarySD (op &) (PrimarySD (h#hs) shzs) \<phi>) \<psi>)"
  by auto


(*
    A formalisation of the third version of the 'add feet' inference inference (i.e.:
    t(A) \<or> \<phi> \<longrightarrow> \<psi> \<turnstile> A \<or> \<phi> \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet_disj: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (BinarySD (op \<or>) (PrimarySD (h'#hs) shzs) \<phi>) \<psi>) \<rbrakk> \<Longrightarrow>
                              sd_sem (BinarySD (op -->) (BinarySD (op \<or>) (PrimarySD (h#hs) shzs) \<phi>) \<psi>)"
  by auto


(*
    A formalisation of the 'split spider' inference inference:

        A \<longleftrightarrow> t_{h, habA}(A, spider) \<or> t_{h, habB}(A, spider)

    Note: this thing differs from what Gem did. I should prove it sound, present
    why is it different and why it is still sound.
*)
lemma sd_rule_split_spiders: "\<lbrakk> habs = (h#hs); habA \<union> habB = h \<rbrakk> \<Longrightarrow>
                              sd_sem (PrimarySD habs shzs) =
                              (sd_sem (PrimarySD (habA#hs) shzs) \<or>
                              sd_sem (PrimarySD (habB#hs) shzs))"
  by auto


(*
    A formalisation of the 'split spider' inference inference---using the BinarySD
    data structure.
*)
lemma sd_rule_split_spiders_B: "\<lbrakk> habs = (h#hs); habA \<union> habB = h \<rbrakk> \<Longrightarrow>
                                sd_sem (PrimarySD habs shzs) =
                                sd_sem (BinarySD (op \<or>)
                                           (PrimarySD (habA#hs) shzs)
                                           (PrimarySD (habB#hs) shzs))"
  by auto

(*lemma sd_rule_excluded_middle: "\<lbrakk> h \<inter> shzs = {}; psd_sem habs shzs \<rbrakk> \<Longrightarrow> (psd_sem habs (h \<union> shzs)) \<or> psd_sem (h#habs) shzs"
apply (auto simp del: sd_region_sem.simps)*)


(*ML {* @{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"} *}
ML {* @{term "True"} *}
ML {* #3 ("dsa", 5, SOME 1) *}
ML {* eq_list op= ((sort_distinct string_ord [ "c", "a", "a", "k", "b" ]), (sort_distinct string_ord [ "k", "c", "a", "b" ])) *}*)

ML {* print_depth 100 *}
ML {* Config.put show_brackets true *}




(*==============================================================================
DIABELLI SETUP (ML-level translation, communication, and tactics procedures)
==============================================================================*)


use "mixr.ML"


(* ML {* MixR.print_subgoals () *} *)

method_setup sd_tac = {*
(fn xs => let
              fun get_option ((oname, _), oval) = (oname, oval)
              fun get_sdi xs = ((Args.$$$ "sdi" -- Args.colon -- Parse.number) >> get_option) xs
              fun get_sp xs = ((Args.$$$ "sp" -- Args.colon -- Parse.string) >> get_option) xs
              fun get_r xs = ((Args.$$$ "r" -- Args.colon -- Parse.string) >> get_option) xs
              fun get_args xs = (Scan.repeat (Scan.first [get_sdi, get_sp, get_r])) xs
              fun get_rule_and_args xs = (Parse.short_ident -- get_args >> (fn (inference, args) => ("ir", inference)::args)) xs
          in
              ((Scan.lift (get_rule_and_args)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (MixR.sd_tac args ctxt))))) xs
          end)
*} "Applies spider-diagrammatic inference rules on the first subgoal."

method_setup mixr = {*
(fn xs => let
          in
              ((Scan.lift (Parse.string)) >> (fn args => (fn ctxt => (Method.SIMPLE_METHOD' (GoalsExport.replace_subgoal_tac args ctxt))))) xs
          end)
*} "This tactic takes the formula 'A' (the only argument), tries to prove 'A ==> B', where 'B' is the first goal, and replaces 'A' with 'B'."



(*lemma testB: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (auto simp del: distinct.simps)
  ML_prf {* MixR.get_goal_terms () *}
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac idempotency sdi: 1)
  by auto*)

lemma example: "\<exists>s. s \<in> (A - B) \<union> (B - A) \<and> (A \<inter> B) = {}"
  oops

lemma step1: "\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> A - B \<union> (B - A) \<Longrightarrow>
    (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B) \<and> A \<inter> B \<noteq> {}"
  oops

lemma step2: "\<And>s1 s2. \<lbrakk>distinct [s1, s2]; s1 \<in> A \<inter> B; s2 \<in> A - B \<union> (B - A)\<rbrakk>
            \<Longrightarrow> (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B) \<and> A \<inter> B \<noteq> {}"
  oops

lemma step3A: "\<And>s1 s2. \<lbrakk>s1 \<noteq> s2; s1 \<in> A \<and> s1 \<in> B; s2 \<in> A \<and> s2 \<notin> B \<or> s2 \<in> B \<and> s2 \<notin> A\<rbrakk> \<Longrightarrow> \<exists>s1 s2. s1 \<noteq> s2 \<and> s1 \<in> A \<and> s2 \<in> B"
  oops
lemma step3B: "\<And>s1 s2. \<lbrakk>distinct [s1, s2]; s1 \<in> A \<inter> B; s2 \<in> A - B \<union> (B - A)\<rbrakk> \<Longrightarrow> A \<inter> B \<noteq> {}"
  oops

lemma testC: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
  apply (inference impI)                                           (* Implication introduction *)
  apply (erule exE | erule conjE)+                            (* Repeated existential and conjunction elimination *)
  apply (inference conjI, simp)                                    (* Conjunction introduction and simplification of sets *)
  apply (erule conjE | erule disjE)+                          (* Repeated conjunction and disjunction elimination *)
  apply (rule_tac x = "s2" in exI, rule_tac x = "s1" in exI)  (* Existential introduction with instantiation of spiders *)
  apply (fast)                                                (* Proves the goal from the assumptions. *)
  apply (rule_tac x = "s1" in exI, rule_tac x = "s2" in exI)  (* Existential introduction with instantiation of spiders *)
  apply (fast)                                                (* Proves the goal from the assumptions. *)
  by blast                                                    (* Proves that A \<inter> B is not empty *)

lemma our: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
(*apply auto*)
(*  apply (auto simp del: distinct.simps)*)
  apply (inference impI)
  apply (inference conjI)
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (mixr "(EX s1 s2. distinct[s1, s2] & s1 : (A Int B) Un (B - A) & s2 : (A - B) Un (A Int B)) | (EX s1 s2. distinct[s1, s2] & s1 : (A - B) Un (A Int B) & s2 : B - A) --> (EX t1 t2. distinct[t1, t2] & t1 : (A - B) Un (A Int B) & t2 : (A Int B) Un (B - A))")
apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac idempotency sdi: 1)
  apply (sd_tac implication_tautology sdi: 0)
  by auto

lemma example1: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
  apply (inference impI)
  apply (inference conjI)
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac idempotency sdi: 1)
  apply (sd_tac implication_tautology sdi: 0)
  by (auto)




(* This lemma should land in the unit tests. *)
lemma testA: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac idempotency sdi: 1)
  apply (sd_tac implication_tautology sdi: 0)
  by simp



(*ML {* MixR.from_snf_to_sd @{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"} *}
ML {* MixR.random_tests "tralala" *}
ML {* Outer_Syntax.scan Position.none "split_spiders sdi: 0 sp: sp1 r: \"[([\\\"A\\\"],[\\\"B\\\"])]\"" *}
ML {* Method.print_methods @{theory} *}*)

(*lemma intermediateA: "(\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A - B \<union> A \<inter> B \<and> s2 \<in> A \<inter> B \<union> (B - A)) \<longrightarrow>
                      (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B) \<Longrightarrow>
                      (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<inter> B \<union> (B - A) \<and> s2 \<in> A - B \<union> A \<inter> B) \<or>
                      (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A - B \<union> A \<inter> B \<and> s2 \<in> A \<inter> B \<union> (B - A)) \<longrightarrow>
                      (\<exists>s1 s2. distinct [s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply auto
  apply iprover
  apply iprover
  by iprover*)

(*ML {* MixR.exec_args "echo" [ "My name is matej.", "T\\h$is \"is\" a 'treat'.", "And a \n newline.", PolyML.makestring (MixR.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"}))] *}
ML {* MixR.exec_args (getenv "DIABELLI_JAVA_PATH") [ "-jar", getenv "DIABELLI_SPEEDITH_PATH", "-sd", PolyML.makestring (MixR.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"})) ] *}
ML {* getenv "DIABELLI_JAVA_PATH" *}
ML {* MixR.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"}); *}*)


(*ML {* MixR.random_tests (MixR.bash_escape (PolyML.makestring (MixR.from_term_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"})))) *}*)
(*ML {* MixR.random_tests (MixR.bash_escape (PolyML.makestring { one = 1, two = "some", mega = SOME 1, three = NONE})) *}*)

end
