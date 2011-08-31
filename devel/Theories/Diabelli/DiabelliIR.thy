(*
     Title:   DiabelliIR.ML
    Author:   Matej Urbas

DiabelliIR:   provides a formalisation of the data structure used as the
              intermediate represenation.

              This record is fed the diagrammatic reasoner on the ML level. The
              external diagrammatic reasoner returns a transformed record,
              which can be directly translated to Isabelle formulae via the
              provided interpretation functions (these are named
              'sd_<name>_sem').
*)

theory DiabelliIR
imports
  Main
uses
  ("diabelli.ML")
  "$ISABELLE_HOME/src/Pure/Concurrent/bash_sequential.ML"
begin

(*  We still have some outstanding proofs. *)
ML {* quick_and_dirty := true *}




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
  Another take on the interpretation function of the primary spider diagram.
*)
fun psd_sem2_habs_f :: "('s \<times> 's sd_region) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "psd_sem2_habs_f (spider, habitat) others = (spider \<in> sd_region_sem habitat \<and> others)"

fun psd_sem2_habs :: "('s \<times> 's sd_region) list \<Rightarrow> bool"
  where
  "psd_sem2_habs sp_habs = foldr psd_sem2_habs_f sp_habs True"

fun psd_sem2_habs2 :: "('s \<times> 's sd_region) list \<Rightarrow> bool"
  where
  "psd_sem2_habs2 [] = True"
  | "psd_sem2_habs2 ((spider, habitat)#sp_habs) = (spider \<in> sd_region_sem habitat \<and> psd_sem2_habs2 sp_habs)"

fun psd_sem2_sh_zones :: "'s list \<Rightarrow> 's sd_zone set \<Rightarrow> bool"
  where
  "psd_sem2_sh_zones spiders sh_zones = (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> set spiders. s = el)"

fun psd_sem2 :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> bool"
  where
  "psd_sem2 habitats sh_zones = (\<exists>spiders.
          distinct spiders \<and>
          size spiders = size habitats \<and>
          psd_sem2_habs (zip spiders habitats) \<and>
          psd_sem2_sh_zones spiders sh_zones)"

lemma "psd_sem2 [{({A, B},{})}, {({A}, {B}),({B}, {A})}] {} = (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))"
  apply auto
  prefer 2
  apply (rule_tac x = "[s1, s2]" in exI)
  apply simp
  prefer 2
  sorry



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
    interpretation using the subset relation.
*)
lemma psd_base_sh_zones_subsets_eq: "psd_sem_impl_base sh_zones spiders =
                                     ((\<forall>z \<in> sh_zones. sd_zone_sem z \<subseteq> set spiders) \<and> distinct spiders)"
  by auto

(*
    Part of the inference rule: insert spider

    Say we are given a list of distinct spiders (with arbitrary habitats) and
    some shaded zones. Then the corresponding primary spider diagram entails
    a primary spider diagram with another fresh spider.
*)
lemma psd_base_insert_spider: "psd_sem_impl_base sh_zones spiders \<Longrightarrow>
                               psd_sem_impl_base sh_zones (List.insert sp spiders)"
  by simp

(*
    Part of the inference rule: remove spider

    If there are no shaded zones in the primary spider diagram, then we can
    remove the spiders from it and the original PSD will entail the new one.
*)
lemma psd_base_remove_spider: "psd_sem_impl_base {} (sp#spiders) \<Longrightarrow>
                               psd_sem_impl_base {} spiders"
  by simp

(*
    Part of the inference rule: remove shaded zone

    If we remove a shaded zone from a primary spider diagram \<phi>, we get a new
    PSD \<psi>, where \<phi> entails \<psi>.
*)
lemma psd_base_remove_sh_zone: "psd_sem_impl_base (insert z sh_zones) spiders \<Longrightarrow>
                                psd_sem_impl_base sh_zones spiders"
  by simp

(*
    An empty spider diagram is a tautology.
*)
lemma psd_empty: "psd_sem [] {} = True"
  by simp

lemma psd2_empty: "psd_sem2 [] {} = True"
  by simp

(*
    We can exchange the order of any two adjacent spiders without changing the
    meaning of the primary diagram. This is the first step to show that the order
    of spiders in the primary diagram does not matter.
*)
lemma psd_swap_spiders: "psd_sem_impl [] sh_zones (sps1 @ [sp1, sp2] @ sps2) =
                         psd_sem_impl [] sh_zones (sps1 @ [sp2, sp1] @ sps2)"
  by auto

lemma psd_spiders_rotate_eq: "psd_sem_impl [] sh_zones spiders1 =
                              psd_sem_impl [] sh_zones (rotate n spiders1)"
  by auto

lemma psd_swap_habitats: "psd_sem2 (h1#h2#habs) {} \<Longrightarrow> psd_sem2 (h2#h1#habs) {}"
  apply auto
  sorry

lemma psd_remove_habitat: "\<And>h. psd_sem (h#habs) {} \<Longrightarrow> psd_sem habs {}"
  sorry

lemma psd_spiders_rotate_eq_2: "psd_sem_impl habs sh_zones spiders1 \<Longrightarrow>
                                psd_sem_impl habs sh_zones (rotate n spiders1)"
  sorry
  (*apply auto
  apply (induct_tac habs)
  apply simp*)

lemma psd_swap_spiders_2: "psd_sem_impl habs sh_zones (s1#s2#spiders) \<Longrightarrow>
                           psd_sem_impl habs sh_zones (s2#s1#spiders)"
  (*apply auto
  apply (case_tac "habs = []")
  apply auto
  apply (unfold psd_sem_impl_def)
  apply (unfold psd_sem_impl_sumC_def)
  apply (unfold psd_sem_impl_graph_def)
  apply (auto)*)
  sorry

(*
    Swapping adjacent elements in a list is enough to express any permutation.
    But I think proofs can be extremely difficult if I use the above approach. I
    was thinking of first showing that the first two elements can be swapped and
    also that the meaning does not change if we rotate the spider list.

    By composition of the swap and rotate we can swap of elements at index $i$
    and $i+1$ by first rotating the list by $i$, then swapping and rotating back
    again (by $len(lst) - i$).
*)

(*
    We can rotate the list of spiders without changing the meaning of the primary
    diagram. This is the second and the last step needed to show that the order
    of spiders in the primary diagram does not matter.
*)

(*lemma psd_decompose: "\<forall>sh_zones. psd_sem_impl habs sh_zones [] \<longrightarrow> (\<exists>Q spiders. Q habs spiders \<and> psd_sem_impl_base sh_zones spiders)"
  apply simp
  apply (induct_tac habs)
  apply (simp)
apply (rule_tac x = "" )
  apply (simp del: sd_region_sem.simps)
  sorry*)

(* TODO: Shows that the order of spider habitats does not matter. *)
(*
    The order in which we specify habitats also does not matter. First we show
    that we can swap the first two habitats.
*)
lemma psd_habs_swap_eq_2: "\<And>sps. psd_sem_impl ([h1, h2] @ habs) {} sps \<Longrightarrow>
                          psd_sem_impl ([h2, h1] @ habs) {} sps"
  apply (auto simp del: sd_region_sem.simps)
  apply (rule_tac x = "sa" in exI)
  apply (rule conjI)
  apply (assumption)
  apply (rule_tac x = "s" in exI)
  apply (simp del: sd_region_sem.simps)
  apply (induct_tac habs)
  apply simp
  sorry

lemma sd_habitats_swap_eq: "sd_sem (PrimarySD (h1#h2#hs) sh_zones) =
                            sd_sem (PrimarySD (h2#h1#hs) sh_zones)"
  sorry

lemma sd_habitats_rotate_eq: "sd_sem (PrimarySD habs1 sh_zones) =
                              sd_sem (PrimarySD (rotate n habs1) sh_zones)"
  sorry




(*==============================================================================
SPIDER DIAGRAMMATIC INFERENCE RULES FORMALISATION
==============================================================================*)

(*
    A formalisation of the first version of the 'add feet' inference rule (i.e.:
    t(A) \<longrightarrow> \<psi> \<turnstile> A \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (PrimarySD (h'#hs) shzs) \<psi>) \<rbrakk> \<Longrightarrow>
                         sd_sem (BinarySD (op -->) (PrimarySD (h#hs) shzs) \<psi>)"
  by auto

(*
    A formalisation of the second version of the 'add feet' inference rule (i.e.:
    t(A) \<and> \<phi> \<longrightarrow> \<psi> \<turnstile> A \<and> \<phi> \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet_con: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (BinarySD (op &) (PrimarySD (h'#hs) shzs) \<phi>) \<psi>) \<rbrakk> \<Longrightarrow>
                             sd_sem (BinarySD (op -->) (BinarySD (op &) (PrimarySD (h#hs) shzs) \<phi>) \<psi>)"
  by auto

(*
    A formalisation of the third version of the 'add feet' inference rule (i.e.:
    t(A) \<or> \<phi> \<longrightarrow> \<psi> \<turnstile> A \<or> \<phi> \<longrightarrow> \<psi>
*)
lemma sd_rule_add_feet_disj: "\<lbrakk> h \<subset> h'; sd_sem (BinarySD (op -->) (BinarySD (op \<or>) (PrimarySD (h'#hs) shzs) \<phi>) \<psi>) \<rbrakk> \<Longrightarrow>
                              sd_sem (BinarySD (op -->) (BinarySD (op \<or>) (PrimarySD (h#hs) shzs) \<phi>) \<psi>)"
  by auto

(*
    A formalisation of the 'split spider' inference rule:

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
    A formalisation of the 'split spider' inference rule---using the BinarySD
    data structure.
*)
lemma sd_rule_split_spiders_B: "\<lbrakk> habs = (h#hs); habA \<union> habB = h \<rbrakk> \<Longrightarrow>
                                sd_sem (PrimarySD habs shzs) =
                                sd_sem (BinarySD (op \<or>)
                                           (PrimarySD (habA#hs) shzs)
                                           (PrimarySD (habB#hs) shzs))"
  by auto



(* NOTE: Follows a second version of the 'sd_sem' interpretation method. It
   uses 'spider identifiers' (which are consecutive natural numbers) and
   a single existentially quantified function, which maps spider identifiers
   to actual elements. Just one quantification instead of N (where N is the
   number of spiders). *)

(* This function takes a list of habitats and returns a set of pairs. The
  first element of these pairs is a natural number (the ID of the spider) and
  the second element is the region where the spider lives (its habitat).

  Note: i-th region in the list of habitats implicitly belongs to the spider
  with the ID i+n (where n is a natural number -- the second argument to this
  function). *)
(*fun sd_habs2pairs :: "'s sd_region list \<Rightarrow> nat \<Rightarrow> (nat * 's sd_region) set"
  where
  "sd_habs2pairs [] n = {}"
  | "sd_habs2pairs (x#xs) n = insert (n, x) (sd_habs2pairs xs (Suc n))"*)

(* Returns a set of consecutive natural numbers starting at n (where n is the
  second argument to this function). There are as many in the set as there
  are regions in the first argument.

  Note: the returned set is actually the set of IDs of all involved spiders. *)
(*fun sd_habs2spids :: "'s sd_region list \<Rightarrow> nat \<Rightarrow> nat set"
  where
  "sd_habs2spids [] n = {}"
  | "sd_habs2spids (x#xs) n = insert n (sd_habs2spids xs (Suc n))"*)

(* sd_sem provides an interpretation of the main data structure 'sd'. In
  fact, this function provides the semantic of the entire language of spider
  diagrams (as encoded by the 'sd' data type). *)
(*fun sd_sem2 :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem2 (PrimarySD habitats sh_zones) =
     (\<exists>f. inj_on f (sd_habs2spids habitats 0) \<and>
     (\<forall>(spider, region) \<in> sd_habs2pairs habitats 0. f spider \<in> sd_region_sem region) \<and>
     (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> sd_habs2spids habitats 0. f s = el))"
  | "sd_sem2 (UnarySD P sd) = (P (sd_sem2 sd))"
  | "sd_sem2 (BinarySD P sdl sdh) = (P (sd_sem2 sdl) (sd_sem2 sdh))"
  | "sd_sem2 NullSD = True"*)



(* NOTE: Follows the third version of the 'sd_sem' interpretation method. It
   uses the same method as the first version, but it interprets the 'primary'
   diagram (unitary diagram) differently. *)

(*definition psd_sem2 :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> bool"
  where
  "psd_sem2 habs sh_zones \<equiv> (\<exists>S. (size S) = (size habs) \<and>
            list_all (\<lambda>(s,h). s \<in> sd_region_sem h) (zip S habs) \<and>
            distinct S \<and>
            (\<forall>z \<in> sh_zones. sd_zone_sem z \<subseteq> set S))"*)

(*fun sd_sem3 :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem3 (PrimarySD habitats sh_zones) = psd_sem2 habitats sh_zones"
  | "sd_sem3 (UnarySD P sd) = (P (sd_sem3 sd))"
  | "sd_sem3 (BinarySD P sdl sdh) = (P (sd_sem3 sdl) (sd_sem3 sdh))"
  | "sd_sem3 NullSD = True"*)



(* NOTE: An, as of yet, failed attempt to prove the equivalence of the three
   interpretations. *)

(*lemma "\<forall>sd. sd_sem3 sd = sd_sem2 sd"
  apply (rule allI)
  apply (induct_tac sd)
  prefer 3
  apply(simp only: sd_sem2.simps sd_sem3.simps)
  prefer 2
  apply (simp only: sd_sem2.simps sd_sem3.simps)
  prefer 2
  apply (simp only: sd_sem2.simps sd_sem3.simps)
  apply (unfold sd_sem3.simps psd_sem2_def sd_sem2.simps)
  apply (auto simp add: psd_sem2_def)
  oops*)



(* TODO: Formalise the SD inference rules with one of the above
   interpretations. *)

(*ML {* @{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"} *}
ML {* @{term "True"} *}
ML {* #3 ("dsa", 5, SOME 1) *}
ML {* eq_list op= ((sort_distinct string_ord [ "c", "a", "a", "k", "b" ]), (sort_distinct string_ord [ "k", "c", "a", "b" ])) *}*)

ML {* print_depth 100 *}
ML {* Config.put show_brackets true *}




(*==============================================================================
DIABELLI SETUP (ML-level translation, communication, and tactics procedures)
==============================================================================*)

use "diabelli.ML"

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
              (*Scan.succeed (fn ctxt => (Method.SIMPLE_METHOD' (Diabelli.sd_tac "fuck you" ctxt))) xs*)
          end)
*} "A no-op tactic for testing the translation from SNF to spider diagrams and communication with Speedith."

(*lemma testB: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (auto simp del: distinct.simps)
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac idempotency sdi: 1)
  by auto*)

(* This lemma should land in the unit tests. *)
lemma testA: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply (sd_tac split_spiders sdi: 1 sp: "s2" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 3 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 3 sp: "s1" r: "[([\"A\"],[\"B\"])]")
  apply (sd_tac add_feet sdi: 2 sp: "s2" r: "[([\"A\", \"B\"],[])]")
  apply (sd_tac add_feet sdi: 2 sp: "s1" r: "[([\"B\"],[\"A\"])]")
  apply (sd_tac idempotency sdi: 1)
  by auto

(*ML {* Diabelli.from_snf_to_sd @{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"} *}
ML {* Diabelli.random_tests "tralala" *}
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

(*ML {* Diabelli.exec_args "echo" [ "My name is matej.", "T\\h$is \"is\" a 'treat'.", "And a \n newline.", PolyML.makestring (Diabelli.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"}))] *}
ML {* Diabelli.exec_args (getenv "DIABELLI_JAVA_PATH") [ "-jar", getenv "DIABELLI_SPEEDITH_PATH", "-sd", PolyML.makestring (Diabelli.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"})) ] *}
ML {* getenv "DIABELLI_JAVA_PATH" *}
ML {* Diabelli.from_snf_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"}); *}*)


(*ML {* Diabelli.random_tests (Diabelli.bash_escape (PolyML.makestring (Diabelli.from_term_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"})))) *}*)
(*ML {* Diabelli.random_tests (Diabelli.bash_escape (PolyML.makestring { one = 1, two = "some", mega = SOME 1, three = NONE})) *}*)

end