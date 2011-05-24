(*  Title:      DiabelliIR.ML
    Author:     Matej Urbas

DiabelliIR: provides a formalisation of the data structure used as the
            intermediate represenation.

            This record is fed the diagrammatic reasoner on the ML level. The
            external diagrammatic reasoner returns a transformed record,
            which can be directly translated to Isabelle formulae via the
            provided interpretation functions (these are named
            'sd_<name>_sem').
*)

theory DiabelliIR
imports Main
uses ("diabelli.ML")
begin

(* sd_zone and sd_region are the types used to encode zones and regions as
   defined in the theory of spider diagarms. *)
types
  'e sd_zone = "'e set set * 'e set set"
  'e sd_region = "'e sd_zone set"

(* 'sd' is the main data structure. It describes any compound spider diagram.
  It serves as the formalisation of the intermediate represenatition for
  communicating formulae between the external diagrammatic reasoner and
  Isabelle.

  A record of this data structure is interpreted by functions
  'sd_<name>_sem'. *)
datatype ('s)sd =
    PrimarySD "'s sd_region list" "'s sd_zone set"
  | UnarySD "bool \<Rightarrow> bool" "('s)sd"
  | BinarySD "bool \<Rightarrow> bool \<Rightarrow> bool" "('s)sd" "('s)sd"
  | NullSD

(* sd_zone_sem defines the semantics of a zone (an interpretation of
  'sd_zone'). *)
fun sd_zone_sem :: "'e sd_zone \<Rightarrow> 'e set"
  where
  "sd_zone_sem (in_sets, out_sets) = (\<Inter> in_sets) - (\<Union> out_sets)"

(* sd_region_sem defines the semantics of a region (an interpretation of
  'sd_region'). *)
fun sd_region_sem :: "'e sd_region \<Rightarrow> 'e set"
  where
  "sd_region_sem zones = (\<Union> z \<in> zones. sd_zone_sem z)"


(* The interpretation of the primary (unitary) spider diagram. *)
fun sd_primary_sem :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> 's list \<Rightarrow> bool"
  where
  "sd_primary_sem [] sh_zones spiders = (distinct spiders \<and> (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> set spiders. s = el))"
  | "sd_primary_sem (h#hs) sh_zones spiders = (\<exists>s. s \<in> sd_region_sem h \<and> sd_primary_sem hs sh_zones (s#spiders))"


(* sd_sem provides an interpretation of the main data structure 'sd'. In
  fact, this function provides the semantic of the entire language of spider
  diagrams (as encoded by the 'sd' data type). *)
fun sd_sem :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem (PrimarySD habitats sh_zones) = sd_primary_sem habitats sh_zones []"
  | "sd_sem (UnarySD P sd) = (P (sd_sem sd))"
  | "sd_sem (BinarySD P sdl sdh) = (P (sd_sem sdl) (sd_sem sdh))"
  | "sd_sem NullSD = True"



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
fun sd_habs2pairs :: "'s sd_region list \<Rightarrow> nat \<Rightarrow> (nat * 's sd_region) set"
  where
  "sd_habs2pairs [] n = {}"
  | "sd_habs2pairs (x#xs) n = insert (n, x) (sd_habs2pairs xs (Suc n))"

(* Returns a set of consecutive natural numbers starting at n (where n is the
  second argument to this function). There are as many in the set as there
  are regions in the first argument.

  Note: the returned set is actually the set of IDs of all involved spiders. *)
fun sd_habs2spids :: "'s sd_region list \<Rightarrow> nat \<Rightarrow> nat set"
  where
  "sd_habs2spids [] n = {}"
  | "sd_habs2spids (x#xs) n = insert n (sd_habs2spids xs (Suc n))"

(* sd_sem provides an interpretation of the main data structure 'sd'. In
  fact, this function provides the semantic of the entire language of spider
  diagrams (as encoded by the 'sd' data type). *)
fun sd_sem2 :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem2 (PrimarySD habitats sh_zones) =
     (\<exists>f. inj_on f (sd_habs2spids habitats 0) \<and>
     (\<forall>(spider, region) \<in> sd_habs2pairs habitats 0. f spider \<in> sd_region_sem region) \<and>
     (\<forall>z \<in> sh_zones. \<forall>el \<in> sd_zone_sem z. \<exists>s \<in> sd_habs2spids habitats 0. f s = el))"
  | "sd_sem2 (UnarySD P sd) = (P (sd_sem2 sd))"
  | "sd_sem2 (BinarySD P sdl sdh) = (P (sd_sem2 sdl) (sd_sem2 sdh))"
  | "sd_sem2 NullSD = True"



(* NOTE: Follows the third version of the 'sd_sem' interpretation method. It
   uses the same method as the first version, but it interprets the 'primary'
   diagram (unitary diagram) differently. *)

definition sd_primary_sem2 :: "'s sd_region list \<Rightarrow> 's sd_zone set \<Rightarrow> bool"
  where
  "sd_primary_sem2 habs sh_zones \<equiv> (\<exists>S. (size S) = (size habs) \<and>
            list_all (\<lambda>(s,h). s \<in> sd_region_sem h) (zip S habs) \<and>
            distinct S \<and>
            (\<forall>z \<in> sh_zones. sd_zone_sem z \<subseteq> set S))"

fun sd_sem3 :: "('s)sd \<Rightarrow> bool"
  where
  "sd_sem3 (PrimarySD habitats sh_zones) = sd_primary_sem2 habitats sh_zones"
  | "sd_sem3 (UnarySD P sd) = (P (sd_sem3 sd))"
  | "sd_sem3 (BinarySD P sdl sdh) = (P (sd_sem3 sdl) (sd_sem3 sdh))"
  | "sd_sem3 NullSD = True"



(* NOTE: An, as of yet, failed attempts to prove the equivalence of the three
   interpretations. *)

lemma "\<forall>sd. sd_sem3 sd = sd_sem2 sd"
  apply (rule allI)
  apply (induct_tac sd)
  prefer 3
  apply(simp only: sd_sem2.simps sd_sem3.simps)
  prefer 2
  apply (simp only: sd_sem2.simps sd_sem3.simps)
  prefer 2
  apply (simp only: sd_sem2.simps sd_sem3.simps)
  apply (unfold sd_sem3.simps sd_primary_sem2_def sd_sem2.simps)
  apply (auto simp add: sd_primary_sem2_def)
  oops



(* TODO: Formalise the SD inference rules with one of the above
   interpretations. *)

ML {* @{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"} *}
ML {* @{term "True"} *}
ML {* #3 ("dsa", 5, SOME 1) *}

use "diabelli.ML"

ML {* Diabelli.from_sdnorm_to_sd (@{term "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"}); *}


(*ML {* Diabelli.random_tests (Diabelli.bash_escape (PolyML.makestring (Diabelli.from_term_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"})))) *}*)
ML {* Diabelli.random_tests (Diabelli.bash_escape (PolyML.makestring { one = 1, two = "some", mega = SOME 1, three = NONE})) *}

end