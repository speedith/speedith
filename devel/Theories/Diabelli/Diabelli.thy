theory MixR
imports MixRIR
begin


(* First let us introduce some basic types used in the theory of Spider
  Diagrams. These are Isabelle counterparts of diagrammatic elements as defined
  by [Howse et al, Spider Diagrams, 2005]. *)
types
  contour = "nat"
  zone = "contour set"
  region = "zone set"
  spider = "nat"

(*lemma split_spiders: "\<forall>habs1 habs2.(list_all2 (\<lambda>r1 r2. (sd_region_sem r1 \<subseteq> sd_region_sem r2)) habs1 habs2 \<longrightarrow> (sd_sem  (PrimarySD habs1 zones) \<longrightarrow> sd_sem (PrimarySD habs2 zones)))"
  apply (auto simp del: sd_region_sem.simps simp add: list_all2_def size.simps)
  apply (induct_tac habs2)
  apply auto*)

text {* This record contains all necessary parameters for the SpiderDiagrams
locale. *}
record 'e SpiderDiagram =

  (* A zone that is an element of this set is called a shaded zone. See
  'only_spiders_in_shzon' in 'SpiderDiagram' locale for the properties of
  shaded zones. *)
  shaded_zones :: "zone set" ("shzon\<index>")

  (* contour_map takes a 'contour identifier' as its argument and returns a concrete set
  which is identified by the contour. It is basically an 'interpretation of
  contours IDs.' zone_map and region_map are analogous versions for zones and regions.
  *)
  contour_map :: "contour \<Rightarrow> 'e set" ("cmap\<index> _")

  (* The 'spider_map' function returns the corresponding element for each
  spider. *)
  spider_map :: "spider \<Rightarrow> 'e" ("smap\<index> _")

  (* The 'habitat_map' function that returns a given spider's habitat. Note that
  different spiders may inhabit the same region. *)
  habitat_map :: "spider \<Rightarrow> region" ("hab\<index> _")



  (* The following is pretty much the definition of the function which maps the
  set of labels to Isabelle sets. This definition can be found in [Howse et al,
  Spider Diagrams, 2005, pg. 5]. *)
fun zone_map :: "('e, 'a) SpiderDiagram_scheme \<Rightarrow> zone \<Rightarrow> 'e set" ("zmap\<index>")
  where
  "zmap\<^bsub>d\<^esub> cs = (\<Inter>c \<in> cs. cmap\<^bsub>d\<^esub> c) - (\<Union>c \<in> (-cs). cmap\<^bsub>d\<^esub> c)"



  (* The definition of the function which maps a diagrammatic region to an
  actual set. *)
fun region_map :: "('e, 'a) SpiderDiagram_scheme \<Rightarrow> region \<Rightarrow> 'e set" ("rmap\<index>")
  where
  "rmap\<^bsub>d\<^esub> r = (\<Union>z \<in> r. zmap\<^bsub>d\<^esub> z)"



  (* Maps a set of spiders to the set of elements that the spiders represent. *)
fun spider_set_map :: "('e, 'a) SpiderDiagram_scheme \<Rightarrow> spider set \<Rightarrow> 'e set" ("ssmap\<index>")
  where
  "ssmap\<^bsub>d\<^esub> ss = { (smap\<^bsub>d\<^esub> s) | s. s \<in> ss }"



text {* This is the first step towards the main locale for SpiderDiagrams. *}
locale SpiderDiagram_base =

  (* Some parameters to the locale: the actual model of the spider diagrams. *)
  fixes d :: "('e, 'a) SpiderDiagram_scheme" (structure)

  (* Some 'locale assumptions' expressing general properties of the concepts in
  abstract spider diagrams. *)

  (* Spiders: *)
  (* Two different spiders refer to two different elements. *)
  assumes ne_spiders_ne_elements: "\<lbrakk> s \<noteq> s' \<rbrakk> \<Longrightarrow> (smap s) \<noteq> (smap s')"

  (* The spiders cannot live in zone-less regions. Which would mean that a
  spider is an element of an empty set. *)
  and spiders_in_nonempty_regions: "hab s \<noteq> {}"

  (* Spiders in their habitats refer to mapped element inclusion in the set to
  which the habitat refers. *)
  and spiders_elements_in_region: "smap s \<in> rmap hab s"

begin

text {* Definitions of useful operators and relations on Spider Diagram
concepts. *}

definition subregion (infix "\<sqsubset>" 50)
  where
  "r \<sqsubset> r' = ((rmap r) \<subset> rmap r')"

definition regioninter (infix "\<sqinter>" 70)
  where
  "r \<sqinter> r' = ((rmap r) \<inter> rmap r')"

definition regionunion (infix "\<squnion>" 70)
  where
  "r \<squnion> r' = ((rmap r) \<union> rmap r')"

definition regionminus (infix "\<setminus>" 70)
  where
  "r \<setminus> r' = ((rmap r) - rmap r')"

definition subregioneq (infix "\<sqsubseteq>" 50)
  where
  "r \<sqsubseteq> r' = ((rmap r) \<subseteq> rmap r')"

definition subzone (infix "\<sqsubset>" 50)
  where
  "z \<sqsubset> r = ((zmap z) \<subset> rmap r)"

definition subzoneeq (infix "\<sqsubseteq>" 50)
  where
  "z \<sqsubseteq> r = ((zmap z) \<subseteq> rmap r)"

definition zoneinter (infix "\<sqinter>" 70)
  where
  "z \<sqinter> z' = ((zmap z) \<inter> zmap z')"

definition zoneinterregion (infix "\<sqinter>" 70)
  where
  "z \<sqinter> r = ((zmap z) \<inter> rmap r)"

definition regioninterzone (infix "\<sqinter>" 70)
  where
  "r \<sqinter> z = ((rmap r) \<inter> zmap z)"

definition inhabiting_spiders ("\<S> _" 80)
  where
  "\<S> (r::region) = {s. (hab s) \<subseteq> r }"

definition touching_spiders ("\<T> _" 80)
  where
  "\<T> (r::region) = {s. (hab s) \<inter> r \<noteq> {} }"

definition spiders_touching_zone ("\<T>\<Z> _" 80)
  where
  "(\<T>\<Z> (z::zone)) = {s. z \<in> hab s }"



text {* These lemmas expose some useful properties about the connection between
zones, regions, and their respective sets. *}

(* Lemma 3.1 part 1:
  This lemma seems quite important to me. It says that two different zones
  represent two disjoint sets. *)
lemma disjoint_zones: "\<lbrakk> z \<noteq> (z'::zone) \<rbrakk> \<Longrightarrow> z \<sqinter> z' = {}"
  by (auto simp: zoneinter_def)

(* More about zones. If the mapped sets of zones contain one common element,
  then we are actually talking about the same zones. *)
lemma shared_el_same_zone: "\<lbrakk> x \<in> zmap z; x \<in> zmap z' \<rbrakk> \<Longrightarrow> z = z'"
  by(auto)

(* More about zones. If two elements are in two different zones then these
  elements are necessarily not the same. *)
lemma diff_zones_diff_el: "\<lbrakk> x \<in> zmap z; x' \<in> zmap z'; z \<noteq> z' \<rbrakk> \<Longrightarrow> x \<noteq> x'"
  by(auto)

declare zone_map.simps [simp del]

ML {* @{thm mod_Suc} *}

lemma shared_el_zone_in_region: "\<lbrakk> x \<in> zmap z; x \<in> rmap r \<rbrakk> \<Longrightarrow> z \<in> r"
proof (auto)
  fix z'
  assume xinz: "x \<in> zmap z"
  assume z'inr: "z' \<in> r"
  assume xinz': "x \<in> zmap z'"
  hence "z = z'" using xinz
    by (simp add: shared_el_same_zone)
  thus "z \<in> r" using z'inr
    by (simp)
qed

(* If two elements are in disjoint regions, they cannot be equal. *)
lemma disj_rmap_diff_spider: "\<lbrakk> x \<in> rmap r; x' \<in> rmap r'; r \<inter> r' = {} \<rbrakk> \<Longrightarrow> x \<noteq> x'"
proof (auto)
  fix z z'
  assume disj: "r \<inter> r' = {}"
  assume x'inz: "x' \<in> zmap z"
  assume x'inz': "x' \<in> zmap z'"
  assume zinr: "z \<in> r"
  assume z'inr': "z' \<in> r'"
  hence "z \<noteq> z'" using zinr disj
    by (auto)
  thus False using x'inz x'inz'
    by (auto simp add: shared_el_same_zone)
qed

(* The map of a region that contains a zone, contains the map of the zone. *)
lemma zone_inter_region_eq_zone: "\<lbrakk> z \<in> r \<rbrakk> \<Longrightarrow> z \<sqinter> r = zmap z"
by(auto simp: zoneinterregion_def)

(* If a region does not contain a zone, then the intersection of the map of this
region and the map of the zone is an empty set. *)
lemma region_inter_other_zone_empty: "\<lbrakk> z \<notin> r \<rbrakk> \<Longrightarrow> r \<sqinter> z = {}"
proof (auto simp add: regioninterzone_def)
  fix e z'
  assume as1: "z \<notin> r"
  assume einz: "e \<in> zmap z"
  assume zinr: "z' \<in> r"
  assume einz': "e \<in> zmap z'"
  have "z \<noteq> z'" using as1 zinr
    by auto
  thus "False" using as1 einz einz'
    by (auto simp: zone_map.simps)
qed

(* If two regions contain the same zone, then their intersection set also
  contains all element of the zone's set. *)
lemma inter_region_inter_rmap: "\<lbrakk> z \<in> r \<inter> r' \<rbrakk> \<Longrightarrow> z \<sqsubseteq> r \<inter> r'"
by (auto simp: subzoneeq_def)

(* Lemma 3.1 part 2.i *)
lemma rmap_inter_additive: "rmap (r \<inter> r') = r \<sqinter> r'"
proof (auto simp add: regioninter_def simp del: zone_map.simps)
  fix e z z'
  assume einz: "e \<in> zmap z"
  assume einz': "e \<in> zmap z'"
  assume z'inr': "z' \<in> r'"
  assume zinr: "z \<in> r"
  have zeqz': "z = z'" using einz einz'
    by (auto simp: zone_map.simps)
  hence zinr': "z \<in> r'" using z'inr'
    by auto
  thus "\<exists>z\<in>r \<inter> r'. e \<in> zmap z" using einz zinr
    by auto
qed

(* Lemma 3.1 part 2.ii *)
lemma rmap_union_additive: "rmap (r \<union> r') = r \<squnion> r'"
by (auto simp add: regionunion_def)

(* Lemma 3.1 part 2.iii *)
lemma rmap_minus_additive: "rmap (r - r') = r \<setminus> r'"
proof (auto simp add: regionminus_def)
  fix e z z'
  assume einz: "e \<in> zmap z"
  assume einz': "e \<in> zmap z'"
  assume z'inr': "z' \<in> r'"
  assume zinr: "z \<in> r"
  assume zninr': "z \<notin> r'"
  have zneqz': "z \<noteq> z'" using zinr zninr' z'inr'
    by auto
  thus "False" using einz einz'
    by (auto simp: zone_map.simps)
qed

(* Lemma 3.1 part 2.iv *)
lemma rmap_subseq_additive: "\<lbrakk> (r::region) \<subseteq> r' \<rbrakk> \<Longrightarrow> r \<sqsubseteq> r'"
by (auto simp add: subregioneq_def)

(* Intersection between regions that do not share any
   zones is empty. *)
lemma diff_regions_inter_empty: "\<lbrakk> (r::region) \<inter> r' = {} \<rbrakk> \<Longrightarrow> r \<sqinter> r' = {}"
proof(auto)
  fix x
  assume iempty: "r \<inter> r' = {}"
  assume xininter: "x \<in> r \<sqinter> r'"
  have "r \<sqinter> r' = {}" using iempty
    proof(auto simp: regioninter_def)
      fix e z z'
      assume einz: "e \<in> zmap z"
      assume einz': "e \<in> zmap z'"
      assume z'inr': "z' \<in> r'"
      assume zinr: "z \<in> r"
      have zeqz': "z = z'" using einz einz'
        by (auto simp: zone_map.simps)
      hence zinr': "z \<in> r'" using z'inr'
        by auto
      hence "z \<in> r \<inter> r'" using zinr' zinr
        by auto
      thus "False" using iempty
        by auto
    qed
    thus "False" using xininter
      by auto
qed

declare region_map.simps [simp del]

(* A spider lives in a zone (but we don't necessarily know which zone). *)
lemma spider_has_zone: "\<exists>z. smap s \<in> zmap z"
proof -
  have rnotempty: "hab s \<noteq> {}"
    by(simp add: spiders_in_nonempty_regions)
  hence sinr: "smap s \<in> rmap hab s"
    by (auto simp add: spiders_elements_in_region)
  thus zone_exists: "\<exists>x. smap s \<in> zmap x" using rnotempty sinr
    by(auto simp: region_map.simps)
qed

(* This lemma shows that there exists a unique zone in which the spider
  actually resides. *)
lemma spider_in_unique_zone: "\<exists>! z. smap s \<in> zmap z"
proof (auto simp add: spider_has_zone disjoint_zones)
  fix z z' s'
  assume sinz: "smap s \<in> zmap z"
  assume sinz': "smap s \<in> zmap z'"
  assume s'inz: "s' \<in> z"
  have "z = z'" using sinz sinz'
    by (auto simp add: shared_el_same_zone)
  thus "s' \<in> z'" using s'inz
    by (simp)
next
  fix z z' s'
  assume sinz: "smap s \<in> zmap z"
  assume sinz': "smap s \<in> zmap z'"
  assume s'inz': "s' \<in> z'"
  have "z = z'" using sinz sinz'
    by (auto simp add: shared_el_same_zone)
  thus "s' \<in> z" using s'inz'
    by (simp)
qed

(* An element that corresponds to a spider is in the set of its habitat. *)
lemma spider_elmnt_in_hab_set: "\<lbrakk> (hab s) = r \<rbrakk> \<Longrightarrow> smap s \<in> rmap r"
proof (auto simp: region_map.simps)
  have rnotempty: "hab s \<noteq> {}"
    by(simp add: spiders_in_nonempty_regions)
  hence sinr: "smap s \<in> rmap hab s"
    by (auto simp add: spiders_elements_in_region)
  thus zone_exists: "\<exists>x \<in> hab s. smap s \<in> zmap x" using rnotempty sinr
    by(auto simp: region_map.simps)
qed

lemma spider_zone_in_habitat: "\<lbrakk> smap s \<in> zmap z \<rbrakk> \<Longrightarrow> z \<in> hab s"
proof -
  assume sinz: "smap s \<in> zmap z"
  hence sinhab: "smap s \<in> rmap hab s"
    by (auto simp add: spiders_elements_in_region)
  thus "z \<in> hab s" using sinz
    by (auto simp add: shared_el_zone_in_region)
qed

lemma diff_smap_diff_spider: "\<lbrakk> smap s \<noteq> smap s' \<rbrakk> \<Longrightarrow> s \<noteq> s'"
by (auto)


end (* SpiderDiagram_base *)



(* The final locale for spider diagrams. We need two locales to work around a
  limitation in the implementation of locales. *)
locale SpiderDiagram = SpiderDiagram_base +
  (* A shaded zone is a subset of the set of all spiders that touch this zone.
  This means that there may not be any other spiders in a shaded zone. *)
  assumes only_spiders_in_shzon: "\<lbrakk> z \<in> shzon \<rbrakk> \<Longrightarrow> (zmap z) \<subseteq> ssmap (\<T>\<Z> r)"
begin

declare region_map.simps [simp add]
declare zone_map.simps [simp add]

(* Spider diagram transformation inference 3 (split spider). *)
lemma sd_rule_split_spider: "(smap s \<in> r \<squnion> r') = (smap s \<in> rmap r \<or> smap s \<in> rmap r')"
  by (auto simp add: regionunion_def)

(* Spider diagram transformation inference 'adding feet to a spider'.
   Note: this inference is very obvious and quite frankly trivial in Isabelle, but it
   has a very interesting diagrammatic equivalent\<dots> so why not 'formalise' it
   here. *)
lemma sd_rule_add_feet: "\<lbrakk> smap s \<in> rmap r; r \<subseteq> r' \<rbrakk> \<Longrightarrow> smap s \<in> rmap r'"
  by (auto)
lemma sd_rule_add_feet_2: "\<lbrakk> hab s \<subseteq> r; r \<subseteq> r' \<rbrakk> \<Longrightarrow> hab s \<subseteq> r'"
  by (simp)

(* Spider diagram transformation inference 'swap feet'. *)
lemma sd_rule_swap_feet_2: "\<lbrakk> smap s \<in> rmap r; smap s' \<in> rmap r'; r' \<subset> r; rs \<subseteq> r - r' \<rbrakk> \<Longrightarrow> \<exists>s1 s1'. smap s1 \<in> rmap (r' \<union>  rs) \<and> smap s1' \<in> rmap (r - rs)"
  by (auto)


(* EXAMPLES *)

(* This is the example Gem gave me. It took quite some work to prove it. It
  would really help to have a diagrammatic language which shortens it. *)
lemma example_1_d: "\<lbrakk> hab s = { { 0, 1 } }; hab s' = { {0}, {1} } \<rbrakk> \<Longrightarrow> \<exists>s s'. smap s \<noteq> smap s' \<and> smap s \<in> cmap 0 \<and> smap s' \<in> cmap 1"
proof -
  assume habs: "hab s = {{0, 1}}"
  assume habs': "hab s' = {{0}, {1}}"
  have sneqs': "s \<noteq> s'" using habs habs'
    by (auto)
  hence s_el_neq_s'_el: "smap s \<noteq> smap s'"
    by (auto simp add: ne_spiders_ne_elements)
  have "smap s \<in> rmap {{0, 1}}" using habs
    by (iprover intro: spider_elmnt_in_hab_set)
  hence s_el_in_0_and_1: "smap s \<in> cmap 0 \<and> smap s \<in> cmap 1"
    by (auto)
  have "smap s' \<in> rmap {{0}, {1}}" using habs'
    by (iprover intro: spider_elmnt_in_hab_set)
  hence "smap s' \<in> cmap 0 \<or> smap s' \<in> cmap 1" using habs'
    by (auto)
  thus "\<exists>s s'. smap s \<noteq> smap s' \<and> smap s \<in> cmap 0 \<and> smap s' \<in> cmap 1" using s_el_in_0_and_1 s_el_neq_s'_el
    apply (auto)
    apply (rule_tac x = "s'" in exI)
    apply (rule_tac x = "s" in exI)
    by (simp)
qed

declare zone_map.simps [simp del]
(*declare One_nat_def [simp del]*)

(* This is the example Gem gave me. It took quite some work to prove it. It
  would really help to have a diagrammatic language which shortens it. *)
lemma example_1_a: "\<lbrakk> hab s = { { 0, 1 } }; hab s' = { {0}, {1} } \<rbrakk> \<Longrightarrow> \<exists>s s'. smap s \<noteq> smap s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}}"
proof -
  assume habs: "hab s = {{0, 1}}"
  assume habs': "hab s' = {{0}, {1}}"
  have sneqs': "s \<noteq> s'" using habs habs'
    by (auto)
  hence s_el_neq_s'_el: "smap s \<noteq> smap s'"
    by (auto simp add: ne_spiders_ne_elements)
  have "smap s \<in> rmap {{0, 1}}" using habs
    by (iprover intro: spider_elmnt_in_hab_set)
  hence s_el_in_0_and_1: "smap s \<in> zmap {0, 1}"
    by (auto)
  have "smap s' \<in> rmap {{0}, {1}}" using habs'
    by (iprover intro: spider_elmnt_in_hab_set)
  hence "smap s' \<in> zmap {0} \<or> smap s' \<in> zmap {1}" using habs'
    by (auto)
  thus "\<exists>s s'. smap s \<noteq> smap s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}}" using s_el_in_0_and_1 s_el_neq_s'_el
    apply (auto)
    apply (rule_tac x = "s'" in exI)
    apply (rule_tac x = "s" in exI)
    by (simp)
qed

(* This is the example Gem gave me. It took quite some work to prove it. It
  would really help to have a diagrammatic language which shortens it. *)
lemma example_1_b: "\<lbrakk> smap s \<in> rmap {{ 0, 1 }}; smap s' \<in> rmap {{0}, {1}} \<rbrakk> \<Longrightarrow> \<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}}"
proof -
  assume habs: "smap s \<in> rmap {{0, 1}}"
  assume habs': "smap s' \<in> rmap {{0}, {1}}"
  hence "smap s \<noteq> smap s'" using habs
    apply (simp)
    apply (erule disjE)
    by (auto simp add: diff_zones_diff_el)
  hence sneqs': "s \<noteq> s'"
    by (auto)
  have s_el_in_0_and_1: "smap s \<in> zmap {0, 1}" using habs
    by (auto)
  have "smap s' \<in> zmap {0} \<or> smap s' \<in> zmap {1}" using habs'
    by (simp)
  thus "\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}}" using s_el_in_0_and_1 sneqs'
    apply (auto)
    apply (rule_tac x = "s'" in exI)
    apply (rule_tac x = "s" in exI)
    by (simp)
qed

(* Spoke with Thomas and he suggested I use some predicates like 'diagram(\<dots>)'
  which nicely capture Isabelle expressions into some structure which is then
  easy to work with. *)

thm "exI"

(* This is another variant of the same example, only this time using the
  existential quantifier without the meta-level operator '\<Longrightarrow>'. *)
lemma example_1_c: "(\<exists>s s'. smap s \<in> rmap {{ 0, 1 }} \<and> smap s' \<in> rmap {{0}, {1}}) \<longrightarrow> (\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}})"
proof (auto simp del: region_map.simps One_nat_def)
  fix s s'
  assume habs: "smap s \<in> rmap {{0, 1}}"
  assume habs': "smap s' \<in> rmap {{0}, {1}}"
  hence "smap s \<noteq> smap s'" using habs
    apply (simp)
    apply (erule disjE)
    by (auto simp add: diff_zones_diff_el)
  hence sneqs': "s \<noteq> s'"
    by (blast)
  have s_el_in_0_and_1: "smap s \<in> zmap {0, 1}" using habs
    by (simp)
  have "smap s' \<in> zmap {0} \<or> smap s' \<in> zmap {1}" using habs'
    by (simp)
  thus "\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}}" using s_el_in_0_and_1 sneqs'
    apply (auto)
    apply (rule_tac x = "s'" in exI)
    apply (rule_tac x = "s" in exI)
    by (simp)
qed



(* This is another variant of the same example, only this time using the
  existential quantifier without the meta-level operator '\<Longrightarrow>'. *)
lemma ex_1: "(\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{ 0, 1 }} \<and> smap s' \<in> rmap {{0}, {1}}) \<longrightarrow>
                    (\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}})"
  by (auto, iprover)



(* This is another variant of the same example, only this time using the
  existential quantifier without the meta-level operator '\<Longrightarrow>'. *)
lemma ex_1_a: "(smap 1 \<in> rmap {{ 0, 1 }} \<and> smap 2 \<in> rmap {{0}, {1}}) \<longrightarrow>
                    (\<exists>s s'. s \<noteq> s' \<and> smap s \<in> rmap {{0}, {0, 1}} \<and> smap s' \<in> rmap {{1}, {0, 1}})"
  apply (auto)
  apply (rule_tac x = "2" in exI)
  apply (rule_tac x = "1" in exI)
  apply (auto)
  apply (rule_tac x = "1" in exI)
  apply (rule_tac x = "2" in exI)
  by (auto)

(* Spider diagram transformation inference 'swap feet'. *)
(*lemma sd_rule_swap_feet_N: "\<exists>s1 s2. s1 \<noteq> s2 \<and> s1 \<in> r1 \<and> s2 \<in> r2 \<and> r1 \<subset> r2 \<and> rs \<subseteq> r2 - r1"
  sorry
lemma sd_rule_swap_feet: "\<lbrakk> s \<noteq> s'; smap s \<in> rmap r; smap s' \<in> rmap r'; r' \<subset> r; rs \<subseteq> r - r' \<rbrakk> \<Longrightarrow> \<exists>ss ss'. ss \<noteq> ss' \<and> ss \<in> rmap (r' \<union>  rs) \<and> ss' \<in> rmap (r - rs)"
  sorry*)

end

end