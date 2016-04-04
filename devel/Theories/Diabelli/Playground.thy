theory Playground
imports MixRIR
begin

lemma inj_noteq: "\<lbrakk> x \<noteq> y; inj f \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
  by (auto simp add: inj_on_def)

lemma "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow>
       (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  apply(auto)
  by(iprover)

(*lemma test_export_xSym: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  by(inference test_export)*)

(*lemma "(\<exists>f. distinct [s, s'] \<and> inj_on f {s, s'} \<and> f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A)) \<longleftrightarrow> sd_sem (UnitarySD [s, s'] {(s, {({A, B},{})}), (s', {({A},{B}), ({B},{A})})} {})"
  apply (auto)*)

lemma "(\<exists>s s'. s \<noteq> s' \<and> s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A)) \<longleftrightarrow> sd_sem (PrimarySD [ {({A, B},{})}, {({A},{B}), ({B},{A})} ] {})"
  apply (simp)
  by (metis)

lemma "(\<exists>s1 s2. s1 \<in> A - B \<and> s2 \<in> A \<inter> B) \<or> (\<exists>s1 s2. s1 \<in> B - A \<and> s2 \<in> A \<inter> B) \<longrightarrow> (\<exists>s1 s2. s1 \<in> A \<and> s2 \<in> B)"
  by (auto)

lemma "(\<exists>s. s \<in> A \<and> A \<subseteq> {s}) \<longleftrightarrow> sd_sem (PrimarySD [{({A},{})}] {({A}, {})})"
  by (auto)

(* The following types correspond to the basic elements in the language of
  spider diagrams. For a definition of spider diagrams see [Howse et al,
  Spider Diagrams, 2005].*)
types
  'e sd1_zone = "'e set list * 'e set list"
  'e sd1_region = "'e sd1_zone list"
  ('a,'e)sd1_habitat = "'a * 'e sd1_region"
  ('a,'e)sd1_habitats = "('a,'e)sd1_habitat list"

(* 'sd' is the main data structure in this theory. It represents a unitary
  spider diagram.

  This structure can be interpreted (in the logic of Isabelle) via
  interpretation functions below. The names of interpretation functions are
  of the following form:

     sd1_<name>_intr

  *)
types ('a, 'e)sd = "'a list * ('a,'e)sd1_habitats * 'e sd1_region"
  (*| CompoundSD "(bool \<Rightarrow> bool \<Rightarrow> bool) * ('a,'e)sd * ('a,'e)sd"*)

fun sd1_zone_inter :: "'e sd1_zone \<Rightarrow> 'e set"
  where
  "sd1_zone_inter (zs_in, zs_out) = (\<Inter> set zs_in) - (\<Union> set zs_out)"

fun sd1_region_intr :: "'e sd1_region \<Rightarrow> 'e set"
  where
  "sd1_region_intr [] = {}"
  | "sd1_region_intr (z # zs) = ((sd1_zone_inter z) \<union> (sd1_region_intr zs))"

definition sd1_zone_in_reg :: "'e sd1_zone \<Rightarrow> 'e sd1_region \<Rightarrow> bool"
  where
  "sd1_zone_in_reg z reg = (sd1_zone_inter z \<subseteq> sd1_region_intr reg)"

fun sd1_habitats_intr :: "('a,'e)sd1_habitats \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> bool"
  where
  "sd1_habitats_intr [] smap = True"
  | "sd1_habitats_intr ((sp, reg) # habs) smap = ((smap sp \<in> sd1_region_intr reg) \<and> sd1_habitats_intr habs smap)"

fun sd1_spiders_touching_zone :: "('a,'e)sd1_habitats \<Rightarrow> 'e sd1_zone \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> 'e set"
  where
  "sd1_spiders_touching_zone [] z smap = {}"
  | "sd1_spiders_touching_zone ((sp, reg)#habs) z smap = (if (sd1_zone_in_reg z reg) then (insert (smap sp) (sd1_spiders_touching_zone habs z smap)) else {})"

fun sd1_sh_zone_intr :: "('a,'e)sd1_habitats \<Rightarrow> 'e sd1_zone \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> bool"
  where
  "sd1_sh_zone_intr habs z smap = (sd1_zone_inter z \<subseteq> sd1_spiders_touching_zone habs z smap)"

fun sd1_sh_zones_intr :: "('a,'e)sd1_habitats \<Rightarrow> 'e sd1_region \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> bool"
  where
  "sd1_sh_zones_intr habs [] smap = True"
  | "sd1_sh_zones_intr habs (z#zs) smap = ((sd1_sh_zone_intr habs z smap) \<and> sd1_sh_zones_intr habs zs smap)"

(* The main interpretation function of a unitary spider diagram. *)
fun sd1_intr :: "('a,'e)sd \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> bool"
  where
  "sd1_intr (sps, habs, shzs) smap = (distinct sps \<and> (inj smap) \<and> (sd1_habitats_intr habs smap) \<and> (sd1_sh_zones_intr habs shzs smap))"
  (*| "sd1_intr (CompoundSD (f, sdl, sdr)) smap = (f (sd1_intr sdl smap) (sd1_intr sdr smap))"*)

lemma "(\<exists>f. distinct [s, s'] \<and> inj f \<and> f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A)) \<longleftrightarrow> (\<exists>f. sd1_intr ([s, s'], [(s, [([A, B],[])]), (s', [([A],[B]), ([B],[A])])], []) f)"
  by (auto)

(* Probably the easiest thing would be to write a translation procedure in ML
and verify the translation via a proof. *)


lemma sd1_distinct_pack [simp]: "\<lbrakk> \<exists>f. sd1_intr (xs @ ys, habs, sh_zones) f \<rbrakk> \<Longrightarrow> \<exists>f. distinct xs \<and> sd1_intr (ys, habs, sh_zones) f"
  by (auto)

lemma sd1_hab_pack [simp]: "\<lbrakk> \<exists>f. sd1_intr (ys, ((s, [([A],[])])#habs), sh_zones) f;  s \<in> set ys\<rbrakk> \<Longrightarrow> \<exists>f. f s \<in> A \<and> sd1_intr (ys, habs, sh_zones) f"
  apply (auto)
  oops



(* RANDOM STUFF *)

lemma "[a, b, c] = []"
  oops

lemma "(\<exists>s s'. s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A) \<and> (A \<inter> B) - (C \<union> D) \<subseteq> {s, s'})"
  oops

lemma "(EX s s'. s : A \<inter> B & s' : (A - B) \<union> (B - A) & (A \<inter> B) - (C \<union> D) \<subseteq> {s, s'})"
  oops

lemma "(\<exists>s s'. s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A) \<and> (A \<inter> B) - (C \<union> D) \<subseteq> {s, s'})"
  oops

lemma "(\<exists>x. P x) = (\<exists>f. P (f x))"
  apply (inference iffI)
  apply (erule exE)
  apply (rule_tac x = "%x. xa" in exI)
  apply (assumption)
  apply (erule exE)
  apply (rule_tac x = "f x" in exI)
  by (assumption)

lemma "(A - B = {}) \<and> x \<in> A \<longrightarrow> x \<in> B"
  by (auto)

lemma "(\<forall>x. D x \<longrightarrow> M x) \<and> (\<forall>y. M y \<longrightarrow> H y) \<longrightarrow> (\<forall>z. D z \<longrightarrow> H z)"
  by (auto)

ML {* print_depth 100 *}
ML {* @{thm impI} *}

(* This looks like something Thomas has suggested. It would be good to
  introduce some shorter notation for zones and regions. *)
definition sd :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "sd xs f P \<equiv> distinct xs \<and> inj f \<and> P"
ML {* @{thm impI} *}

(* This looks like something Thomas has suggested. It would be good to
  introduce some shorter notation for zones and regions. *)
definition sp :: "'a list \<Rightarrow> bool \<Rightarrow> bool"
  where
  "sp xs P \<equiv> distinct xs \<and> P"

definition zone :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set"  ("(_ without _)" 80)
  where
  "zone cs_in cs_out \<equiv> (\<Inter>c \<in> cs_in. c) - (\<Union>c \<in> cs_out. c)"

ML {* @{term "(\<exists>s s' s2 s3. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A))) \<longrightarrow>
                      (\<exists>s s'. sp [s, s'] (s \<in> A \<and> s' \<in> B))"} *}
ML {* @{term "(f s1 \<in> A \<inter> B \<and> f s2 \<in> (A - B) \<union> (B - A)) \<and> f s' \<in> B"} *}
ML {* @{term "(\<exists>f. spider_diagram [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. spider_diagram [s, s'] f (f s \<in> A \<and> f s' \<in> B))"} *}

ML {* PolyML.makestring (MixR.from_hosnf_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"})); *}
ML {* MixR.from_hosnf_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"}); *}
ML {* MixR.from_hosnf_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s'' \<in> (A - B) \<union> (B - A)))"}); *}

(* The proof of the main example using only one second-order existential
  quantification. *)
lemma example_1_b: "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A))) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"
  apply (auto simp add: sd_def)
  apply (rule_tac x = "\<lambda>x.(if x = s then f s' else (if x = s' then f s else f x))" in exI)
  by (auto simp add: inj_on_def)
ML {* MixR.from_hosnf_to_sd (@{term "(\<exists>f. sd [s, s'] f (f s \<in> A \<inter> B \<and> f s' \<in> (A - B) \<union> (B - A)))"}); *}

(* The proof of the main example using many first-order existential
  quantifiers. *)
lemma example_1_b_1: "(\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A))) \<longrightarrow>
                      (\<exists>s s'. sp [s, s'] (s \<in> A \<and> s' \<in> B))"
  by (auto simp add: sp_def, iprover)

(* Here we try to use the zone notation. *)
lemma example_1_b_2: "(\<exists>f. sd [s, s'] f (f s \<in> { A, B } without {} \<and> f s' \<in> ({A} without {B}) \<union> ({B} without {A}))) \<longrightarrow>
                      (\<exists>f. sd [s, s'] f (f s \<in> ({A} without {}) \<and> f s' \<in> ({B} without {})))"
  apply (auto simp add: sd_def zone_def)
  apply (rule_tac x = "\<lambda>x.(if x = s then f s' else (if x = s' then f s else f x))" in exI)
  by (auto simp add: inj_on_def)

lemma example_1_b_3: "(\<exists>s s'. s \<noteq> s' \<and> s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s s'. s \<noteq> s' \<and> s \<in> A \<and> s' \<in> B)"
  by (auto simp add: sp_def, iprover)

lemma example_1_b_4: "(\<exists>s s'. s \<noteq> s' \<and> A s \<and> B s \<and> ((A s' \<and> \<not> B s') \<or> (B s' \<and> \<not>A s'))) \<longrightarrow> (\<exists>s s'. s \<noteq> s' \<and> A s \<and> B s')"
  by (auto simp add: sp_def, iprover)

lemma example_1_step1: "(\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (A - B) \<union> (B - A))) \<longrightarrow>
                        (\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (A - B))) \<or> (\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (B - A)))"
apply (simp)
  by (auto simp add: sp_def)

lemma example_1_step2: "(\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (A - B))) \<or> (\<exists>s s'. sp [s, s'] (s \<in> A \<inter> B \<and> s' \<in> (B - A))) \<longrightarrow>
                        (\<exists>s s'. sp [s, s'] (s \<in> (A \<inter> B) \<union> (B - A) \<and> s' \<in> (A - B) \<union> (A \<inter> B))) \<or> (\<exists>s s'. sp [s, s'] (s \<in> (A \<inter> B) \<union> (A - B) \<and> s' \<in> (B - A) \<union> (A \<inter> B)))"
  by (auto simp add: sp_def)

lemma example_1_step4: "(\<exists>s s'. sp [s, s'] (s \<in> (A \<inter> B) \<union> (B - A) \<and> s' \<in> (A - B) \<union> (A \<inter> B))) \<or> (\<exists>s s'. sp [s, s'] (s \<in> (A \<inter> B) \<union> (A - B) \<and> s' \<in> (B - A) \<union> (A \<inter> B))) \<longrightarrow>
                        (\<exists>s s'. sp [s, s'] (s \<in> A \<and> s' \<in> B))"
  by (simp add: sp_def, iprover intro: sp_def)


(* Using plain form. This is the actual formula we want to x *)
lemma example1_a: "(\<exists>e e'. e \<noteq> e' \<and> e \<in> A \<inter> B \<and> e' \<in> (A \<union> B) - (A \<inter> B)) \<longrightarrow> (\<exists>e e'. e \<noteq> e' \<and> e \<in> A \<and> e' \<in> B)"
  by (auto, iprover)


(* Using plain form. This is the actual formula we want to x *)
lemma example1_b: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<and> s2 \<in> B)"
  by (auto, iprover)

lemma hol_implies_fol: "(\<exists>f. sd [s, s'] f (P (f s) (f s'))) \<longrightarrow> (\<exists>x y. sp [x, y] (P x y))"
  apply (auto simp add: sd_def sp_def)
  apply (rule_tac x = "f s" in exI)
  apply (rule_tac x = "f s'" in exI)
  by (simp add: inj_eq)

lemma sd_outline: "\<exists>s1 s2 s3. distinct [s1, s2, s3] \<and> s1 \<in> (B - (A \<union> C)) \<and> s2 \<in> (B - (A \<union> C)) \<and> s3 \<in> (A - (B \<union> C)) \<union> ((A \<inter> B) - C) \<union> (A \<inter> B \<inter> C) \<and> (B - (A \<union> C)) \<subseteq> {s1, s2}"
  apply (auto simp add: distinct_def)
  oops

ML {* @{thm "allI"} *}

lemma pets_and_rabbits: "(\<forall>x. x \<in> Rabbit \<longrightarrow> x \<in> HasFur) \<and> (\<exists>x. x \<in> Pet \<and> x \<in> Rabbit) \<longrightarrow> (\<exists>x. x \<in> Pet \<and> x \<in> HasFur)"
  by (auto)

lemma reptiles: "(\<forall>x. x \<in> Reptile \<longrightarrow> x \<notin> Furry) \<and> (\<forall>x. x \<in> Snake \<longrightarrow> x \<in> Reptile) \<longrightarrow> (\<forall>x. x \<in> Snake \<longrightarrow> x \<notin> Furry)"
  by (auto)

lemma rockets: "(\<forall>x. x \<in> R \<longrightarrow> x \<in> F) \<and> \<not>(\<exists>x. x \<in> F \<and> x \<in> S) \<longrightarrow> (\<forall>x. x \<in> R \<longrightarrow> x \<notin> S)"
  by (auto)

    (* So the FOL form does not imply the HOL form... *)
(*lemma fol_implies_hol: "(\<exists>x y. (sp [x, y] (P x y)) \<and> distinct [s, s']) \<longrightarrow> (\<exists>f. sd [s, s'] f (P (f s) (f s')))"
  apply (simp add: sp_def sd_def)
  apply (inference impI)
  apply (erule exE)+
  apply (erule conjE)+
  apply (simp)
  apply (rule_tac x = "\<lambda>z. if z = s then x else (if z = s' then y else g z)" in exI)
  apply (auto simp add: inj_eq)
  apply (split split_if_asm)
done*)

(* Now the problem is how to include shaded zones\<dots> How do I go about that? *)

(* And a failed proof just for the fun of it. *)
lemma example_1_a: "(\<exists>f. sd [s, s'] f (f s' \<in> A \<and> f s \<in> B)) \<longrightarrow> (\<exists>f. sd [s, s'] f (f s \<in> A \<and> f s' \<in> B))"
  apply (auto simp add: sd_def)
  apply (rule_tac x = "\<lambda>x.(if x = s then f s' else (if x = s' then f s else f x))" in exI)
  by (auto simp add: inj_on_def)

(*fun spiders :: "'a set \<Rightarrow> bool \<Rightarrow> bool"
where
  "spiders sps P = P"

ML {* @{term "\<lbrakk> smap s \<in> rmap r; r \<subseteq> r' \<rbrakk> \<Longrightarrow> smap s \<in> rmap r'"}  *}
ML {* MixR.traverse_term @{term "\<lbrakk> smap s \<in> rmap r; r \<subseteq> r' \<rbrakk> \<Longrightarrow> smap s \<in> rmap r'"}  *}

lemma "\<lbrakk> spiders { s, s', s'' } (s \<noteq> s' \<and> s' \<noteq> s'') \<rbrakk> \<Longrightarrow> \<exists> s s'. s \<noteq> s'" *)


locale Test =
  fixes IsDog :: "'a \<Rightarrow> bool"
  fixes IsMammal :: "'a \<Rightarrow> bool"
  fixes IsReptile :: "'a \<Rightarrow> bool"
  fixes IsHerbivore :: "'a \<Rightarrow> bool"
  fixes IsOmnivore :: "'a \<Rightarrow> bool"
  fixes IsCarnivore :: "'a \<Rightarrow> bool"
  fixes IsFurry :: "'a \<Rightarrow> bool"
  fixes IsSnake :: "'a \<Rightarrow> bool"

  assumes a1: "IsReptile x \<Longrightarrow> \<not>IsFurry x"
  assumes a2: "IsSnake x \<Longrightarrow> IsReptile x"
  assumes a3: "IsDog x \<Longrightarrow> IsMammal x"
begin

lemma "IsSnake x \<longrightarrow> \<not>IsFurry x"
  apply (inference impI)
  apply (drule a2)
  by (drule a1, assumption)


end

end