theory HeterogeneousStatements
imports IsaDia
begin

section {* MixR test examples *}

(* Spider Diagram translation test. *)
lemma test1: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A)) \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
(*  ML_prf {* GoalsExport.i3p_write_sds_goals () *} *)
  apply(auto)
  oops

(* Spider Diagram translation test. *)
lemma test2: "\<lbrakk> \<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<inter> B \<and> t2 \<in> (A - B) \<union> (B - A) \<rbrakk>
            \<Longrightarrow> (\<exists>u1 u2. distinct[u1, u2] \<and> u1 \<in> A \<and> u2 \<in> B)"
  apply(auto)
  apply (mixr "(EX t1 t2. distinct[t1, t2] & t1 : (A Int B) Un (B - A) & t2 : A - B) --> (EX u1 u2. distinct[u1, u2] & u1 : (A - B) Un (A Int B) & u2 : (A Int B) Un (B - A))")
  apply (mixr "(EX t1 t2. distinct[t1, t2] & t1 : (A Int B) Un (B - A) & t2 : (A - B) Un (A Int B)) --> (EX u1 u2. distinct[u1, u2] & u1 : (A - B) Un (A Int B) & u2 : (A Int B) Un (B - A))")
  apply (mixr "True")
  by (auto)

(* Spider Diagram translation test. *)
lemma test2: "\<exists>s1 s2 s3. distinct[s1, s2, s3] \<and> s1 \<in> A \<and> s2 \<in> B \<and> s3 \<in> (C \<union> D)"
  oops

(* Spider Diagram translation test. *)
lemma test4: "(\<exists>s1 s2 s3. s1 \<noteq> s2 \<and> s1 \<noteq> s3 \<and> s2 \<noteq> s3
              \<and> s1 \<in> A \<and> s1 \<in> B \<union> -C \<and> s1 \<notin> D
              \<and> s3 \<in> (B \<inter> C) - (A \<union> D)
              \<and> s2 \<in> D \<and> s2 \<in> A)
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B)"
  by(auto)

lemma test5: "(\<exists>s1 s2 s3. distinct[s1, s2, s3] \<and> s1 \<in> A \<and> s1 \<in> B \<union> -C \<and> s1 \<notin> D \<and> s3 \<in> (B \<inter> C) - (A \<union> D) \<and> s2 \<in> D \<and> s2 \<in> A) \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B)"
  by(auto)




(* Spider Diagram translation test. *)
lemma test3: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> A \<inter> B \<noteq> {}"
  apply(inference impI)
  apply(inference conjI)


  oops

subsection {* PicProc test examples *}

typedecl PicProcImage
typedecl ShapeType
consts   AreaOf :: "PicProcImage \<Rightarrow> nat" ShapeOf :: "PicProcImage \<Rightarrow> ShapeType"
         Triangle :: "ShapeType" Square :: "ShapeType" Circle :: "ShapeType"
         ShapeA :: "PicProcImage"
lemma "MixR ''ImgUrl:file:///home/matej/Pictures/ShapeA.png'' \<Longrightarrow> ShapeOf ShapeA = Square"
  apply (mixrOracle "[| ShapeOf ShapeA = Square |] ==> ShapeOf ShapeA = Square")
  by (auto)

lemma "MixR ''ImgUrl:file:///home/matej/Pictures/ShapeA.png'' \<Longrightarrow> AreaOf ShapeA > 5000"
  apply (mixrOracle "[| AreaOf ShapeA = 5733 |] ==> 5000 < AreaOf ShapeA")
  by (auto)

section {* Verification of MixR's proof concepts *}
(* ================== MixR Heterogeneous Proof Verification ================== *)

(* Lemma 1: If we have formula A' that is entailed by a premise A, and B'
  entails the conclusion B, then by proving A' \<Longrightarrow> B', we also prove A \<Longrightarrow> B. *)
lemma assumes en1: "A \<Longrightarrow> A'" and en2: "B' \<Longrightarrow> B" and new: "A' \<Longrightarrow> B'"
      shows old: "A \<Longrightarrow> B"
proof -
  assume a: "A"
  show ?thesis using assms a
    by (fast)
qed

(* Lemma 2: If we have a goal G to prove, and we know that G' \<Longrightarrow> G, can we
    then prove G by just proving G'? *)
lemma assumes en1: "G' \<Longrightarrow> G" and new: "G'"
      shows "G"
  by (fast intro: en1 new)

(* Lemma 3: A backwards proof can be applied on a conclusion in HOL if it is a
    conjunction. *)
lemma assumes p1: "B' \<Longrightarrow> B" and p2: "A \<Longrightarrow> B' \<and> C"
  shows "A \<Longrightarrow> B \<and> C"
  by (metis p1 p2)

(* Lemma 4: A backwards proof can be applied on a conclusion in HOL if it is a
    disjunction. *)
lemma assumes p1: "B' \<Longrightarrow> B" and p2: "A \<Longrightarrow> B' \<or> C"
  shows "A \<Longrightarrow> B \<or> C"
  by (metis p1 p2)


section {* Placeholders Theory *}

text {* These are all the definitions that are needed for supporting placeholders: *}

(*typedecl mixr_var
consts
  About :: "'a list \<Rightarrow> mixr_var"

consts
  MixRVars :: "mixr_var list \<Rightarrow> string \<Rightarrow> bool"
  MixR :: "string \<Rightarrow> bool"*)

typedecl person
consts
  Ann :: person
  Bob :: person
  ParentOf :: "person \<Rightarrow> person \<Rightarrow> bool"

axiomatization where
  Relation1: "ParentOf Ann Bob"


lemma "MixR ''NatLang: Ann is a child of Bob.''"
  apply (mixrOracle "MixR ''NatLang: Bob is a parent of Ann.''")
  apply (mixrOracle "ParentOf Ann Bob")
  by (simp add: Relation1)


lemma "MixRVars [About[Ann, Bob]] ''NatLang: Ann is a child of Bob.''"
  apply (mixrOracle "ParentOf Ann Bob")
  oops







lemma "MixR ''TPTP:fof(empty_is_sorted, axiom, sorted(nil)).''"

subsection {* Example 1 *}

text {* Typically, placeholders will need some surrounding theory (like
constants, functions, relations etc.) which the external reasoner of the placeholder
talks about. Without properly connecting the content of the placeholder with the
logic and theory of the hosting reasoner, confusions and invalid inferences might
occur. We demonstrate some of these problems problems and also provide solutions: *}

text {* One problem arises when the placeholder is talking about constants which are in fact
treated as free variables and are thus universally quantified. The example below
demonstrates the problem. It shows an inference step, which misleads us to believe
that the natural language payload is talking about ``Child of'' and ``Parent of''
relations between two persons. Particularly, it says that if Ann is a child of Bob,
then they are in the Isabelle/HOL relation @{text "Child Ann Bob"}. However, the predicate
symbol @{text "Child"} is not a constant, but a free variable. It is thus universally
quantified, which means that the predicate symbol @{text "Child"} is merely a name that
talks about all relations (and not a particular relation, which we might intuitively
expect). *}
axiomatization where
  Inference1: "MixRVars [About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Child Ann Bob"

text {* Given the above inference step, let us try to prove a lemma that exposes the problem.
The lemma merely changes the name of the predicate @{text "Child"} into @{text "Parent"}. The proof
succeeds, as the substitution of @{text "Child"} into @{text "Parent"} yields a unification with the
@{text "Inference1"} axiom and thus produces a ``valid'' proof. *}
lemma "MixRVars[About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Parent Ann Bob"
  by(simp add: Inference1)

(** THE SOLUTION **)
text {* Let us define a constant, which will prevent Isabelle to treat references to @{text "Child"} as
a free variables: *}
consts Child :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
text {* Again, we simulate the inference step that would be otherwise provided by an external reasoner: *}
axiomatization where
  Inference2: "MixRVars[About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Child Ann Bob"

text {* Now the following become unprovable (as expected): *}
lemma "MixRVars[About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Parent Ann Bob"
  oops

text {* Additionally, we may provide another constant @{text "Parent"} and define it in terms of @{text "Child"}: *}
consts Parent :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
defs Parent_def: "Parent x y \<equiv> Child y x"

text {* After this, we can perform the desired reasoning: *}
lemma "MixRVars[About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Parent Bob Ann"
  by(simp add: Inference2 Parent_def)

text {* Furthermore, the following is still not provable: *}
lemma "MixRVars[About[Ann, Bob]] ''Ann is a child of Bob.'' \<Longrightarrow> Parent Ann Bob"
  oops

subsection {* Example 2: Theory without referenced variables *}
text {* A natural language example. Over the sets of humans. *}
locale HumanParents =
  fixes Humans :: "'a set" and
  Owner :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and
  Dogs :: "'a set"
  assumes Inference3: "MixR ''NatLang: Every human has a parent.'' \<Longrightarrow> \<forall>h \<in> Humans. (\<exists>p \<in> Humans. Parent p h)"
begin
lemma "MixR ''NatLang: Every human has a parent.''
       \<and> h \<in> Humans
       \<longrightarrow> (\<exists>p \<in> Humans. Parent p h)"
  by (auto simp add: Inference3)
end

subsection {* Example 3: Referenced variables without a theory *}

text {* Similar example without a surrounding theory, only referenced variables: *}
axiomatization where
  Inference4: "MixRVars [About[Humans, Mortal]] ''NatLang: All humans are mortal'' \<Longrightarrow> \<forall>h \<in> Humans. h \<in> Mortal" and
  Inference5: "MixRVars [About[Greeks, Humans]] ''NatLang: All Greeks are human.'' \<Longrightarrow> \<forall>g \<in> Greeks. g \<in> Humans"

text {* As expected, we can prove lemmata of the following form:  *}
lemma "MixRVars [About[Humans, Mortal]] ''NatLang: All humans are mortal''
       \<and> MixRVars [About[Greeks, Humans]] ''NatLang: All Greeks are human.''
       \<and> g \<in> Greeks
       \<longrightarrow> g \<in> Mortal"
  apply(inference impI)
  apply(erule conjE)+
  apply(drule Inference4 Inference5)+
  by(auto)

text {* Note, however, that the predicates @{text "Humans"}, @{text "Mortal"}, and @{text "Greeks"} are
again free variables. Therefore, thay can be exchanged with any other predicate symbols: *}
lemma "MixRVars [About[Mortal, Greeks]] ''NatLang: All humans are mortal''
       \<and> MixRVars [About[Humans, Mortal]] ''NatLang: All Greeks are human.''
       \<and> h \<in> Humans
       \<longrightarrow> h \<in> Greeks"
  apply(inference impI)
  apply(erule conjE)+
  apply(drule Inference4 Inference5)+
  by(auto)

text {* The above statement is true because we @{text "Inference4"}
and @{text "Inference5"} are merely schematic axioms which establishes
a relation between three variables---regardless of what their names are. *}

subsection {* Example 4: Blocksworld *}
consts LeftOf :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  RightOf :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  Dodec :: "'a \<Rightarrow> bool"
  Tet :: "'a \<Rightarrow> bool"
  Box :: "'a \<Rightarrow> bool"




section {* Placeholders---caveats  *}

axiomatization where
  ErrInference1: "MixR ''x is greater than y'' \<Longrightarrow> x > y" and
  OkayInference1: "MixRVars [About[x, y]] ''x is greater than y'' \<Longrightarrow> x > y"

lemma err1: "MixR ''x is greater than y'' \<Longrightarrow> (0::int) > 1"
  by(fast intro: ErrInference1)

lemma "MixR ''x is greater than y'' = False"
  apply(insert err1)
  by(fastforce)

lemma "MixRVars [About[x, y]] ''x is greater than y'' \<Longrightarrow> (0::int) > 1"
  apply(auto simp add: OkayInference1)
  oops

lemma "MixRVars [About[(0::int), 1]] ''x is greater than y'' \<Longrightarrow> (0::int) > 1"
  apply(insert OkayInference1 [of "0::int" "1::int"])
  by fast




section {* Backward and forward reasoning in MixR *}

lemma backward_step:
      assumes premise: "\<lbrakk>A; B'\<rbrakk> \<Longrightarrow> B" and inference: "B' \<Longrightarrow> B" and rest: "A \<Longrightarrow> B'"
      shows concl:     "A \<Longrightarrow> B"
proof -
  assume a: "A"
  show ?thesis using a premise inference rest
    by auto
qed



end