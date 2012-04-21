theory HeterogeneousStatements
imports Main
uses
  "GoalsExport.ML"
begin

(* Spider Diagram translation test. *)
lemma test1: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
  oops

(* Spider Diagram translation test. *)
lemma test2: "\<lbrakk> \<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A) \<rbrakk>
            \<Longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B) \<and> (A \<inter> B) \<noteq> {}"
  oops

(* Spider Diagram translation test. *)
lemma test3: "(\<exists>s1 s2. distinct[s1, s2] \<and> s1 \<in> A \<inter> B \<and> s2 \<in> (A - B) \<union> (B - A))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B)"
  oops

(* Spider Diagram translation test. *)
lemma test4: "(\<exists>s1 s2 s3. s1 \<noteq> s2 \<and> s1 \<noteq> s3 \<and> s2 \<noteq> s3
              \<and> s1 \<in> A \<and> s1 \<in> B \<union> -C \<and> s1 \<notin> D
              \<and> s3 \<in> (A \<inter> B) - (C \<union> D))
              \<longrightarrow> (\<exists>t1 t2. distinct[t1, t2] \<and> t1 \<in> A \<and> t2 \<in> B)"
  oops

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

(* Lemma 3: A backward proof can be applied on a conclusion in HOL if it is a
    conjunction. *)
lemma assumes p1: "B' \<Longrightarrow> B" and p2: "A \<Longrightarrow> B' \<and> C"
  shows "A \<Longrightarrow> B \<and> C"
  by (metis p1 p2)

(* Lemma 4: A backward proof can be applied on a conclusion in HOL if it is a
    disjunction. *)
lemma assumes p1: "B' \<Longrightarrow> B" and p2: "A \<Longrightarrow> B' \<or> C"
  shows "A \<Longrightarrow> B \<or> C"
  by (metis p1 p2)

end