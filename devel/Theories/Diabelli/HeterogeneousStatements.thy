theory HeterogeneousStatements
imports Main
begin

(* Lemma 1: If we have formula A' that is entailed by a premise A, then by
  proving A' \<Longrightarrow> B, we also prove A \<Longrightarrow> B. *)
lemma assumes en1: "A \<Longrightarrow> A'" and en2: "B' \<Longrightarrow> B" and new: "A' \<Longrightarrow> B'"
      shows "A \<Longrightarrow> B"
  by (fast intro: en1 en2 new)

end