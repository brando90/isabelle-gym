theory mp1_isar
imports Main
begin

(* lemma problem1: "(A \<and> B) \<longrightarrow> (B \<and> A)" *)
thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)

lemma problem1_attempt5: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  show "B \<and> A" using `A \<and> B` 
  proof (rule conjE)
    assume B and A
    show "B \<and> A" using `B` `A` by (rule conjI)
  qed
qed

(*
lemma problem1_attempt6: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  show "B \<and> A" using `A \<and> B` 
  proof -
    apply (rule conjE)
    assume B and A
    show "B \<and> A" using `B` `A` by (rule conjI)
  qed
qed
*)

(* lemma problem2: "(A \<or> B) \<longrightarrow> (B \<or> A)" *)

thm disjE (* \<lbrakk>?P \<or> ?Q; ?P \<Longrightarrow> ?R; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
thm disjI1 (* ?P \<Longrightarrow> ?P \<or> ?Q *)

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume "A \<or> B"
  show "B \<or> A" using `A \<or> B`
  proof (rule disjE)
    show "A \<Longrightarrow> B \<or> A" by (rule disjI2) 
    show "B \<Longrightarrow> B \<or> A" by (rule disjI1)
  qed
qed

(* lemma problem3: "(A \<and> B) \<longrightarrow> ((\<not>B) \<longrightarrow> (\<not>A))" *)
thm notI (* (?P \<Longrightarrow> False) \<Longrightarrow> \<not> ?P *)
thm notE (* \<lbrakk>\<not> ?P; ?P\<rbrakk> \<Longrightarrow> ?R *)
thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma
  shows "(A \<and> B) \<longrightarrow> ((\<not>B) \<longrightarrow> (\<not>A))"
proof (rule impI)
  assume AnB: "A \<and> B"
  have A: "A" using AnB by (rule conjE)
  have B: "B" using AnB by (rule conjE)
  show nB2nA: "(\<not>B) \<longrightarrow> (\<not>A)" proof (rule impI)
    assume nB: "\<not> B"
    show "\<not> A" proof (rule notI)
      from nB B show "False" by (rule notE)
    qed
  qed
qed

(* lemma problem5: "((A \<and> B) \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))" *)
thm impE (* *)
lemma my_mp: "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B" by (erule impE)
thm impI

lemma "\<lbrakk>A \<Longrightarrow> B \<Longrightarrow> C \<rbrakk> \<Longrightarrow> (A \<longrightarrow> B \<longrightarrow> C)"
  apply (rule impI)
  apply (rule impI)
  by assumption

lemma
  shows "((A \<and> B) \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
proof (rule impI)
  assume AnBiC: "(A \<and> B) \<longrightarrow> C"
  have A2B2C: "A \<Longrightarrow> B \<Longrightarrow> C" using AnBiC proof-
    assume A: A and B: B
    have AnB: "A \<and> B" using A B by (rule conjI)
    show C: "C" using AnB AnBiC by (rule my_mp)
  qed
  have Big2Big: "\<lbrakk>A \<Longrightarrow> B \<Longrightarrow> C \<rbrakk> \<Longrightarrow> (A \<longrightarrow> B \<longrightarrow> C)" proof (rule impI)
    show "\<lbrakk>\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C; A\<rbrakk> \<Longrightarrow> B \<longrightarrow> C" proof (rule impI)
      show "\<lbrakk>\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C; A; B\<rbrakk> \<Longrightarrow> C" by assumption
    qed
  qed
  (* show "(A \<longrightarrow> B \<longrightarrow> C)" using A2B2C Big2Big by (drule my_mp) *)
  oops


end