theory predicate_logic_examples_isar
imports Main
begin

(* lemma ex1: "A \<Rightarrow>(B \<Rightarrow> (A \<and> B)))" *)

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma 
  shows "\<lbrakk>A;B\<rbrakk> \<Longrightarrow> (A \<and> B)"
proof -
  assume A: A
  assume B: B
  from A B show "A \<and> B" by (rule conjI)
qed

(* Your turn 1 *)

lemma 
  shows "A \<longrightarrow> (A \<or> B)"
proof (rule impI)
  show "A \<Longrightarrow> (A \<or> B)" by (rule disjI1)
qed

lemma 
  shows "A \<longrightarrow> (A \<or> B)"
proof (rule impI)
  assume A: A
  from A show "(A \<or> B)" by (rule disjI1)
qed

(* Example 4: (A \<Rightarrow> B) \<Rightarrow> ((B \<Rightarrow> C) \<Rightarrow> (A \<Rightarrow> C)) *)

thm impI (* (?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q *)
thm impE (* \<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma
  shows "(A \<Longrightarrow> B) \<Longrightarrow> ((B \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> C))"
proof -
  assume A2B: "A\<Longrightarrow>B"
  assume B2C: "B\<Longrightarrow>C"
  assume A: "A"
  from A2B have A22B: "A\<longrightarrow>B" by (rule impI)
  from B2C have A22C: "B\<longrightarrow>C" by (rule impI)
  have B: "B" proof -
    from A22B A show "B" by (rule impE) qed
  show "C" proof -
    from A22C B show "C" by (rule impE) qed
qed

(* Your turn 2:  (A \<and> B) \<Rightarrow> (A \<or> B) *)

thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma
  shows "A \<and> B \<longrightarrow> A \<or> B"
proof (rule impI)
  assume AnB: "A \<and> B"
  have AB2ArB: "A \<Longrightarrow> B \<Longrightarrow> A \<or> B" by (rule disjI1)
  from AnB AB2ArB show "A \<or> B" by (rule conjE)
qed

end