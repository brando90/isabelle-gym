theory chapter5_exercises_test
imports Main sexpression_print
begin

(*
Exercise 5.1. Give a readable, structured proof of the following lemma:
*)

thm allE (* \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
thm exE (* \<lbrakk>\<exists>x. ?P x; \<And>x. ?P x \<Longrightarrow> ?Q\<rbrakk> \<Longrightarrow> ?Q *)
lemma exercise5p1_apply:
"\<lbrakk> \<forall>x y. T x y \<or> T y x;(\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y);(\<forall>x y. T x y \<longrightarrow> A x y); A x y\<rbrakk> \<Longrightarrow> T x y"
  by metis

thm HOL.mp (* \<lbrakk>?P \<longrightarrow> ?Q; ?P\<rbrakk> \<Longrightarrow> ?Q *)
thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma exercise5p1:
  assumes T: "\<forall>x y. T x y \<or> T y x" 
    and   A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y" 
    and   TA: "\<forall>x y. T x y \<longrightarrow> A x y" 
    and   "A x y" 
  shows "T x y"
proof - 
  have T2: "T x y \<or> T y x" using T by simp
  print_state
  ML_val "List.map to_sexpr_untyped (Thm.prems_of (#goal @{Isar.goal}))"
  have exercise5p1 sorry
qed

end