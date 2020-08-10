theory mp1
imports Main sexpression_print
begin

(*
In this exercise, you will prove some lemmas of propositional
logic with the aid of a calculus of natural deduction.

For the proofs, you may only use "assumption", and the following rules
with rule, erule, rule_tac or erule_tac.  You may also use lemmas that
you have proved so long as they meet the same restriction.
*)

thm notI
thm notE
thm conjI
thm conjE
thm disjI1
thm disjI2
thm disjE
thm impI
thm impE
thm iffI
thm iffE

(*
notI: (P \<Longrightarrow> False) \<Longrightarrow> \<not> P
notE: \<lbrakk> \<not> P; P \<rbrakk> \<Longrightarrow> Q
conjI: \<lbrakk> P; Q \<rbrakk> \<Longrightarrow> P \<and> Q
conjE: \<lbrakk> P \<and> Q; \<lbrakk> P; Q \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R
disjI1: P \<Longrightarrow> P \<or> Q
disjI2: Q \<Longrightarrow> P \<or> Q
disjE: \<lbrakk> P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R
impI: (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
impE: \<lbrakk> P \<longrightarrow> Q; P; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R
iffI: \<lbrakk> P \<Longrightarrow> Q; Q \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P = Q
iffE: \<lbrakk> P = Q; \<lbrakk> P \<longrightarrow> Q; Q \<longrightarrow> P \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R

Prove:
*)


lemma problem1: "(A \<and> B) \<longrightarrow> (B \<and> A)"
  apply (rule impI)
  apply (rule conjI)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  print_state
  ML_val "@{Isar.goal}"
  ML_val "List.map to_sexpr_untyped (Thm.prems_of (#goal @{Isar.goal}))"
  apply assumption
done

lemma problem2: "(A \<or> B) \<longrightarrow> (B \<or> A)"
  apply (rule impI)
  apply (rule disjE)
    apply assumption
   apply (rule disjI2)
  apply assumption
   apply (rule disjI1)
  apply assumption
done

lemma problem3: "(A \<and> B) \<longrightarrow> ((\<not>B) \<longrightarrow> (\<not>A))"
  apply (rule impI)
  apply (rule impI)
  apply (erule notE)
  apply (erule conjE)
  apply assumption
done
 
lemma problem4: " (A \<longrightarrow> B) \<longrightarrow> ((\<not> B) \<longrightarrow> (\<not> A))"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
done

lemma problem5: "((A \<and> B) \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply assumption
done

lemma problem6: "((\<not> B) \<or> (\<not> A)) \<longrightarrow> (\<not>(A \<and> B))"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
  apply assumption
  apply (erule notE)
  apply assumption  
done

lemma problem7: "(\<not>A \<or> \<not>B) \<longrightarrow> (\<not>(A \<and> B))"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
  apply assumption
  apply (erule notE)
  apply assumption  
done

(* Extra Credit *)
thm classical

lemma doubleE: "\<not> \<not> A \<Longrightarrow> A"
  apply (rule classical)
  apply (erule notE)
  apply assumption
done

lemma problem8: "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule doubleE)
  apply assumption
done

lemma problem9: "A \<or> \<not> A"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule doubleE)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
done

lemma problem10: "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
  apply (rule impI)
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
done

lemma problem11: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption
  apply assumption
done

lemma dem1: "(\<not> (A \<and> B)) \<Longrightarrow> (\<not> A \<or> \<not> B)"
  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
  apply (rule classical)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule classical)
   apply (erule notE)
   apply (rule disjI2)
   apply assumption
done

lemma dem2: " (\<not> A \<or> \<not> B) \<Longrightarrow> (\<not> (A \<and> B))" (* not classical *)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply assumption
done

lemma problem12: "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)
   apply (rule dem1)
  apply assumption
  apply (rule dem2)
  apply assumption
done

lemma problem13: "(\<not> A \<longrightarrow> False) \<longrightarrow> A"
  apply (rule impI)
  apply (rule doubleE)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply assumption
done

end
