theory mp1_sol
imports Main
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

(* +3 *)
lemma problem1: "(A \<and> B) \<longrightarrow> (B \<and> A)"
apply (rule impI)
apply (erule conjE)
apply (rule conjI)
apply assumption
apply assumption
done

(* + 4 *)
lemma problem2: "(A \<or> A) \<longrightarrow> (B \<or> A)"
apply (rule impI)
apply (rule disjI2)
apply (erule disjE)
apply (assumption)
apply (assumption)
done

(* +4  *)
lemma problem3: "(A \<and> B) \<longrightarrow> ((\<not>B) \<longrightarrow> (\<not>A))"
apply (rule impI)
apply (erule conjE)
apply (rule impI)
apply (erule notE)
apply assumption
done

(* + 5 *)
lemma problem4: " (A \<longrightarrow> B) \<longrightarrow> ((\<not> B) \<longrightarrow> (\<not> A))"
apply (rule impI)
apply (rule impI)
apply (rule notI)
apply (rule impE, assumption, assumption)
apply (rule notE, assumption, assumption)
done

(* + 5 *)
lemma problem5: "((A \<and> B) \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (rule impE, assumption)
apply (rule conjI, assumption, assumption)
apply assumption
done

(* + 7 *)
lemma problem6: "((\<not> B) \<or> (\<not> A)) \<longrightarrow> (\<not>(A \<and> B))"
apply (rule impI)
apply (rule notI)
apply (rule conjE, assumption)
apply (rule disjE, assumption)
apply (rule notE, assumption, assumption)
apply (rule notE, assumption, assumption)
done

(* + 7 *)
lemma problem7: "(\<not>A \<or> \<not>B) \<longrightarrow> (\<not>(A \<and> B))"
apply (rule impI)
apply (rule notI)
apply (rule conjE, assumption)
apply (rule disjE, assumption)
apply (rule notE, assumption, assumption)
apply (rule notE, assumption, assumption)
done

(* Extra Credit *)
thm classical

(* + 1 *)
lemma problem8: "\<not> \<not> A \<longrightarrow> A"
apply(rule impI)
apply(rule classical)
apply(erule notE)
apply assumption
done

(* + 2 *)
lemma problem9: "A \<or> \<not> A"
apply(rule classical)
apply(rule disjI2)
apply(rule notI)
apply(erule notE)
apply(rule disjI1)
apply assumption
done

(* + 2 *)
lemma problem10: "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
apply(rule impI)
apply(rule impI)
apply(rule classical)
apply(erule impE)
apply(assumption)
apply(erule notE)
apply assumption
done

(* +2 *)
lemma problem11: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
apply(rule impI)
apply(rule classical)
apply(erule impE)
apply(rule impI)
apply(erule notE)
apply assumption
apply assumption
done

(* + 5 *)
lemma problem12: "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
apply (rule iffI)
apply (rule classical)
apply (rule disjI1)
apply (rule notI)
apply (erule notE)
apply (rule conjI)
apply assumption
apply (rule classical)
apply (erule notE)
apply (rule disjI2)
apply assumption
apply (rule notI)
apply (erule conjE)
apply (erule disjE)
apply (erule notE)
apply assumption
apply (erule notE)
apply assumption
done

(* + 3 *)
lemma problem13: "(\<not> A \<longrightarrow> False) \<longrightarrow> A"
apply (rule impI)
apply (rule classical)
apply (erule impE)
apply assumption
apply (rule_tac P = "\<not> A" in notE)
apply (rule notI)
apply assumption
apply assumption
done

end
