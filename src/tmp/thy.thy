theory thy
imports Main sexpression_print
begin
lemma problem1: "(A \<and> B) \<longrightarrow> (B \<and> A)"
apply (rule impI)
apply (rule conjI)
