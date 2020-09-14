theory test
 imports Main sexpression_print
 begin
 lemma problem1: "(A \<and> B) \<longrightarrow> (B \<and> A)"
  apply (rule impI)
ML_val "List.map to_sexpr_untyped (Thm.prems_of (#goal @{Isar.goal}))"
  apply (rule conjI)
sorry
end
