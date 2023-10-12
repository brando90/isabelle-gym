theory hw3
imports Main
begin

thm allE

lemma problem1: "(∀x. ∀y. P x ⟶ Q y) ⟶( (∃x. P x) ⟶ (∀y. Q y) )"
  apply (rule impI)
  apply (rule impI)
  apply (rule allI)
  apply (erule exE)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done


lemma problem2: "(∀x. ∀y. (P x ∧ P y)) ⟶ ( (∀ x. P x) ∧ (∀ y. P y) )"
  apply (rule impI)
  apply (erule allE)
  apply (rule conjI)
   apply (rule allI)
   apply (erule allE)
   apply (erule conjE)
  apply assumption
  apply (rule allI)
  apply (erule allE)
  apply (erule conjE)
  apply assumption
  done
