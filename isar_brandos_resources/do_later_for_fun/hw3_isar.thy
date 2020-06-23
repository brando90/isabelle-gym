theory hw3_isar
  imports Main
begin

thm allE (* \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
(* same as infinite AND in the assumption, 
so we have ALL P x's in the assumption for concluding R.
But since we only need 1 really to conclude the proof we choose once as the other
assumption to get R *)
thm allI (* \<And>x. ?P x) \<Longrightarrow> \<forall>x. ?P x *)
(* same as an infite AND in the conclusion. So we need to be able to have that P x is
true for ALL x's. Then we can conclude it's really true forall x's and introduce
the atomic formula \<forall>x. ?P x *)
thm exE (* \<lbrakk>\<exists>x. ?P x; \<And>x. ?P x \<Longrightarrow> ?Q\<rbrakk> \<Longrightarrow> ?Q *)
(* same as a infinite or in the assumption. 
So to eliminate it we need to be able to show the conclusion Q holds for all values 
of x. Why? Because we don't know WHICH value make it true. Was it P x1 or P x2 or...?
Well then we have to show it's true regardless of the one we assumed.
Choose them all and does that imply the conlcusion Q? 
*)
thm exI (* ?P ?x \<Longrightarrow> \<exists>x. ?P x *)
(* To introduce the atomic formula exists P x we need to exhibit an example x that 
makes P x hold. If we have P x then forget that x but claim the atomic formula that
there exist's an x s.t. P x. 
*)

lemma problem1: "(\<forall>x. \<forall>y. P x \<longrightarrow> Q y) \<longrightarrow>( (\<exists>x. P x) \<longrightarrow> (\<forall>y. Q y) )"
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

thm allE (* \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma problem1_isar: 
  assumes "(\<forall>x. \<forall>y. P x \<longrightarrow> Q y)"
  shows "( (\<exists>x. P x) \<longrightarrow> (\<forall>y. Q y) )"
proof (rule impI)
  show ?thesis



lemma problem2: "(\<forall>x. \<forall>y. (P x \<and> P y)) \<longrightarrow> ( (\<forall> x. P x) \<and> (\<forall> y. P y) )"
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

end