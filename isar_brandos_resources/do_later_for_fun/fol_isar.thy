theory fol_isar
  imports Main
begin

thm allE (* \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma "(\<exists> x. \<forall> y. x \<le> y) \<longrightarrow> (\<forall>x. \<exists> y. y \<le> x)"

lemma
  assumes "(\<exists> x. \<forall> y. x \<le> y)"
  shows "(\<forall>x. \<exists> y. y \<le> x)"
proof (rule allI)
  show "\<And>x. \<exists>y. y \<le> x" proof -
    fix x
 
end