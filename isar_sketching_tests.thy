theory isar_sketching_tests
imports Main
begin

(*
lemma "thm"
proof
  have l1 using ... by sorry
  ...
  have ln using ... by sorry
  shows "thm" using l1 ... ln by auto
*)

lemma test1: "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume surj: "surj f" 
  have diagonal_argument: "\<exists>a. {x. x \<notin> f x} = f a" using surj by (simp add: surj_def)
  show "False" using diagonal_argument by auto
qed

lemma test2: "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume surj: "surj f" 
  have diagonal_argument: "\<exists>a. {x. x \<notin> f x} = f a" using surj by sorry
  show "False" using diagonal_argument by blast
qed

end