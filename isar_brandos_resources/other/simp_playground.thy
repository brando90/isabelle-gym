theory simp_playground
  imports Main
begin

datatype 'a boolexp =
   TRUE 
  | FALSE 
  | Var 'a 
  | Not "'a boolexp"
  | And "'a boolexp" "'a boolexp"
  | Or "'a boolexp" "'a boolexp"
  | Implies "'a boolexp" "'a boolexp"
print_theorems

fun boolexp_eval :: "('a \<Rightarrow> bool) \<Rightarrow> 'a boolexp \<Rightarrow> bool" where
   "boolexp_eval env TRUE = True"
 | "boolexp_eval env FALSE = False"
 | "boolexp_eval env (Var x) = env x"
 | "boolexp_eval env (Not b) = (\<not> (boolexp_eval env b))"
 | "boolexp_eval env (And a b) = ((boolexp_eval env a) \<and> (boolexp_eval env b))"
 | "boolexp_eval env (Or a b) = ((boolexp_eval env a) \<or> (boolexp_eval env b))"
 | "boolexp_eval env (Implies a b) = ((\<not> (boolexp_eval env a)) \<or> (boolexp_eval env b))"

definition env1 where "env1 \<equiv> (\<lambda> x. case x of (0::nat) \<Rightarrow> True | _ \<Rightarrow> False)"

value "boolexp_eval env1 (Not (Var (1::nat)))"

lemma  "boolexp_eval env1 (Not (Var (1::nat))) = True"
  apply (simp only: env1_def)
  apply (simp only: boolexp_eval.simps(4))
  by simp

lemma "A \<longrightarrow> A \<and> B = (if A then B else False)" by simp

end