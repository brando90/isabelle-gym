theory datatypes_pg
  imports Main
begin

datatype mybool = T | F

fun not :: "mybool \<Rightarrow> mybool" where
  "not T = F" |
  "not F = T"

lemma "not (not b) = b" 
  apply (cases b) 
  apply simp 
  by simp

lemma
  shows "not (not b) = b"
proof (cases b)
case T
  then show ?thesis by simp
next
  case F
  then show ?thesis by simp
qed

(* my nat *)

value "Suc"
datatype my_nat = Zero | suc my_nat
value "Zero"
value "suc"
value "suc Zero" (* 1 *)

fun my_add :: "my_nat \<Rightarrow> my_nat \<Rightarrow> my_nat" where 
"my_add Zero n = n" |
"my_add (suc m) n = suc( my_add m n)"

(* induction say for 2 constructors
 1. my_add Zero Zero = Zero
 2. \<And>m. my_add m Zero = m \<Longrightarrow> my_add (suc m) Zero = suc m

 1. my_add Zero C1  = Zero
 2. \<And>m. my_add m Zero = m \<Longrightarrow> my_add (suc m) Zero = suc m
*)
lemma "my_add_0": "my_add m Zero = m"
  apply (induction m)
   apply simp
  by simp

(* type with more than 1 argument *)

datatype tau = 
C0 |
C1 tau |
C2 tau tau


end