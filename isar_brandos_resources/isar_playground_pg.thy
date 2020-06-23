theory isar_playground_pg
imports Main
begin

lemma duper_simple0: "A\<longrightarrow>A"
  apply (rule impI)
  apply assumption
  done

lemma duper_simple1: "A\<longrightarrow>A"
proof (rule impI)
  show "A\<Longrightarrow>A" by assumption
qed

lemma
  assumes "A"
  shows "A"
proof -
  from assms show "A" by assumption
qed

lemma
  assumes "A"
  shows "A"
proof -
  show "A" using assms by assumption
qed

thm impI (* (?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q *)
lemma 
  shows "A\<longrightarrow>A"
proof -
  have A2A: "A\<Longrightarrow>A" by assumption
  from A2A show "A\<longrightarrow>A" by (rule impI)
qed

(* *)

lemma "A \<longrightarrow> A \<or> B"
  apply (rule impI) (* A \<Longrightarrow> A \<or> B *)
  thm disjI1 (* ?P \<Longrightarrow> ?P \<or> ?Q *)
  apply (rule disjI1) (* A \<Longrightarrow> A *)
  by assumption

lemma very_simple2: "A \<longrightarrow> A \<or> B"
proof (rule impI) (* goal: A\<Longrightarrow>A\<or>B *)
  assume A
  from this show "A \<or> B" by (rule disjI1)
qed

lemma "A \<longrightarrow> A \<or> B"
proof (rule impI) (* goal: A\<Longrightarrow>A\<or>B *)
  assume 0: A
  show "A \<or> B" using 0 by (rule disjI1)
qed

lemma "A \<longrightarrow> A \<or> B"
proof (rule impI)
  assume A
  then show "A \<or> B" by (rule disjI1)
qed

lemma "A \<longrightarrow> A \<or> B"
proof (rule impI)
  assume A
  thus "A \<or> B" by (rule disjI1)
qed

thm disjI1 (* ?P \<Longrightarrow> ?P \<or> ?Q *)
lemma
  assumes A: "A"
  shows "A \<or> B"
proof -
  from A show "A \<or> B" by (rule disjI1)
qed

lemma
  assumes"A"
  shows "A \<or> B"
proof -
  from assms show "A \<or> B" by (rule disjI1)
qed

(* different proof of "A \<longrightarrow> A \<or> B  *)

lemma "A \<longrightarrow> A \<or> B"
proof (rule impI)
  show "A \<Longrightarrow> A \<or> B" by (rule disjI1)
qed

lemma "A \<longrightarrow> A \<or> B"
proof
  show "A \<Longrightarrow> A \<or> B" by (rule disjI1)
qed

(* Exercise: A \<Longrightarrow>(B \<Longrightarrow> (A \<and> B)) *)

(* TODO
lemma " A \<longrightarrow> (B \<longrightarrow> (A \<and> B)) "
proof -
  assume 0: "A" and 1: "B"
  have "A \<Longrightarrow> (B \<longrightarrow> (A \<and> B))" by (rule impI)
*)

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma 
  assumes A B
  shows "A \<and> B"
proof -
  from assms show "A \<and> B" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma 
  assumes A and B
  shows "A \<and> B"
proof -
  from assms show "A \<and> B" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma 
  shows "\<lbrakk>A;B\<rbrakk> \<Longrightarrow> (A \<and> B)"
proof -
  show "A \<Longrightarrow> (B \<Longrightarrow>A \<and> B)" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma "A \<Longrightarrow> (B \<Longrightarrow> (A \<and> B))"
proof -
  assume A B
  from this show "A \<and> B" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma "A \<Longrightarrow> (B \<Longrightarrow> (A \<and> B))"
proof -
  assume A B
  from this show "A \<Longrightarrow> (B \<Longrightarrow> (A \<and> B))" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma 
  assumes A and B
  shows "A \<and> B"
proof -
  from assms show "A \<and> B" by (rule conjI)
qed

thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
lemma "A \<Longrightarrow> (B \<Longrightarrow> (A \<and> B))"
proof -
  assume 0: "A"
  assume 1: "B"
  from 0 1 show "A \<and> B" by (rule conjI)
qed

lemma 
  assumes 0: "A"
  assumes 1: "B"
  shows "A \<and> B"
  thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
proof -
  from 0 1 show "A \<and> B" by (rule conjI)
qed

lemma 
  assumes "A"
  assumes "B"
  shows "A \<and> B"
  thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
proof -
  from assms show "A \<and> B" by (rule conjI)
qed

lemma 
  assumes "A"
  assumes "B"
  shows "A \<and> B"
  thm conjI (* \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q *)
proof -
  show "A \<and> B"using assms by (rule conjI)
qed

(* \<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R  *)

thm impE (* \<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma "\<lbrakk>P \<longrightarrow> Q; P; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
proof -
  show "\<lbrakk>P \<longrightarrow> Q; P; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" by (erule impE) (* why do both rule & erule work? *)
qed

lemma
  assumes "P\<longrightarrow>Q" P "Q\<Longrightarrow>R"
  shows R
proof -
  from assms show R by (rule impE) (* why can't we do erule? *)
qed

(* Exercise: (A \<Longrightarrow> B) \<Longrightarrow> ((B \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> C)) *)
(* TODO
thm impE (* \<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma " (A \<longrightarrow> B) \<Longrightarrow> ((B \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> C))"
  apply (erule impE)

lemma " (A \<Longrightarrow> B) \<Longrightarrow> ((B \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> C))"
proof -
  assume "A \<Longrightarrow> B"
  assume "B \<Longrightarrow> C"
  have "(B \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow>C)"
*)


(* 
Modus Ponens
A \<Rightarrow> B A
======== MP
B
*)

thm impE (* \<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma Mod_Pon: "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
  apply (erule impE)
   apply assumption
  by assumption

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  show "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B" by (erule impE)
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume "A" "A\<longrightarrow>B"
  from this show "B" by simp
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume "A" "A\<longrightarrow>B"
  then show "B" by simp
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume "A" "A\<longrightarrow>B"
  thus "B" by simp
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume 0: "A" "A\<longrightarrow>B"
  show "B" using 0 by simp (* doesn't like this here *)
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume 0: "A" "A\<longrightarrow>B"
  show "B" using 0 by simp
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume 0: "A"
  assume 1: "A\<longrightarrow>B"
  show "B" using 0 1 by simp
qed

lemma "\<lbrakk>A;A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B"
proof -
  assume 0: "A"
  assume 1: "A\<longrightarrow>B"
  with 0 show "B" by simp
qed

lemma
  assumes "A" "A\<longrightarrow>B"
  shows "B"
proof -
  from assms show "B" by simp (* improve by using rule/erule*)
qed

lemma
  assumes "A" "A\<longrightarrow>B"
  shows "B"
proof -
  from assms show "B" by simp (* improve by using rule/erule*)
qed

lemma
  assumes "A" "A\<longrightarrow>B"
  shows "B"
proof -
  show "B" using assms by simp (* improve by using rule/erule*)
qed

(* TODO curious about this one
lemma Mod_Pon2: "\<lbrakk>A;A\<Longrightarrow>B\<rbrakk>\<Longrightarrow>B"
*)

(*
A \<Rightarrow> B A B
Imp E
B
*)
lemma Imp_Elim: "\<lbrakk>A \<longrightarrow> B;A;B\<rbrakk>\<Longrightarrow>B"
  apply (erule impE)
   apply assumption
  by assumption

(*
Left Conjunct
A \<and> B
==== AndL
A
A \<and> B A
AndL E
A
Right Conjunct
A \<and> B
==== AndR
B
A \<and> B B
AndR E
B
*)

(* problem 1: (A \<and> B) \<longrightarrow> (A \<or> B) *)
thm impI (* (?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q *)
thm disjI1 (* ?P \<Longrightarrow> ?P \<or> ?Q *)
thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (rule disjI1)
  apply (erule conjE)
  by assumption

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  by assumption

(* TODO: why didn't this require conjE? *)
lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof (rule impI)
  assume 0: "A \<and> B"
  thm this
  from this have "A" by simp
  from this show "A \<or> B" by (rule disjI1)
qed

lemma 
  assumes "A \<and> B"
  shows "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof
  from assms have "A" by simp
  from this show "A \<or> B" by (rule disjI1)
qed

lemma 
  assumes "A \<and> B"
  shows "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof
  from assms have "A" by simp
  then show "A \<or> B" by (rule disjI1)
qed

lemma 
  assumes "A \<and> B"
  shows "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof
  have "A" using assms by simp
  thus "A \<or> B"  by (rule disjI1)
qed

lemma 
  assumes "A \<and> B"
  shows "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof
  have 0: "A" using assms by simp
  show "A \<or> B" using 0 by (rule disjI1)
qed

(* lemma problem2: "(A \<or> B) \<longrightarrow> (B \<or> A)" *)

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume "(A \<or> B)"
  from this show "B \<or> A" by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume "(A \<or> B)"
  then show "B \<or> A" by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume "(A \<or> B)"
  thus "B \<or> A" by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume "(A \<or> B)"
  thus "B \<or> A" by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume 0: "(A \<or> B)"
  show "B \<or> A" using 0 by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume 0: "(A \<or> B)"
  from 0 show "B \<or> A" by auto
qed

lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume 0: "(A \<or> B)"
  with 0 show "B \<or> A" by auto (* silly you don't need 0 really*)
qed

lemma 
  assumes "(A \<or> B)"
  shows "(B \<or> A)"
proof -
  from assms show "B \<or> A" by auto
qed

lemma 
  assumes "(A \<or> B)"
  shows "(B \<or> A)"
proof -
  show "B \<or> A" using assms by auto
qed

thm disjE (* \<lbrakk>?P \<or> ?Q; ?P \<Longrightarrow> ?R; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
thm disjI1 (* thm disjI1  *)
lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume 0: "(A \<or> B)"
  from 0 show "B" by simp
  oops

(* 5.1 *)


(* 
http://www21.in.tum.de/~ballarin/belgrade08-tut/session03/session03.pdf
blast = tableaux prover (good for predicate)
metis = resolution prover for FOL with equality
clarify = applies all safe rules that do not split goal
safe = apply all safe rules

TODO: resolution prover, tableaux prover, safe rules.
*)
 
lemma example_apply_script: "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
  apply (rule notI)
  apply (simp add: surj_def)
  apply (erule allE)
  apply (erule exE)
  sorry

thm notI (* (?P \<Longrightarrow> False) \<Longrightarrow> \<not> ?P *)
thm surj_def (* surj ?f = (\<forall>y. \<exists>x. y = ?f x) *)

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
assume 0: "surj f"
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def )
  from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by metis
  from 2 show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof safe
  assume "surj f"
  thm this
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by (simp add: surj_def)
  thm this
  from this show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by (simp add: surj_def)
  from this show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof safe
  assume 0: "surj f"
  have 1: "\<exists>a. {x. x \<notin> f x} = f a" using 0 by (simp add: surj_def)
  show "False" using 1 by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume "surj f"  (* surj ?f = (\<forall>y. \<exists>x. y = ?f x) *)
(* if it's surjective then some a must map to the Diagonal set via f *)
  (* hence "\<exists>a. f a = {x. x \<notin> f x} " by (simp add: surj_def) *)
 (*above failed cuz unification failed, RHS is a set but surj is stated with RHS as f x, LHS set*)
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (simp add: surj_def)
(* this is a contradiction cuz by def of D then a \<notin> f a but then that means its in D and a \<in> f a since f a = D
  so by law of excluded middle then a must be in a if the first is a contradiction but running the argument backwards get a contradiction
 i.e. if a \<in> f a then a is in D so it satisfies the property of elements of D namely a \<notin> f a contradiction *)
  thus "False" by auto
qed

definition Diag where "Diag f \<equiv> {x. x \<notin> f x}"

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume "surj f"
  hence "\<exists>a. (Diag f) = f a" by (auto simp add: Diag_def)
  thus "False" by (auto simp add: Diag_def)
qed

(* why doesn't it like my metis proofs? *)

(* TODO: make everything explicit *)
(*
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume "surj f"
  from this have 0: "\<exists>a.{x. x \<notin> f x} = f a" by (simp add: surj_def)
  fix  (* "a. {x. x \<notin> f x} = f a" *)
  from 0 have 1: "a \<in> (f a)" by simp
  from 0 have 2: "a \<notin> (f a)" by metis
  from 1 from 2 show "False" by metis
  sorry

*)

lemma "False\<Longrightarrow>False"
proof -
  assume 0: "False"
  from 0 show "False" by blast
qed

lemma
  assumes "False" 
  shows goal: "False" 
proof -
  from assms have "False" by assumption
  thus "False" by blast
qed

lemma
  assumes A1: "False" 
  shows goal1: "False" 
proof -
  from A1 have "False" by assumption
  thus "False" by blast
qed

lemma
  assumes A1: "False" 
  shows goal2: "False" 
proof -
  from A1 show "False" by blast
qed

thm goal2

lemma "False \<Longrightarrow> False" by (simp add: goal2)

lemma 
  fixes f :: " 'a \<Rightarrow> 'a set" 
  assumes s: "surj f" and "True"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def) 
  thus "False" by blast
qed

lemma 
  fixes f :: " 'a \<Rightarrow> 'a set" 
  assumes s: "surj f" and "True"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def) 
  from this show "False" by blast
qed

lemma 
  fixes f :: " 'a \<Rightarrow> 'a set" 
  assumes s: "surj f"
  shows my_lemma: "False"
proof -
  have 0: "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def) 
  show "False" using 0 by blast
qed

thm my_lemma

(* 5.2 Proof Patterns *)

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume 0: "surj f" 
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def ) 
  from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast
  from 2 show "False" by blast 
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume 0: "surj f" 
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def ) 
  from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast 
  from 2 have 3: "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  from 3 show "False" by blast 
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume 0: "surj f" 
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def ) 
  from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast 
  from 2 show "False" by blast 
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" proof
assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x } = f a" by (auto simp: surj_def) 
  then obtain a where "{x. x \<notin> f x } = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" proof
assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x } = f a" by (auto simp: surj_def) 
  then obtain a where "{x. x \<notin> f x } = f a" by blast
  thus "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" proof
assume "surj f"
  hence 0: "\<exists>a. {x. x \<notin> f x } = f a" by (auto simp: surj_def) 
  obtain a where "{x. x \<notin> f x } = f a" using 0 by blast
  thus "False" by blast
qed

(* 5.3.1 Streamling & quotations *)

lemma 
  shows "A\<longrightarrow>A"
proof -
  show "A\<longrightarrow>A" (is "?A1 \<longrightarrow> ?A2")
  proof (rule impI)
    assume "?A1"
    from this show "?A2" by (assumption)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  assume 0: "A \<or> B"
  from this show "(A \<or> B) \<Longrightarrow> (B \<or> A)" (is "?L \<Longrightarrow> ?R")
  proof -
    have 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    have 2: "B \<Longrightarrow> ?R" by (rule disjI1)
    from 0 1 2 show "B \<or> A" by (rule disjE)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  let ?L = "A \<or> B"
  let ?R = "B \<or> A"
  assume 0: ?L
  from this show "?R"
  proof -
    have 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    have 2: "B \<Longrightarrow> ?R" by (rule disjI1)
    from 0 1 2 show "?R" by (rule disjE)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  let ?L = "A \<or> B" and ?R = "B \<or> A"
  assume 0: ?L
  from this show "?R"
  proof (rule disjE)
    show 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    show 2: "B \<Longrightarrow> ?R" by (rule disjI1)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  let ?L = "A \<or> B" and ?R = "B \<or> A"
  assume 0: ?L
  from this show "?R"
  proof -
    have 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    have 2: "B \<Longrightarrow> ?R" by (rule disjI1)
    from 0 1 2 show "?R" by (rule disjE)
  qed
qed

lemma 
  shows "A\<longrightarrow>A"
proof -
  have "A\<Longrightarrow>A" by assumption
  from `A\<Longrightarrow>A` show "A\<longrightarrow>A" by (rule impI)
qed

lemma problem1_attempt1: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume AnB: "A \<and> B"
  from AnB have A: A by (rule conjE)
  from AnB have B: B by (rule conjE)
  from B A show "B \<and> A" by (rule conjI)
qed

lemma problem1_attempt2: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  from `A\<and>B` have A: A by (rule conjE)
  from `A\<and>B` have B: B by (rule conjE)
  from B A show "B \<and> A" by (rule conjI)
qed

(* 5.3.2 moreover *)

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  let ?L = "A \<or> B" and ?R = "B \<or> A"
  assume 0: ?L
  from this show "?R"
  proof -
    have 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    have 2: "B \<Longrightarrow> ?R" by (rule disjI1)
    from 0 1 2 show "?R" by (rule disjE)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)"
proof
  let ?L = "A \<or> B" and ?R = "B \<or> A"
  assume 0: ?L
  thus "?R"
  proof -
    have "?L" using 0  by assumption
    moreover have "A \<Longrightarrow> ?R" by (rule disjI2) 
    moreover have "B \<Longrightarrow> ?R" by (rule disjI1)
    ultimately show "?R" by (rule disjE)
  qed
qed

(* 5.3.3 Local Lemmas *)

lemma 
  fixes a b :: int 
  assumes "b dvd (a+b)" 
  shows "b dvd a" 
proof -
  have "\<exists>k. a = b * k" if asm: "a + b = b * k" for k 
  proof
    show "a = b * (k - 1)" using asm by (simp add: algebra_simps) 
  qed
  then show ?thesis using assms by (auto simp add: dvd_def ) 
qed

(*
lemma 
  fixes a b :: int 
  assumes "b dvd (a+b)" 
  shows "b dvd a" 
proof -
  fix k
  assume asm: "a + b = b * k"
  have "\<exists>k. a = b * k" using asm
  proof -
    show "a = b * (k - 1)" by (simp add: algebra_simps) 
  qed
  then show ?thesis using assms by (auto simp add: dvd_def ) 
qed
*)

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)" (is "?L \<longrightarrow> ?R")
proof
  assume 0: ?L
  show "?R" if "?L"
  proof (rule_tac ?P=A and ?Q=B in disjE)
    show "?L" using 0 by assumption
    show 1: "A \<Longrightarrow> ?R" by (rule disjI2) 
    show 2: "B \<Longrightarrow> ?R" by (rule disjI1)
  qed
qed

lemma 
  shows "(A \<or> B) \<longrightarrow> (B \<or> A)" (is "?L \<longrightarrow> ?R")
proof
  assume 0: ?L
  show "?R" if "?L"
  proof (rule disjE)
    show "?L" using 0 by assumption
    show "A \<Longrightarrow> ?R" by (rule disjI2) 
    show "B \<Longrightarrow> ?R" by (rule disjI1)
  qed
qed

lemma "A \<longrightarrow> A"
proof
  show A if asm: A 
  proof- 
    show A using asm by assumption
  qed
qed

lemma "A \<longrightarrow> A"
proof
  assume 0: A
  from 0 show A
  proof- 
    show A using 0 by assumption
  qed
qed

lemma problem1_attempt3: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  have A: A using `A \<and> B` by (rule conjE)
  have B: B using `A \<and> B` by (rule conjE)
  from B A show "B \<and> A" by (rule conjI)
qed

lemma problem1_attempt5: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  show "B \<and> A" using `A \<and> B` 
  proof (rule conjE)
    assume B and A
    show "B \<and> A" using `B` `A` by (rule conjI)
  qed
qed

lemma problem1_attempt6: 
  shows"(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  show "B \<and> A" if asm: "A \<and> B"
  proof (rule conjE)
    from asm show "A \<and> B" by assumption
    assume B and A
    show "B \<and> A" using `B` `A` by (rule conjI)
  qed
qed

(* 5.4.1  Datatype Case Analysis *)
(* Ocaml
type foo =
  | Nothing (* Constant *)
  | Int of int (* Int constructor with value int *)
  | Pair of int * int (* Pair constructor with value as pair of ints *)
  | String of string;; (* constructor String that has the value string *)
*)

datatype 'a foo =
  Nothing (* Constant *)
  | MyInt int 'a (* Int constructor with value int *)
  | Pair 'a 'a (* Pair constructor with value as pair of ints *)
  | String string (* constructor String that has the value string *)
print_theorems

thm foo.case

value Nothing
value "MyInt 2"
value "MyInt 2 x"
value "Pair x x"
value "String 'asc'"

value "True"

datatype my_bool = true | false
value "true" (* it has value true with type my_bool *)

fun conj :: "my_bool \<Rightarrow> my_bool \<Rightarrow> my_bool" where 
"conj true true = true" |
"conj _ _ = false"
print_theorems

thm conj.simps
thm conj.simps(2)

definition con_t_t where "con_t_t \<equiv> conj true true"
print_theorems
thm con_t_t_def

lemma "conj true true = true" by simp

lemma "con_t_t = true" by (simp add: con_t_t_def)

lemma 
  shows "conj true true = true"
proof -
  show "isar_playground.conj true true = true" by simp
qed

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

(* thm tl.simps TODO: why didn't it work?! *)
lemma "length(tl xs) = length xs - 1" 
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp 
next
  fix y ys 
  assume "xs = y # ys"
  thus ?thesis by simp 
qed

lemma "length(tl xs) = length xs - 1" 
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp 
next
  fix y ys 
  assume "xs = y # ys"
  thus ?thesis by simp 
qed

lemma "length(tl xs) = length xs - 1"
  apply (cases xs)
  apply simp
  by simp

datatype nat my_nat_list = My_nat_nil | My_nat_cons nat "nat my_nat_list"
print_theorems
value my_nat_nil
value "my_nat_cons 2 my_nat_nil" (* [2] = 2::[] *)
value "my_nat_cons 3 (my_nat_cons 2 my_nat_nil)" (* [3,2] = 3 :: [2] = 3 :: 2 :: [] *)

datatype 'a my_list = MyNil | MyCons 'a "'a my_list"
print_theorems
thm my_list.case
thm my_list.induct

value "nat my_list"

value "MyNil"
value Nil

value "MyCons 2 MyNil"
value "Cons 2 Nil"
value "3 # 2 # []"
value "[3:2]"
value "x"
value "Cons x Nil"
value "Cons x2 (Cons x1 Nil)"

datatype 'a bintree = empty | BinTree "'a bintree" "'a bintree"
thm bintree.induct(*\<lbrakk>?P bintree.empty; \<And>x1 x2. \<lbrakk>?P x1; ?P x2\<rbrakk> \<Longrightarrow> ?P (BinTree x1 x2)\<rbrakk> \<Longrightarrow> ?P ?bintree *)

(* 
short hand to avoid writing
fix x1 x2 x3
assume "t = C x1 x2 x3"
for each constructor
*)

lemma "length(tl xs) = length xs - 1" 
proof (cases xs)
  case Nil
  thus ?thesis by simp 
next
  case (Cons y ys) 
  thus ?thesis by simp 
qed

lemma "length(tl xs) = length xs - 1" 
proof (cases xs)
  case Nil
  from this show ?thesis by simp 
next
  case (Cons y ys)
  from this show ?thesis by simp 
qed

(* 5.4.2 Structural Induction *)

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
  apply (induction n)
   apply simp
  by simp

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" 
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n::nat
  assume "\<Sum> {0..n} = n * (n + 1) div 2"
  thus "\<Sum> {0..Suc n} = Suc n * (Suc n + 1) div 2" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" 
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n::nat
  assume "\<Sum> {0..n} = n * (n + 1) div 2"
  thus "\<Sum> {0..Suc n} = Suc n * (Suc n + 1) div 2" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  term ?P
  show "?P 0" by simp 
next
  fix n 
  assume "?P n"
  thus "?P(Suc n)" by simp 
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
case 0
  then show "?P 0" by simp
next
  case (Suc n)
  then show "?P(Suc n)" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  case 0 (* no this cuz this introduces no assumptions just show ?P 0 *)
  show "?P 0" by simp
next
  case (Suc n)
  from this show "?P(Suc n)" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  case 0 (* no this cuz this introduces no assumptions just show ?P 0 *)
  show "?P 0" by simp
next
  show "\<And>n. ?P n \<Longrightarrow> ?P (Suc n)" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
  show "\<And>n. ?P n \<Longrightarrow> ?P (Suc n)" by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
case 0
  then show ?case by simp
  case (Suc n)
  then show ?case by simp
qed

lemma 
  fixes n::nat
  shows "\<Sum>{0..n} = n*(n+1) div 2" (is "?P n")
proof (induction n)
case 0
  then show ?case by simp
  fix n
  assume "?P n"
  then show "?P (Suc n)" by simp
qed

(* 5.4.3 Rule Induction *)

datatype nat2 = O | Suc2 nat
thm nat2.induct

datatype 'a bintree2 = 
  empty2 | 
  BinTree2 "'a bintree" "'a bintree"
thm bintree2.induct

(* it maps to bool, so what is the boolean value of ev 0? *)
inductive ev :: "nat \<Rightarrow> bool" where 
ev0: "ev 0" (* is this basically an axiom? How can I see it's truth value T(ev 0) = True  *) |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

inductive bar2 :: "'a \<Rightarrow> bool" where
bar0: "bar2 x" |
bar1: "bar2 x \<Longrightarrow> bar2 x" |
bar2: "bar2 x \<Longrightarrow> bar2 y"
thm bar2.induct
thm bar2.cases

thm nat.induct (* \<lbrakk>?P 0; \<And>nat. ?P nat \<Longrightarrow> ?P (Suc nat)\<rbrakk> \<Longrightarrow> ?P ?nat *)

lemma "\<And>x. P x \<Longrightarrow> P x"
  apply assumption
  done

definition PP where "PP x \<equiv> True"

lemma "bar2 x \<Longrightarrow> PP x" 
  apply  (induction rule: bar2.induct)
   defer
   apply assumption
  apply (simp add: PP_def)
  done

print_theorems
thm ev.cases
thm ev.ev0
thm ev.evSS
thm ev.induct (* \<lbrakk>ev ?x; ?P 0; \<And>n. \<lbrakk>ev n; ?P n\<rbrakk> \<Longrightarrow> ?P (Suc (Suc n))\<rbrakk> \<Longrightarrow> ?P ?x *)
thm bar2.induct (* \<lbrakk>bar2 ?x; \<And>x. ?P x; \<And>x y. \<lbrakk>bar2 x; ?P x\<rbrakk> \<Longrightarrow> ?P y\<rbrakk> \<Longrightarrow> ?P ?x *)

lemma "ev( Suc(Suc 0) )"
  apply (rule ev.evSS)
  apply (rule ev.ev0)
  done

lemma
  shows "ev( Suc(Suc 0))"
proof (rule evSS)
  show "ev 0" by (rule ev.ev0)
qed

(* 
note simp only re-writes from L\<rightarrow>R. In Isar we can have a single fact like ev 0 (so the
have is actually crucial for the proof to work) and then conclude something else later by simp
(it does the rewriting forward) and if it arrives at what we need to show by proof method suggested
it ends with the local lemma or shows statement.
Note simp also re-writes forward in apply script. So it gets all terms and re-writes them from L\<rightarrow>R.
In the conclusion and assumptions.
*)
lemma
  shows "ev( Suc(Suc 0))"
proof -
  have "ev 0" by (rule ev.ev0)
  from `ev 0` show "ev( Suc(Suc 0))" by (simp add: ev.evSS)
qed

lemma "ev 0 \<Longrightarrow> ev( Suc(Suc 0) )" (* this is still backward reasoning though *)
  thm ev.evSS
  apply (rule ev.evSS)
  by assumption

lemma "ev 0 \<Longrightarrow> ev( Suc( Suc( Suc(Suc 0) ) ) )" 
(* I guess this example show simp does many re-writings... *)
  by (simp only: ev.evSS) 

(* TODO only by cases
lemma "ev m \<Longrightarrow> ev (m - 2)"
  apply (rule ev.cases)
    defer
    apply blast
  apply blast
  apply (rule ev.evSS)
*)

lemma "ev m \<Longrightarrow> ev (m - 2)"
  apply (induction rule: ev.induct)
   apply (simp)
   apply (rule ev.ev0)
  apply simp
  done

fun evn :: "nat \<Rightarrow> bool" where 
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n" 
proof (induction rule: ev.induct)
  show "evn 0" by simp
  show "\<And>n. \<lbrakk>ev n; evn n\<rbrakk> \<Longrightarrow> evn (Suc (Suc n))" by simp
qed

lemma "ev n \<Longrightarrow> evn n" 
  apply (induction rule: ev.induct)
   apply simp
  by (simp only: evn.simps(3))

lemma "ev n \<Longrightarrow> evn n" 
proof (induction rule: ev.induct)
  show "evn 0" by simp
next
  fix n
  show "\<lbrakk>ev n; evn n\<rbrakk> \<Longrightarrow> evn (Suc (Suc n))" by simp
qed

lemma
  shows "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  show "evn 0" by simp
next
  fix n
  assume evSS_assump: "ev n"
  assume IH: "evn n"
  from evSS_assump IH show "evn (Suc(Suc(n)))" by simp
qed

(* 5.4.5 Rule Inversion *)

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume "ev n"
  from this show "ev (n - 2)"
  proof cases
    case ev0 then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS n') then show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed

(*
lemma
  shows "ev (n - 2)"
proof -
  show "ev (n - 2)"
  proof cases
    case ev0 then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS n') then show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed
*)

datatype mybool = T | F
thm mybool.induct

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

lemma
  shows "not (not b) = b"
proof (cases b)
  assume "b = T"
  from this show ?thesis by simp
next
  assume "b = F"
  from this show ?thesis by simp
qed

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume 0: "ev n"
  from this show "ev (n - 2)"
  proof (cases)
    assume "n = 0"
    from this show "ev (n - 2)" by (simp add: ev.ev0)
  next
    fix n'
    assume caseSS_part1: "n = Suc (Suc n')"
    assume caseSS_part2: "ev n'"
    from caseSS_part1 caseSS_part2 
    show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed


lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume 0: "ev n"
  from this show "ev (n - 2)"
  proof (cases)
    assume "n = 0"
    from this show "ev (n - 2)" by (simp add: ev.ev0)
  next
    fix n'
    assume caseSS_part1: "n = Suc (Suc n')"
    assume caseSS_part2: "ev n'"
    from caseSS_part1 caseSS_part2 
    show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed

(*
lemma
  shows "ev (n - 2)"
proof (cases n)
    case ev0 then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS n') then show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed
*)

lemma
  shows "ev (Suc (Suc 0))"
proof (rule ev.evSS)
  show "ev 0" by (rule ev.ev0)
qed

lemma
  shows "ev (Suc (Suc 0))"
proof -
  have "ev 0" by (rule ev.ev0)
  from this show "ev (Suc (Suc 0))" by (rule ev.evSS)
qed

lemma
  shows "ev (Suc (Suc 0))"
proof -
  have "ev 0" by (rule ev.ev0)
  from this show "ev (Suc (Suc 0))" by (rule ev.evSS)
qed

lemma
  shows "ev (Suc 0) \<Longrightarrow> P"
proof (cases P)
  case True
  then show ?thesis by assumption
next
  case False
  then show ?thesis sorry
qed

lemma
  shows "\<not> ev(Suc 0)"
proof (rule notI)
  assume "ev(Suc 0)" then show False by cases
qed

(* 
lemma
  shows "\<not> ev(Suc 0)"
proof (rule notI)
  assume "ev(Suc 0)" then show False
  proof (cases)
    case ev0
    show ?case
  next
    case evSS
    then show ?case sorry
  qed
qed
*)

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume 0: "ev n"
  from this show "ev (n - 2)"
  proof (cases)
    case ev0 then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS n') then show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed

lemma 
  shows "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume "ev(Suc(Suc n))"
  from this show ?thesis 
  proof (cases)
    case ev0
    then show ?case sorry
  next
    case evSS
    then show ?thesis sorry
  qed

(* 5.4.6 Advanced Rule Inversion *)

(* 
lemma 
  shows "ev (Suc m) \<Longrightarrow> \<not> (ev m)"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  case ev0
  show True
  then show ?case by simp
next
  case (evSS n)
  then show ?case sorry
qed
*)

lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not>ev m" 
  show "\<not> ev (Suc n)"
  proof (rule notI)
    assume "ev (Suc n)"
    from this show False
      proof cases 
        fix k assume "n = Suc k" "ev k"
        thus False using IH by auto 
      qed
    qed 
  qed

lemma 
  shows "ev (Suc m) \<Longrightarrow> \<not> (ev m)"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  case (evSS n)
  then show ?case using ev.simps by blast 
qed

lemma
  shows "ev n \<Longrightarrow> evn n"
proof (induction n rule: ev.induct)
  show "evn 0" by simp
next
  fix n'
  assume rule_asmp: "ev n'"
  assume IH: "evn n'"
  from rule_asmp IH show "evn (Suc (Suc n'))" by simp
qed

lemma
  shows "ev n \<Longrightarrow> evn n"
proof (induction n rule: ev.induct)
  show "evn 0" by simp
next
  show "\<And>n. \<lbrakk>ev n; evn n\<rbrakk> \<Longrightarrow> evn (Suc (Suc n))" by simp
qed

lemma 
  shows "ev (Suc m) \<Longrightarrow> \<not> (ev m)"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  (* case (evSS n) *)
  fix n
  assume "ev n"
  assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  from `ev n` IH show "\<not> ev (Suc n)" using ev.simps by blast
qed

lemma 
  shows "ev (Suc m) \<Longrightarrow> \<not> (ev m)"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  (* case (evSS n) *)
  fix n 
  show "\<lbrakk>ev n; \<And>m. n = Suc m \<Longrightarrow> \<not> ev m\<rbrakk> \<Longrightarrow> \<not> ev (Suc n)" using ev.simps by blast
qed

(* inspecting exercise 5.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
" elems [] = {}" |
" elems (a # xs) = {a} \<union> elems xs"

lemma 
  shows "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof cases
    sorry

lemma
  shows "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "?A x xs \<Longrightarrow> ?P x xs")
proof (induction xs)
  (* case Nil [] *)
  assume prems : "x \<in> elems []"
  from prems have x_in_emptyset: "x \<in> {}" by (simp only: elems.simps(1))
  from x_in_emptyset have "False" by simp
  from `False` show "\<exists>ys zs. [] = ys @ x # zs \<and> x \<notin> elems ys" by simp
next
(*  case (Cons a xs)  *)
  fix a' xs'
  assume IH: "?A x xs' \<Longrightarrow> ?P x xs'"
  assume Goal_Premise: "?A x (a' # xs')"
  from IH Goal_Premise show "?P x (a'#xs')"
    sorry

(* obtain *)

lemma
  shows "G x"
proof -
  have "\<exists> x. P x" sorry
  obtain y where fact: "P y" sorry
  oops

(* alternative 5.2 with obtains *)

lemma
  shows "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof (cases)
  assume 0: "2 dvd (length xs)" (* length xs = 2*k *)
  (* this is the crux cuz it gives us how many elements k we need from knowing length xs = 2*k *)
  obtain k where 1: "length xs = 2*k" using 0 by blast
  let ?ys="take k xs"
  let ?zs="drop k xs"
  have 2: "xs = ?ys @ ?zs" by auto
  have 3:"length ?ys = length ?zs" using 0 1 by auto
  show ?thesis using 2 3 by blast
next
  assume 0: "\<not> 2 dvd (length xs)" (* length xs = 2*k+1 *)
  obtain k where 1: "length xs = 2*k+1" using 0 using oddE by blast
  obtain ys where 2: "ys=take (k+1) xs" by blast
  obtain zs where 3: "zs=drop (k+1) xs" by blast
  have 4: "xs = ys @ zs" using 2 3 by auto
  have 5: "length ys = (length zs) + 1" using 1 2 3 by auto
  show ?thesis using 4 5 by blast
qed

(* exercise 4.5 *)

datatype alpha = a | b
type_synonym str = "alpha list"

inductive S :: "str \<Rightarrow> bool" where
Seps: "S( [] )" | (* S \<rightarrow> eps *)
Sawb: "S w \<Longrightarrow> S( (a # w) @ [b])" | (* S \<longrightarrow> aSb*)
Sss: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S( w1 @ w2 )" (* S \<longrightarrow> SS *)

inductive TT :: "str \<Rightarrow> bool" where
Teps: "TT( [] )" | (* T \<longrightarrow> eps *)
Twbwb: "TT w1 \<Longrightarrow> TT w2 \<Longrightarrow> TT( w1 @ [a] @ w2 @ [b] )" (* T \<longrightarrow> TaTb *)

lemma T2S: "TT w \<Longrightarrow> S w"
  apply (induction rule: TT.induct)
   apply (rule S.Seps)
  using Sawb Sss by auto

lemma S2T: "S w \<Longrightarrow> TT w"
  apply (induction rule: S.induct)
    apply (rule TT.Teps)
  using Teps Twbwb apply force
  using Teps Twbwb apply auto
  sorry

(* exercise 5.3 *)

lemma 
  shows "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume assumption: "ev (Suc( Suc n))"
  from assumption show "ev n"
  proof (cases rule: ev.cases)
    case ev0
    then show ?case sorry
  next
    case evSS
    then show ?thesis sorry
  qed

lemma "ev n \<Longrightarrow> ev ( Suc(Suc n))" by (rule ev.evSS)
lemma "ev ( Suc(Suc n)) \<Longrightarrow> ev n" sorry

lemma 
  shows "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume assumption: "ev (Suc( Suc n))"
  from assumption show "ev n"
  proof (rule ev.cases)
  (* proof (cases rule: ev.cases) *)
    show "Suc (Suc n) = 0 \<Longrightarrow> ev n" 
    proof -
      assume "Suc (Suc n) = 0"
      from this have "False" by simp
      from `False` show "ev n" by simp
    qed
    fix na
    show "\<lbrakk>Suc (Suc n) = Suc (Suc na); ev na\<rbrakk> \<Longrightarrow> ev n" 
    proof -
      assume "Suc (Suc n) = Suc (Suc na)"
      from this have "na = n" by simp
      from `na = n` show "ev na \<Longrightarrow> ev n" by simp
    qed
  qed
qed

lemma 
  shows "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume assumption: "ev (Suc( Suc n))"
  from assumption show "ev n"
  proof (rule ev.cases) (* 1 *)
    show "Suc (Suc n) = 0 \<Longrightarrow> ev n" 
    proof -
      assume "Suc (Suc n) = 0" (* 2 *)
      from this have "False" by simp (* 3 *)
      from `False` show "ev n" by simp (* 4 *)
    qed
    fix na (* 5 *)
    assume evSS_assumption: "Suc (Suc n) = Suc (Suc na)" "ev na" (* 5 *)
    show "ev n" using evSS_assumption 
    proof -
      assume "Suc (Suc n) = Suc (Suc na)"
      from this have "na = n" by simp
      from `na = n` show "ev na \<Longrightarrow> ev n" by simp
    qed
  qed
qed

lemma 
  shows "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume assumption: "ev (Suc( Suc n))"
  from assumption show "ev n"
  proof (rule ev.cases) (* 1 *)
    show "Suc (Suc n) = 0 \<Longrightarrow> ev n" 
    proof -
      assume "Suc (Suc n) = 0" (* 2 *)
      from this have "False" by simp (* 3 *)
      from `False` show "ev n" by simp (* 4 *)
    qed
    fix na (* 5 *)
    assume evSS_assumption: "Suc (Suc n) = Suc (Suc na)" "ev na" (* 5 *)
    have "na = n" using evSS_assumption by simp
    show "ev na \<Longrightarrow> ev n" using `na = n` by simp
  qed
qed

lemma
  shows "\<not> ev (Suc (Suc (Suc 0)))"
proof (rule notI)
  assume "ev (Suc (Suc (Suc 0)))"
  from this show "False"
  proof cases
(*  note first case is empty and I don't know how to explicitly close the proof *)
    case evSS
    thm ev.cases (* \<lbrakk>ev ?a; ?a = 0 \<Longrightarrow> ?P; \<And>n. \<lbrakk>?a = Suc (Suc n); ev n\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P *)
    then show ?thesis using ev.cases by auto
  qed
qed

(* *)

lemma
  shows "A"
proof -
  show "A" by sorry
qed

lemma
  assumes as: "A"
  shows "A"
  by (simp add: assms)

lemma
  assumes as: "A"
  shows "A"
proof -
  show "A" using as by simp
qed

lemma
  shows "A\<Longrightarrow>A"
proof -
  assume 0: "A"
  show "A" using 0 by simp
qed

end