theory cases_playground
imports Main
begin

(* example simple custom bools *)

datatype mybool = T | F
print_theorems
thm mybool.induct

fun not :: "mybool \<Rightarrow> mybool" where
  "not T = F" |
  "not F = T"

lemma "not (not b) = b" apply (cases b) apply simp by simp

lemma
  shows "not (not b) = b"
proof (cases b)
case T
  then show ?thesis by simp
next
  case F
  then show ?thesis by simp
qed

(* example Inductively defined predicates *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where 
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma
  shows "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0
  then show ?case by simp
next
  case (evSS n)
  then show ?case by simp
qed

(* failed to do it directly to it
lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof (cases n)
    case ev0 then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS n') then show "ev (n - 2)" by (simp add: ev.evSS)
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
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume 0: "ev n"
  from this show "ev (n - 2)"
  proof (cases)
    assume "n = 0" 
    then show "ev (n - 2)" by (simp add: ev.ev0)
  next
    fix n'
    assume "n = Suc (Suc n')" "ev n'"
    then show "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume "ev n"
  from this show "ev (n - 2)"
  proof (cases)
    case ev0
    then show ?thesis using `ev n` by auto 
  next
    case (evSS n)
    then show ?thesis by simp 
  qed
qed

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume "ev n"
  from this show "ev (n - 2)"
  proof (cases rule: ev.cases)
    case ev0
    then show ?thesis by (simp add: ev.ev0)
  next
    case (evSS n)
    then show ?thesis by simp
  qed
qed

(* failed to unify manually for the argument ev ?a *)
lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof (cases rule: ev.cases)
  show ?thesis by sorry
  show ?thesis by sorry
  show ?thesis by sorry
qed

lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof (rule ev.cases)
  show ?thesis by sorry
  show ?thesis by sorry
  show ?thesis by sorry
qed

(* but the manual unifications succeds here though *)
lemma "ev n \<Longrightarrow> ev (n - 2)"
  thm ev.cases
  apply (cases rule: ev.cases)
    apply simp
   apply simp
  by simp

thm ev.induct ev.cases
(*
Note that induction and cases is very similar except that induction introduces
the induction hypothesis after doing the unification, the ?Pn in this example.
  ev ?x \<Longrightarrow> ?P 0 \<Longrightarrow> (\<And>n. ev n \<Longrightarrow> ?P n \<Longrightarrow> ?P (Suc (Suc n))) \<Longrightarrow> ?P ?x
  ev ?a \<Longrightarrow> (?a = 0 \<Longrightarrow> ?P) \<Longrightarrow> (\<And>n. ?a = Suc (Suc n) \<Longrightarrow> ev n \<Longrightarrow> ?P) \<Longrightarrow> ?P
*)

(* this does the unification for me *)
lemma
  shows "ev n \<Longrightarrow> ev (n - 2)"
proof (cases)
  show ?thesis by sorry
  show ?thesis by sorry
qed

(* Construct clashes *)

lemma
  shows "\<not> ev (Suc 0)"
proof (rule notI)
  assume "ev (Suc 0)"
  then show False 
  proof
    show "Suc 0 = 0 \<Longrightarrow> False" by simp
    show "\<And>n. \<lbrakk>Suc 0 = Suc (Suc n); ev n\<rbrakk> \<Longrightarrow> False" by simp
  qed
qed

lemma
  shows "ev (Suc 0) \<Longrightarrow> P"
proof (cases P)
  case True
  then show ?thesis by assumption
next
  case False
  then show ?thesis
  qed

lemma
  shows "\<not> ev (Suc 0)"
proof (rule notI)
  assume "ev (Suc 0)"
  then show False 
  proof (cases)
  case ev0
    then show ?case by blast
  next
    case evSS
    then show ?case sorry
qed

end