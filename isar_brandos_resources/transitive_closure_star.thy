theory transitive_closure_star
imports Main
begin
(* 
Relation = if x \in X, y \in Y when we have R x y \<longleftrightarrow> (x,y) \<in> X \<times> Y.
Reflexive = self loops  in the graph. e.g. \<forall>x \<in> X, (x,x) \in X \<times> X
Transitive = if there is a path from x to y and from y to z then there is one from
x to z. if R x y, R y z \<Longrightarrow> R x z.
Reflexive closure = smallest relation that is reflexive and contains R. 
  r(R) := R \<union> Diagonal.
Transitive closure t(r) := R \<and> Transitive \<and> Smallest

Transitive closure := 
tr(r) := R \<and> Reflexive \<and> Transitive \<and> Smallest

transitive closure
transitive closure relation means it must be reflexive and transitive. 
So if we have R then tr(R) = R* is a new relation that is reflexive and transitive.
Note the * operator maps relations to it’s transitive closure 
i.e. *(R) = R* for short hand.

*)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where 
refl: "star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
 
(* By definition star r is reflexive. *)

lemma star_reflexive: "star r x x" by (rule refl)

(* It is also transitive, but we need rule induction to prove that: *)

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply assumption
  by (simp add: star.step)

lemma 
  shows "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof (induction rule: star.induct)
case (refl x)
  then show ?case by assumption
next
  case (step x y z)
  then show ?case by (simp add: star.step)
qed

end