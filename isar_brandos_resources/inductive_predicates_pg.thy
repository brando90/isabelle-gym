theory inductive_predicates_pg
imports Main
begin

datatype tau = 
C0 |
C1 tau |
C2 tau tau |
C3 tau tau tau
thm tau.induct

value "C0"
value "C1 C0"
value "C2 (C0) (C1 C0)"

inductive ev :: "nat \<Rightarrow> bool" where 
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"
thm ev.cases ev.induct

inductive IP :: "tau \<Rightarrow> bool"  where
rule0: "IP C0" |
rule1: "IP x" |
rule2: "Q (x::tau) \<Longrightarrow> IP x" |
rule3: "Q (x::tau) \<Longrightarrow> IP x'" 
thm IP.cases IP.induct

(* *)

inductive bar2 :: "'a \<Rightarrow> bool" where
bar0: "bar2 x" |
bar1: "bar2 x \<Longrightarrow> bar2 x" |
bar2: "bar2 x \<Longrightarrow> bar2 y"

(* *)

inductive I :: "tau \<Rightarrow> bool"  where
rule0: "I C0" |
rule1: "I x" |
rule2: "Q x \<Longrightarrow> I (x::tau)" |
rule3: "Q (x::tau) \<Longrightarrow> I x'" |
rule4: "Q x \<Longrightarrow> I (C1 x)" |
rule5: "Q (C1 x) \<Longrightarrow> I x" |
rule6: "Q (C1 x) \<Longrightarrow> I x'" |
rule7: "Q (x::tau) \<Longrightarrow> I (C2 x' x'')" |
rule8: "I (C2 x' x'')" |
rule9: "Q (x::tau) \<Longrightarrow> I C0 \<Longrightarrow> I (C3 x x' x'') \<Longrightarrow> I (C2 x x')" |
rule10: "Q (x::tau) \<Longrightarrow> I C0 \<Longrightarrow> I x \<Longrightarrow> I (C3 x x' x'') \<Longrightarrow> I (C2 x x')"
thm I.cases I.induct
thm nat.induct
thm I.induct
(*
I ?x \<Longrightarrow>
?P C0 \<Longrightarrow>
(\<And>x. ?P x) \<Longrightarrow>
(\<And>Q x. Q x \<Longrightarrow> ?P x) \<Longrightarrow>
(\<And>Q x x'. Q x \<Longrightarrow> ?P x') \<Longrightarrow>
(\<And>Q x. Q x \<Longrightarrow> ?P (C1 x)) \<Longrightarrow>
(\<And>Q x. Q (C1 x) \<Longrightarrow> ?P x) \<Longrightarrow>
(\<And>Q x x'. Q (C1 x) \<Longrightarrow> ?P x') \<Longrightarrow>
(\<And>Q x x' x''. Q x \<Longrightarrow> ?P (C2 x' x'')) \<Longrightarrow>
(\<And>x' x''. ?P (C2 x' x'')) \<Longrightarrow>
(\<And>Q x x' x''. Q x \<Longrightarrow> I C0 \<Longrightarrow> ?P C0 \<Longrightarrow> I (C3 x x' x'') \<Longrightarrow> ?P (C3 x x' x'') \<Longrightarrow> ?P (C2 x x')) \<Longrightarrow>
(\<And>Q x x' x''. Q x \<Longrightarrow> I C0 \<Longrightarrow> ?P C0 \<Longrightarrow> I x \<Longrightarrow> ?P x \<Longrightarrow> I (C3 x x' x'') \<Longrightarrow> ?P (C3 x x' x'') \<Longrightarrow> ?P (C2 x x')) \<Longrightarrow> ?P ?x
*)

theorem "I x \<Longrightarrow> P x"
  apply (induction rule: I.induct)
  sorry

theorem "I x \<Longrightarrow> P x"
  apply (rule I.induct)
  sorry

theorem "I x \<Longrightarrow> P x"
  apply (cases rule: I.cases)
  apply simp (* explicitly unifies! *)
  sorry

(* 
Exercise 4.4. Analogous to star, give an inductive definition of the n-fold iteration of a relation r:
iter r n x y should hold if there are x0, ..., xn s.t. x = x0, xn = y and r xi xi+1 for all i < n
Correct and prove the following claim: star r x y =\<Rightarrow> iter r n x y.

iter r n x y \<equiv> \<exists> x1 ... xn . x=x0 \<and> y=xn \<and> \<forall> i < n. r xi x(i+1)
*)

(* 
iter r n x y = there should be a path from x to y using r to get from x to y.
iter0: iter must be reflexive. i.e. there is a path of length 0 from x to y and y is simply itself x.
iterSS: is inductively defined. If we already know there is a path of length n from y to z and we
simply include the extra step x\<rightarrow>y using r, then of course there is a path from x to z using r.
Simply use the old path from the inductively defined  iter r n y z the "old path" and then add the
new path x\<rightarrow>y using r. Thus there is a path of length n+1 (i.e. we can conclude the left most 
predicate in the meta-implication chain.
*)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
iterSS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where 
refl: "star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
thm star.induct

lemma "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule: star.induct)
(* apply (rule_tac ?n2="0" in exI) *)
(* apply (rule_tac r="\<lambda>x. 0" in exI) *)
   apply (meson iter0)
(* 
proof: 
1) r x y & r* y z let's us conclude r* x z via start.step
2) Then using the assumptions r* x z and for any n. iter r n y z 
we can use iter.iterSS to get iter r (Suc n) x z for any n (from previous selection).
Which gives us iter r ?n x z for the n above as required (need to show existential so there is the
witness).
*)
  by (meson iterSS)

lemma "iter r n x y \<Longrightarrow> star r x y"
  apply (induction rule: iter.induct)
   apply (rule star.refl)
  by (simp add: star.step)

lemma
  shows "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (iter0 x)
  then show ?case by (rule star.refl)
next
  case (iterSS x y n z)
  then show ?case by (meson star.step) 
qed

end