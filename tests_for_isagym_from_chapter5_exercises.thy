theory tests_for_isagym_from_chapter5_exercises
imports Main
begin

(*
Exercise 5.1. Give a readable, structured proof of the following lemma:
*)

thm allE (* \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
thm exE (* \<lbrakk>\<exists>x. ?P x; \<And>x. ?P x \<Longrightarrow> ?Q\<rbrakk> \<Longrightarrow> ?Q *)
lemma exercise5p1_apply:
"\<lbrakk> \<forall>x y. T x y \<or> T y x;(\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y);(\<forall>x y. T x y \<longrightarrow> A x y); A x y\<rbrakk> \<Longrightarrow> T x y"
  by metis

thm HOL.mp (* \<lbrakk>?P \<longrightarrow> ?Q; ?P\<rbrakk> \<Longrightarrow> ?Q *)
thm conjE (* \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R *)
lemma exercise5p1:
  assumes T: "\<forall>x y. T x y \<or> T y x" 
    and   A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y" 
    and   TA: "\<forall>x y. T x y \<longrightarrow> A x y" 
    and   "A x y" 
  shows "T x y"
proof - 
  have T2: "T x y \<or> T y x" using T by simp
  show "T x y" using T2 proof (rule disjE) (* 1) *)
    (* Part 0*)
    show "T x y \<Longrightarrow> T x y" by assumption (* 2) *)
    show "T y x \<Longrightarrow> T x y" proof -
      (* Part 1: *)
      have TA3: "T y x \<longrightarrow> A y x" using TA by (simp add: TA) (* 3) *)
      assume "T y x" (* 1) *)
      have "A y x" using TA3 `T y x` by (rule HOL.mp) (* 4) *)
      (* Part 2: *)
      have A2: "A x y \<and> A y x \<longrightarrow> x = y" using A by simp (* 5 *)
      have "x=y" using `A y x` `A x y` A2 by simp (* 6 *)
      show "T x y" using `x=y` `T y x` by simp (* 7 *)
    qed
  qed
qed

(*
this second version fixes the issue with the previous version
of the proof to strcture it in a more Isar style according to 
section 5.2 of the Proof Pattern chapter
*)
lemma exercise5version2:
  assumes T: "\<forall>x y. T x y \<or> T y x" 
    and   A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y" 
    and   TA: "\<forall>x y. T x y \<longrightarrow> A x y" 
    and   "A x y" 
  shows "T x y"
proof - 
  have T2: "T x y \<or> T y x" using T by simp
  show "T x y" using T2 proof (rule disjE) (* 1) *)
    (* Part 0*)
    assume "T x y"
    show "T x y" using `T x y` by assumption (* 2) *)
  next
    assume "T y x"
    show "T x y" proof -
      (* Part 1: *)
      have TA3: "T y x \<longrightarrow> A y x" using TA by (simp add: TA) (* 3) *)
      have "A y x" using TA3 `T y x` by (rule HOL.mp) (* 4) *)
      (* Part 2: *)
      have A2: "A x y \<and> A y x \<longrightarrow> x = y" using A by simp (* 5 *)
      have "x=y" using `A y x` `A x y` A2 by simp (* 6 *)
      show "T x y" using `x=y` `T y x` by simp (* 7 *)
    qed
  qed
qed

(*
We want to show T x y.
To show that we do:
1) disjE and try to prove T x y from both T x y and T y x.
Part 0: the trivial case from disjE
2) From T x y goal (T x y) is trivial (just by assumption)
Part 1: Now we want the goal T x y from (assm) T y x. The idea is to show x=y to have T y x = T x y.
To do that we need A y x and A x y. So first we get A y x:
3) Establish T y x \<rightarrow> A y x from initial thm assumption TA
4) Use disjE assumption T y x and TA3 (T y x \<longrightarrow> A y x) to get A y x.
Part 2: Now the second part to conclude the proof:
5) Establish we can indeed do A x y \<and> A y x \<longrightarrow> x = y from initial thm assumption.
6) Establish x=y from A y x (from 4) and A x y (from initial thm assumption)
7) Complete proof using all the facts we need x=y & T y x \<rightarrow> T x y.
Done

*)

(* Note to self. The insight was that you needed to use T x y \<or> T y x. Using that you get by disjE
that you need to proof some goal using them seperately. The insight was that if you noticed that
A y x would give you x = y which would ultimately give you T x y. But A y x was NOT true by iself,
so when you tried proving it by itself you failed (of course). BUT disjE allowed you to get T y x
by itself which would give you the goal you needed, A y x which gave x = y which have T x y using
T y x. So apply disjE early on. Then the first assumption it introduces IS the goal so it ends 
immediately. Then you do need to use more logic to get to A y x but you ONLY have to show A y x
using T y x, instead of needing to show A y x using T x y also (which probably can't be done).
The reason that problem would occur is if you try to have A y x as a stand alone theorem, which is
not true. It's only true using ONLY T y x. 
*)

(* 
Exercise 5.2. Give a readable, structured proof of the following lemma

Hint: There are predefined functions take :: nat \<Rightarrow> ′a list \<Rightarrow> ′a list and 
drop :: nat \<Rightarrow> ′a list \<Rightarrow> ′a list such that 
take k [x1,...] = [x1,...,xk] and drop k [x1,...] = [xk+1,...]. 
Let sledgehammer find and apply the relevant 
take and drop lemmas for you.
*)

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
  apply (cases)
  sorry

lemma
  shows "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof (cases)
  assume 0: "2 dvd (length xs)" (* length xs = 2*k *) (* 1 *)
  (* this is the crux cuz it gives us how many elements k we need from knowing length xs = 2*k *)
  obtain k where 1: "length xs = 2*k" using 0 by blast (* 2 *)
  let ?ys="take k xs" (* 3 *)
  let ?zs="drop k xs" (* 3 *)
  have 2: "xs = ?ys @ ?zs" by auto (* 4 *)
  have 3:"length ?ys = length ?zs" using 0 1 by auto (* 5 *)
  show ?thesis using 2 3 by blast (* 6 *)
next
  assume 0: "\<not> 2 dvd (length xs)" (* length xs = 2*k+1 *) (* 1 *)
  obtain k where 1: "length xs = 2*k+1" using 0 using oddE by blast (* 2 *)
  let ?ys="take (k+1) xs" (* 3 *)
  let ?zs="drop (k+1) xs" (* 3 *) 
  have 2: "xs = ?ys @ ?zs" by simp (* 4 *)
  have 5: "length ?ys = (length ?zs) + 1" using 1 by auto (* 5 *)
  show ?thesis using 2 5 by blast (* 6 *)
qed

(*
thm: Show that given a list xs you can always find two lists to split xs s.t. they combine to get
the original list and the split can be done evenly or just 1 off.
There are two cases:
Part 1: xs is even length so the split is perfectly even
Part 2: xs is not even so the split is 1 off from even.
The technique to show them is the same (except with the negation of the other, i.e. even or odd):
1) Do assumtion, xs is even or not (wlog xs is even)
2) get the length k of the list you need via isabelle
3) define the appropriate splits from take and drop
4) use the splits to show they combine to give xs
5) use the splits to get the length and show k'=k (even case) or k'=k+1 (odd case)
6) using 4 and 5 proof is concluded for both cases

*)

(* Exercise 5.3 
Give a structured proof by rule inversion:
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"

rule inversion: case analysis to which rules could have been used to arrive at certain facts.
e.g. 
ev n \<Longrightarrow> n=0 \<or> (\<exists>k. n = Suc(Suc(k)) \<and> ev k )
i.e. if we have the fact ev n, we could have arrived using either rule for it. 
*)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc( Suc(n)))"
thm ev.cases (* ev ?a \<Longrightarrow> (?a = 0 \<Longrightarrow> ?P) \<Longrightarrow> (\<And>n. ?a = Suc (Suc n) \<Longrightarrow> ev n \<Longrightarrow> ?P) \<Longrightarrow> ?P *)

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
    have "na = n" using evSS_assumption by simp (* 6 *)
    show "ev na \<Longrightarrow> ev n" using `na = n` by simp (* 7 *)
  qed
qed

(*
The proof is by rue inversion (i.e. what rule/cases could we have applied to arrive at
ev(n+2)? Then show from those cases that arrived at ev(n+2) show ev n.
1) First step is rule inversion step (rule ev.cases) which introduces that n+2=0 arrives at the goal
ev n (via rule/case ev0) or via 2nd case/rule evSS, which introduces \<And>na. n+2 = na+2; ev na
Part1: ev0 case
2) Assume the rule inversion assumtion n+2=0 via rule ev0
3) Make explicit that this assumption is equal to False in natural numbers.
4) Conclude goal ev n from False.
Part2: evSS
5) Assume the evSS assumptions \<And>na. n+2 = na+2; ev na.
6) Simplify n+2 = n+2 to conclude na = n.
7) Using the assumption ev na from rule inversion and na=na, conclude goal ev n
*)

(* 
Exercise 5.4. 
Give a structured proof of 
\<not> ev (Suc (Suc (Suc 0))) by rule inversions. 
If there  are no cases to be proved you can close
a proof immediately with qed.
*)

thm ev.cases (* \<lbrakk>ev ?a; ?a = 0 \<Longrightarrow> ?P; \<And>n. \<lbrakk>?a = Suc (Suc n); ev n\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P *)

lemma
  shows "\<not> ev (Suc (Suc (Suc 0)))"
proof (rule notI) (* 1 *)
  assume "ev (Suc (Suc (Suc 0)))" (* 3 *)
  from this show "False"
  proof cases (* 3 *)
    (*  note first case is empty *) (* 4 *)
    case evSS (* 5 *)
    then show ?thesis using ev.cases by auto
  qed
qed

(*
Prove that we cannot get 3 being an even number.
1) Rule not Introduction i.e. change goal to ev 3 \<Longrightarrow> False
2) By contradiction, assume we did have the inductiv predicate ev 3
3) Rule inversion, what cases (ev0,evSS) could have arrived at assumption and then at the goal (False)?
4) First case is empty since it's impossible and Isabelle closes that proof obligation
5) We could have arrived using evSS rule which for this case simplifies as follow:
\<And>na. (0+1)+2=na+2; ev na thus na = 0+1 which leads to use ev (0+1) to prove False.
6) Now since no rules could have been used to arrive at goal (False) we invoke the rules
and auto to conclude it's impossible to have ev (1+0), which concludes proof.

*)

(* Exercise 5.5 *)
(* Notes:
iter r n x y = n-fold iteration of a relation r should hold if there are x0, ..., xn 
such that x = x0, xn = y and r xi xi+1 for all i < n.

iter0: iter must be reflexive. i.e. there is a path of length 0 from x to y 
and y is simply itself x.
iterSS: is inductively defined. If we already know there is a path of length n from y to z and we
simply include the extra step x\<rightarrow>y using r, then of course there is a path from x to z using r.
Simply use the old path from the inductively defined  iter r n y z the "old path" and then add the
new path x\<rightarrow>y using r. Thus there is a path of length n+1 (i.e. we can conclude the left most 
predicate in the meta-implication chain.
*)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
iterSS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"
(* 
iterSS says there is a path with r of length n+1 inductively, if there is
a path of length n with r and we have an addition step with r.
path(r,x\<rightarrow>y) & path(r,y \<rightarrow>z,length=n) \<Rightarrow> path(r,x\<rightarrow>y,length=n+1)

*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where 
refl: "star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
thm star.cases
thm star.induct

lemma "iter r n x y \<Longrightarrow> star r x y"
  apply (induction rule: iter.induct)
   apply (rule star.refl)
  by (simp add: star.step)

lemma (* Correct proof but prefer the other one I wrote *)
  shows "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (iter0 x)
  then show ?case by (rule star.refl)
next
  case (iterSS x y n z)
  then show ?case by (meson star.step) 
qed

lemma
  shows "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct) (* 1 *)
  (*   case (iter0 x) *)
  fix x' (* 2 *)
  show "star r x' x'" by (rule star.refl)
next
  (* case (iterSS x y n z) *)
  fix x' y' z' n' (* 4 *)
  assume iterSS_rxy_asm: "r x' y'" (* 5 *)
  assume iterSS_iter_asm: " iter r n' y' z'" (* 5 *) (* NOT needed, it's helpful as it introduces IH *)
  assume IH: "star r y' z'" (* 6 *) (* IH from iter r n y z *)
  show "star r x' z'" using `r x' y'` `star r y' z'` by (rule star.step)
qed

(*
Thm: We want to show that if the n-fold iteration from x to y using relation r holds then
the transitive closure for r from x to y also holds.

1) The proof is by induction. We could have arrived at iter r n x y 
with either iter0 or iterSS. So break the assumption into those two cases and include the
induction hypothesis if any of them introduces it.
Part 1: iter0 base case
2) The first step Unified iter r n x y in the thm statement with the iter0 rule.
This identifies that the mapping of the variables in the thm should be the follow:
sigma = {x\<rightarrow>x'} and that's it, where x' is quantified for any x' (since the rule iter0
holds for any x x).
3) We get the 1st goal \<And>x. star r x x which is exactly the same as the rule reflexive for r*
and that closes the proof.
Part 2: iterSS: indutive step step
The idea for this proof is that we use r x' y' and the IH r* y' z' to conclude r* x' z'.
i.e. r x' y' + r* y' z' \<Longrightarrow> r* x' z' using the star step rule (which mathches that).
Note that the unification has the map sigma={x\<rightarrow>x',y\<rightarrow>y',z\<rightarrow>z',n\<rightarrow>n'} (usually the mapping 
is a little more interesting if there are constructors e.g. mapping of variable goals
to variable from rule like this sigma={x\<rightarrow>C x1' x2' ... xn'} etc.
Note: goal is \<And>x y n z. r x y \<Longrightarrow> iter r n y z \<Longrightarrow> star r y z \<Longrightarrow> star r x z
since we removed iter n x z with the rule that could have arrived at it & IH r* y z.
4) Introduce the variables from the quanitifcation from the induction rule on iterSS
5) Introduce the assumptions from iterSS rule: r x y \<Longrightarrow> iter r n y z
6) Introduce the IH r* y z (introduced by iter r n y z).
7) use r x' y' (iterSS assumption) and r* y' z' (IH) to conclude goal r* y z using
r* step rule (which is exactly that r x y \<Rightarrow> r* y z \<Rightarrow> r* x z.
*)

(* 
Exercise 5.6. Define a recursive function 
elems :: ′a list \<Rightarrow> ′a set (gets the set of elements of the list) and 
prove: x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys.
*)

fun elems :: "'a list \<Rightarrow> 'a set" where
" elems [] = {}" |
" elems (a # xs) = {a} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
  apply (induction xs)
   apply simp
  apply auto
   apply fastforce
  by (metis Un_iff append.simps(2) append_Nil elems.simps(1) elems.simps(2) empty_iff insert_iff)

thm list.induct (* \<lbrakk>?P []; \<And>x1 x2. ?P x2 \<Longrightarrow> ?P (x1 # x2)\<rbrakk> \<Longrightarrow> ?P ?list *)

lemma
  shows "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x#zs \<and> x \<notin> elems ys" (is "?A x xs \<Longrightarrow> ?P x xs")
proof (induction xs) (* 1 *)
  (* case Nil [] *)
  assume prems : "x \<in> elems []" (* 1 *)
  from prems have x_in_emptyset: "x \<in> {}" by (simp only: elems.simps(1)) (* 2 *)
  from x_in_emptyset have "False" by simp (* 2 *)
  from `False` show "\<exists>ys zs. [] = ys @ x # zs \<and> x \<notin> elems ys" by simp (* 3 *)
next
(*  case (Cons x' xs)  *)
  fix x' xs'
  assume IH: "x \<in> elems xs' \<Longrightarrow> \<exists>ys zs. xs' = ys @ x#zs \<and> x \<notin> elems ys" (* 4 *)
  assume Goal_Premise: "x \<in> elems (x'#xs')" (* 5 *)
  show "\<exists>ys zs. (x'#xs') = ys @ x#zs \<and> x \<notin> elems ys" using IH Goal_Premise (* 5 *)
  proof cases
    (*  this case yields: xs\<rightarrow>x'#xs'
        then ultimately we want: (x'#xs') = ys @ x#zs \<and> x \<notin> elems ys
   *)
    assume "x' = x" (* 5 *)
    (* since our goal ?P has existentials, we introduce them by exhibiting witness that work*)
    obtain ys where ys: "(ys :: 'a list) = []" by simp (* 7 *)
    obtain zs where zs: "zs = xs'" by simp (* 7 *)
    have first: "x'#xs'= ys @ x'#zs" using ys zs by simp (* 8 *)
    have second: "x' \<notin> elems ys" using ys by simp  (* 9 *)
    have thesis: "?P x (x'#xs')" using `x'=x` ys zs first second by blast (* 10 *)
    show "\<exists>ys zs. x'#xs' = ys@(x#zs) \<and> x \<notin> elems ys" using thesis by simp (* 10 *)
  next
    assume "x' \<noteq> x" (* 6 *)
    (* get ys' zs' that we need from the induction hypothesis *)
    have 0: "x \<in> elems xs'" using Goal_Premise `x' \<noteq> x` by simp (* 12 *)
    have 1: "\<exists> ys' zs'. xs'=ys'@(x#zs') \<and> x \<notin> elems ys'" using 0 IH by simp (* 12 *)
    obtain ys' zs' where 2: "xs'=ys'@(x#zs') \<and> x \<notin> elems ys'" using 1 by auto (* 12 *)
    have 3: "x \<notin> elems ys'" using 2 by simp
    (* obtain ys zs where x'#xs'=ys@x#zs where xs'=ys'@x#zs'*)
    let ?ys="x'#ys'" (* 11 *)
    let ?zs="zs'" (* 11 *)
    have 4: "x \<notin> elems ?ys" using  `x'\<noteq>x` 3 by simp (* 13 *)
    have 5: "x'#xs' = ?ys @(x#?zs)" using  `x'\<noteq>x` 2 by simp (* 14 *)
    show "\<exists>ys zs. x'#xs' = ys @(x#zs) \<and> x \<notin> elems ys" using 4 5 by blast
  qed
qed

(* 
Recall:
elems xs = the set of elements of the list 
WTS: x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys.
i.e. we want to show that if x is in the set of elements of list xs, then we can always split
the list into two parts ys zs s.t. we recover the original list via xs = ys @(x#zs) and
x is not in the first half of the list ys.
Proof:
1) Induction on the list xs. We get two cases [] and x#xs.
Part 1: [] Nil base case
2) In the Nil case we have [] \<equiv> {} so have x \<in> {}.
3) In that x \<in> {} is false whuch we can conclude anything (in particular the goal).
Part 2: Cons case x'#xs'
Introduce the assumptions:
4) Since we are doing induction, we can introduce the implication we are
trying to prove but for xs' from the cons case:
IH: P xs' \<equiv> x \<in> elems xs' \<Longrightarrow> \<exists>ys zs. xs' = ys @ x#zs \<and> x \<notin> elems ys
5) Notice how the goal we are trying to show has xs\<rightarrow>xs'#x from unification
of the goal term xs to the cons case xs'#x'.
So we are proving:
\<And>x' xs'. (x \<in> elems xs' \<Longrightarrow> \<exists>ys zs. xs' = ys @ x#zs \<and> x \<notin> elems ys) \<Longrightarrow> x \<in> elems (x'#xs') \<Longrightarrow> \<exists>ys zs. x'#xs' = ys @ x # zs \<and> x \<notin> elems ys
First term in brackets is the IH (which is an implication for xs') and the last is the new goal and it's assumption (using mapping xs\<rightarrow>xs'#x').

Notice what the ultimate goal is: x \<in> elems (x'#xs') \<Longrightarrow> \<exists>ys zs. x'#xs' = ys @ x # zs \<and> x \<notin> elems ys
The main idea is that the first split ys must NOT have the element. Thus there must be two cases:
5) when x is indeed the head and when it's 6) not the head.
Cases: 

-1st: 7) When x is in the head (x=x') then we set the witnesses ys\<rightarrow>[] and zs\<rightarrow>xs, 8) and check
that when combined they return the original list xs. i.e. []@x'#xs is x#xs.
9) note that we have x \<notin> ys since x \<notin> [] is true.
10) With 9 and 8 we have that x is not in the ys list and the split returns the original list as required

-2nd: 11) When x is not in the head (x\<noteq>x') we set the first half of the target list ys
to be x'#ys' i.e. ys\<rightarrow>x'#ys' and the second half zs to be zs\<rightarrow>zs'.
12) But we obtained ys' and zs' from the induction hypothesis. Thus, ys' will
have the property we need x \<notin> ys' and zs' completes the list xs'
13) The witness ys is the important one because we want it such that x is NOT in it.
That is satisfied from construction of them by 12, since by induction ys' will have the property 
we want (that x is not in ys') and also x\<noteq>x'.
14) We show that the construction for ?ys and ?zs indeed complete the original list since
x'#ys'@(x#zs') \<rightarrow> x'@xs' via 2 as required.
15) now that we have the two statements we need (that the original list is completed by 5 and
that x is not in the first half of the list ?ys 4) we concliude the proof.

(note ys\<equiv>?ys, zs\<equiv>?zs) 
*)

(* Substitute for Ex 5.7 *)

(*
lemma
  shows "x \<in> \<real> \<and> x*x =2"
*)

end