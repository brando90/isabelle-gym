(* File: boolexp.thy *)

theory boolexp
imports Main
begin

section{* Basic Type and Evaluation Function
         for Boolean Expressions *}

text{*
 The following type mirrors the BNF grammar
we gave in for boolean expressions.  We will use
only prefixed connectives here
*}

datatype 'a boolexp =
   TRUE | FALSE |Var 'a | Not "'a boolexp"
  | And "'a boolexp" "'a boolexp"
  | Or "'a boolexp" "'a boolexp"
  | Implies "'a boolexp" "'a boolexp"

text{*
The following is a recursive definition of the function for evaluating
boolean expressions. It is the same as the definition
of \textit{models} given in class. 
*}

fun boolexp_eval 
where
   "boolexp_eval env TRUE = True"
 | "boolexp_eval env FALSE = False"
 | "boolexp_eval env (Var x) = env x"
 | "boolexp_eval env (Not b) = (\<not> (boolexp_eval env b))"
 | "boolexp_eval env (And a b) =
    ((boolexp_eval env a) \<and> (boolexp_eval env b))"
 | "boolexp_eval env (Or a b) =
    ((boolexp_eval env a) \<or> (boolexp_eval env b))"
 | "boolexp_eval env (Implies a b) =
    ((\<not> (boolexp_eval env a))\<or> (boolexp_eval env b))"

text{*
Because all our definition have been purely
computational, we may use \tettt{value} to evaluate
expressions using the type \texttt{boolexp} and the term
boolexp_eval.
*}

(*
value "boolexp_eval
(\<lambda> x. case x of ''a'' \<Rightarrow> True | _ \<Rightarrow> False)
 (Implies (Var ''b'') (Var ''a''))"
*)


value "boolexp_eval
(\<lambda> x. case x of (0::nat) \<Rightarrow> True | _ \<Rightarrow> False)
 (Implies (Var (1::nat)) (Var (0::nat)))"


text{*
Our objective is to build a function that will tell
us all the ways a boolean expression can be satisfied.
Our approach is to put the boolean expression in
disjunctive normal form.
We start by eliminating implies.
*}

fun remove_implies where
   "remove_implies TRUE = TRUE"
 | "remove_implies FALSE = FALSE"
 | "remove_implies (Var x) = Var x"
 | "remove_implies (Not a) = Not (remove_implies a)"
 | "remove_implies (And a b) =
    And (remove_implies a) (remove_implies b)"
 | "remove_implies (Or a b) =
    Or (remove_implies a) (remove_implies b)"
 | "remove_implies (Implies a b) =
    (Or (Not (remove_implies a)) (remove_implies b))"

thm boolexp.induct

lemma remove_implies_same_eval [simp]:
"boolexp_eval env (remove_implies a) =
 boolexp_eval env a"
apply (induct "a")
by simp_all
(*
by (induct "a", auto)
*)

fun number_of_implies where
   "number_of_implies TRUE = (0::nat)"
 | "number_of_implies FALSE = 0"
 | "number_of_implies (Var x) = 0"
 | "number_of_implies (Not a) = number_of_implies a"
 | "number_of_implies (And a b) =
   (number_of_implies a) + (number_of_implies b)"
 | "number_of_implies (Or a b) =
   (number_of_implies a) + (number_of_implies b)"
 | "number_of_implies (Implies a b) =
   (number_of_implies a) + (number_of_implies b) + 1" 

lemma number_of_implies_remove_implies_0 [simp]:
"number_of_implies (remove_implies a) = 0"
by (induct "a", auto)


fun push_not where   
   "push_not TRUE = TRUE"
 | "push_not FALSE = FALSE"
 | "push_not (Var x) = Var x"          
 | "push_not (Not TRUE) = FALSE"
 | "push_not (Not FALSE) = TRUE"
 | "push_not (Not (Var x)) = Not (Var x)"
 | "push_not (Not (Not a)) = push_not a"
 | "push_not (Not (And a b)) =
    (Or (push_not (Not a)) (push_not (Not b)))"
 | "push_not (Not (Or a b)) =
    (And (push_not (Not a)) (push_not (Not b)))"
 | "push_not (Not (Implies a b)) =
   (And (push_not a) (push_not (Not b)))"
 | "push_not (And a b) =
   (And (push_not a) (push_not b))"      
 | "push_not (Or a b) =
   (Or (push_not a) (push_not b))"      
 | "push_not (Implies a b) =
    (Implies (push_not a) (push_not b))"

lemma push_not_same_eval [simp]:
 "(boolexp_eval env (push_not (Not a))
   = (\<not> (boolexp_eval env (push_not a)))) \<and>
  (boolexp_eval env (push_not a) = boolexp_eval env a)"
by (induct "a", auto)

lemma push_not_preserves_no_implies_helper:
"number_of_implies a = 0 \<Longrightarrow>
 (number_of_implies (push_not a) = 0) \<and>
 (number_of_implies (push_not (Not a)) = 0)"
by (induct "a", auto)

lemma push_not_preserves_no_implies:
"number_of_implies a = 0 \<Longrightarrow>
 (number_of_implies (push_not a) = 0)"
by (auto simp add: push_not_preserves_no_implies_helper)

lemma push_not_remove_implies_no_implies [simp]:
"number_of_implies (push_not (remove_implies a)) = 0"
apply (rule push_not_preserves_no_implies)
apply (rule number_of_implies_remove_implies_0)
done


export_code boolexp_eval push_not remove_implies
in OCaml
 module_name Boolexp file "boolexp.ml"


datatype 'a boolexp_no_imp =
      TRUE_ni | FALSE_ni |Var_ni 'a
    | Not_ni "'a boolexp_no_imp"
    | And_ni "'a boolexp_no_imp" "'a boolexp_no_imp"
    | Or_ni "'a boolexp_no_imp" "'a boolexp_no_imp"

fun boolexp_no_imp_eval where
   "boolexp_no_imp_eval env TRUE_ni = True"
 | "boolexp_no_imp_eval env FALSE_ni = False"
 | "boolexp_no_imp_eval env (Var_ni x) = env x"
 | "boolexp_no_imp_eval env (Not_ni a) =
    (\<not> (boolexp_no_imp_eval env a))"
 | "boolexp_no_imp_eval env (And_ni a b) =
    ((boolexp_no_imp_eval env a) \<and>
     (boolexp_no_imp_eval env b))"
 | "boolexp_no_imp_eval env (Or_ni a b) =
    ((boolexp_no_imp_eval env a) \<or>
     (boolexp_no_imp_eval env b))"


fun remove_implies_ni where
   "remove_implies_ni TRUE = TRUE_ni"
 | "remove_implies_ni FALSE = FALSE_ni"
 | "remove_implies_ni (Var x) = Var_ni x"
 | "remove_implies_ni (Not a) =
    Not_ni (remove_implies_ni a)"
 | "remove_implies_ni (And a b) =
    And_ni (remove_implies_ni a) (remove_implies_ni b)"
 | "remove_implies_ni (Or a b) =
    Or_ni (remove_implies_ni a) (remove_implies_ni b)"
 | "remove_implies_ni (Implies a b) =
    (Or_ni (Not_ni (remove_implies_ni a))
           (remove_implies_ni b))"

lemma remove_implies_ni_same_eval:
  "boolexp_no_imp_eval env (remove_implies_ni a) =
   boolexp_eval env (remove_implies a)"
by (induct_tac a, auto)

datatype 'a boolexp_nipn =
    TRUE_nipn | FALSE_nipn |Var_nipn 'a
    | Not_Var_nipn 'a
    | And_nipn "'a boolexp_nipn" "'a boolexp_nipn"
    | Or_nipn "'a boolexp_nipn" "'a boolexp_nipn"

fun push_not_pn where
   "push_not_pn TRUE_ni = TRUE_nipn"
 | "push_not_pn FALSE_ni = FALSE_nipn"
 | "push_not_pn (Var_ni x) = Var_nipn x"      
 | "push_not_pn (Not_ni TRUE_ni) = FALSE_nipn"
 | "push_not_pn (Not_ni FALSE_ni) = TRUE_nipn"
 | "push_not_pn (Not_ni (Var_ni x)) = Not_Var_nipn x"
 | "push_not_pn (Not_ni (Not_ni a)) = push_not_pn a"
 | "push_not_pn (Not_ni (And_ni a b)) =
    (Or_nipn (push_not_pn (Not_ni a))
             (push_not_pn (Not_ni b)))"
 | "push_not_pn (Not_ni (Or_ni a b)) =
    (And_nipn (push_not_pn (Not_ni a))
              (push_not_pn (Not_ni b)))"
 | "push_not_pn (And_ni a b) = 
   (And_nipn (push_not_pn a) (push_not_pn b))"    
 | "push_not_pn (Or_ni a b) =
   (Or_nipn (push_not_pn a) (push_not_pn b))"

fun boolexp_nipn_eval where
   "boolexp_nipn_eval env TRUE_nipn = True"
 | "boolexp_nipn_eval env FALSE_nipn = False"
 | "boolexp_nipn_eval env (Var_nipn x) = env x"
 | "boolexp_nipn_eval env (Not_Var_nipn a) =
    (\<not> (env a))"
 | "boolexp_nipn_eval env (And_nipn a b) =
    ((boolexp_nipn_eval env a) \<and>
     (boolexp_nipn_eval env b))"
 | "boolexp_nipn_eval env (Or_nipn a b) =
    ((boolexp_nipn_eval env a) \<or>
     (boolexp_nipn_eval env b))"

lemma push_not_pn_same_eval [simp]:
"(boolexp_nipn_eval env (push_not_pn (Not_ni b)) =
  (\<not> (boolexp_no_imp_eval env b))) \<and>
 (boolexp_nipn_eval env (push_not_pn b) =
  boolexp_no_imp_eval env b)"
by (induct_tac b, auto)

fun node_count where     
   "node_count TRUE = (1::nat)"
 | "node_count FALSE = 1"
 | "node_count (Var x) = 1"
 | "node_count (Not x) = 1 + node_count x"
 | "node_count (And a b) =
    1 + (node_count a) + (node_count b)"
 | "node_count (Or a b) =
    1 + (node_count a) + (node_count b)"
 | "node_count (Implies a b) =
    1 + (node_count a) + (node_count b)" 
 
lemma node_count_non_zero [simp]:
"0 < node_count b"
by (induct_tac b, auto)

function push_not_elim_imp where   
   "push_not_elim_imp TRUE = TRUE_nipn"
 | "push_not_elim_imp FALSE = FALSE_nipn"
 | "push_not_elim_imp (Var x) = Var_nipn x"          
 | "push_not_elim_imp (Not TRUE) = FALSE_nipn"
 | "push_not_elim_imp (Not FALSE) = TRUE_nipn"
 | "push_not_elim_imp (Not (Var x)) = Not_Var_nipn x"
 | "push_not_elim_imp (Not (Not b)) =
    push_not_elim_imp b"
 | "push_not_elim_imp (Not (And a b)) =
    (Or_nipn (push_not_elim_imp (Not a))
             (push_not_elim_imp (Not b)))"
 | "push_not_elim_imp (Not (Or a b)) =
    (And_nipn (push_not_elim_imp (Not a))
              (push_not_elim_imp (Not b)))"
 | "push_not_elim_imp (Not (Implies a b)) =
   (And_nipn (push_not_elim_imp a)
             (push_not_elim_imp (Not b)))"
 | "push_not_elim_imp (And a b) =
   (And_nipn (push_not_elim_imp a)
             (push_not_elim_imp b))"      
 | "push_not_elim_imp (Or a b) =
   (Or_nipn (push_not_elim_imp a)
            (push_not_elim_imp b))"      
 | "push_not_elim_imp (Implies a b) =
    (Or_nipn (push_not_elim_imp (Not a))
             (push_not_elim_imp b))"                   
by (pat_completeness, auto)
term "op <*mlex*>"
termination
by (relation "measures [node_count]", auto)

lemma push_not_elim_imp_push_not_pn_remove_implies_ni [simp]:
"(push_not_elim_imp (boolexp.Not a) =
  push_not_pn (Not_ni (remove_implies_ni a))) \<and>
 (push_not_elim_imp a =
  push_not_pn (remove_implies_ni a))"
by (induct_tac a, auto)

lemma push_not_elim_imp_same_eval [simp]:
"(boolexp_nipn_eval env (push_not_elim_imp (Not a)) =
  (\<not>(boolexp_eval env a))) \<and>
 (boolexp_nipn_eval env (push_not_elim_imp a) =
  boolexp_eval env a)"
by (induct_tac a, auto)

datatype 'a bool_atom =
   TRUE_at | FALSE_at |Var_at 'a | Not_Var_at 'a
   
fun bool_atom_eval where
   "bool_atom_eval env TRUE_at = True"
 | "bool_atom_eval env FALSE_at = False"
 | "bool_atom_eval env (Var_at x) = env x"
 | "bool_atom_eval env (Not_Var_at x) = (\<not>(env x))"
 
datatype 'a bool_conj =
   Atom "'a bool_atom"
 | And_conj "'a bool_atom" "'a bool_conj"

fun bool_conj_eval where
   "bool_conj_eval env (Atom a) = bool_atom_eval env a"
 | "bool_conj_eval env (And_conj a b) =
    ((bool_atom_eval env a) \<and>
     (bool_conj_eval env b))"
     
fun conj_and where
   "conj_and (Atom a) b = And_conj a b"
 | "conj_and (And_conj a b) c =
    And_conj a (conj_and b c)"
    
lemma conj_and_eval [simp]:
"bool_conj_eval env (conj_and a b) =
 ((bool_conj_eval env a) \<and> (bool_conj_eval env b))"
by (induct_tac a, auto)

datatype 'a bool_dnf =
   Conj "'a bool_conj"
 | Or_dnf "'a bool_conj" "'a bool_dnf"

fun bool_dnf_eval where
   "bool_dnf_eval env (Conj c) = bool_conj_eval env c"
 | "bool_dnf_eval env (Or_dnf a b) =
    ((bool_conj_eval env a) \<or> (bool_dnf_eval env b))"

fun dnf_or where
   "dnf_or (Conj a) b = Or_dnf a b"
 | "dnf_or (Or_dnf a b) c = Or_dnf a (dnf_or b c)"
 
lemma dnf_or_eval [simp]:
"bool_dnf_eval env (dnf_or a b) =
  ((bool_dnf_eval env a) \<or> (bool_dnf_eval env b))"
by (induct_tac "a", auto)

fun conj_or where
   "conj_or a (Conj b) = Conj (conj_and a b)"
 | "conj_or a (Or_dnf b c) =
    Or_dnf(conj_and a b) (conj_or a c)"

lemma conj_or_eval [simp]:
"bool_dnf_eval env (conj_or a b) =
  ((bool_conj_eval env a) \<and> (bool_dnf_eval env b))"
by (induct_tac "b", auto)

fun dist_and_or where
   "dist_and_or (Conj a) b = conj_or a b"
 | "dist_and_or (Or_dnf a b) c =
    dnf_or (conj_or a c) (dist_and_or b c)"

lemma dist_and_or_and_eval [simp]:
"bool_dnf_eval env (dist_and_or a b) =
 ((bool_dnf_eval env a) \<and> (bool_dnf_eval env b))"
by (induct_tac a, auto)

fun basic_dnf where
   "basic_dnf TRUE_nipn = Conj(Atom TRUE_at)"
 | "basic_dnf FALSE_nipn = Conj(Atom FALSE_at)"
 | "basic_dnf (Var_nipn x) = Conj(Atom (Var_at x))"
 | "basic_dnf (Not_Var_nipn x) =
    Conj(Atom (Not_Var_at x))"
 | "basic_dnf (And_nipn a b) =
    dist_and_or (basic_dnf a) (basic_dnf b)"
 | "basic_dnf (Or_nipn a b) =
    dnf_or (basic_dnf a) (basic_dnf b)"
    
lemma basic_dnv_eval [simp]:
"bool_dnf_eval env (basic_dnf a) =
 boolexp_nipn_eval env a"
by (induct_tac a, auto)

definition dnf where
"dnf a = basic_dnf (push_not_elim_imp a)"

lemma dnf_eval [simp]:
"boolexp_eval env a = bool_dnf_eval env (dnf a)"
by (auto simp only: dnf_def push_not_elim_imp_same_eval basic_dnv_eval)

fun sat_bool_atom where
   "sat_bool_atom TRUE_at = Some (None)"
 | "sat_bool_atom FALSE_at = None"
 | "sat_bool_atom (Var_at x) = Some(Some(x,True))"
 | "sat_bool_atom (Not_Var_at x) = Some(Some(x,False))"

lemma sat_bool_atom_no_sat [simp]:
"sat_bool_atom a = None \<Longrightarrow> \<not>(bool_atom_eval env a)"
by (case_tac "a", simp_all)

lemma sat_bool_atom_sound [simp]:
"\<lbrakk> sat_bool_atom a = Some l;
   (l = None) \<or> l = Some (y, env y) \<rbrakk> \<Longrightarrow>
 bool_atom_eval env a"
by (induct a, auto)

lemma sat_bool_atom_complete [simp]:
"bool_atom_eval env a \<Longrightarrow>
\<exists> l y. ((sat_bool_atom a = Some l) \<and> 
     ((l = None) \<or> l = Some(y, env y)))"
apply (case_tac "sat_bool_atom a", auto)
by (induct a, auto)

fun member where
   "member x [] = False"
 | "member x (y#ys) = ((x = y) \<or> (member x ys))"
 
fun sat_conj where
   "sat_conj (Atom a) = 
    (case sat_bool_atom a of None \<Rightarrow> None
        | Some None \<Rightarrow> Some []
        | Some (Some (y,t)) \<Rightarrow> Some[(y,t)])"
 | "sat_conj (And_conj a b) =
    (case sat_bool_atom a of None \<Rightarrow> None
        | Some None \<Rightarrow> sat_conj b
        | Some (Some (y,t)) \<Rightarrow>
         (case sat_conj b of None \<Rightarrow> None
             | Some l \<Rightarrow>
               (if member (y,\<not>t) l then None
                else if member (y,t) l then Some l
                else Some ((y,t)#l))))"

fun sat_to_env where
   "sat_to_env [] = {env. True}"
 | "sat_to_env ((y,b)#l) = {env. env y = b} \<inter> (sat_to_env l)"

(*
lemma sat_conj_sound:
"\<lbrakk> sat_conj a = Some l; env \<in> sat_to_env l \<rbrakk> \<Longrightarrow> bool_conj_eval env a"
apply (induct "a", simp_all)  
apply (case_tac "bool_atom", simp_all)
apply auto
*)

fun sat_dnf where
    "sat_dnf (Conj a) =
     (case sat_conj a of None \<Rightarrow> []
         | Some l \<Rightarrow> [l])"
 | "sat_dnf (Or_dnf a b) =
    (case sat_conj a of None \<Rightarrow> sat_dnf b
        | Some l => l# (sat_dnf b))"

        
definition sat where
"sat a \<equiv> sat_dnf (dnf a)"

export_code sat
in OCaml
 module_name Sat file "sat.ml"


end
