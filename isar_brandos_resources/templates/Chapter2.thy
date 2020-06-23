theory Chapter2
imports Main
begin

text{*
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
*}

 "1 + (2::nat)"
 "1 + (2::int)"
 "1 - (2::nat)"
 "1 - (2::int)"
 "[a,b] @ [c,d]"

text{*
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
*}

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text{*
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
*}

lemma add_assoc: "add (add m n) p = add m (add n p)"
(* your definition/proof here *)

lemma add_comm: "add m n = add n m"
(* your definition/proof here *)

text{* Define a recursive function *}

fun double :: "nat \<Rightarrow> nat" where
(* your definition/proof here *)

text{* and prove that *}

lemma double_add: "double m = add m m"
(* your definition/proof here *)
text{*
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
*}

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
(* your definition/proof here *)
text {*
Test your definition of @{term count} on some examples.
Prove the following inequality:
*}

theorem "count xs x \<le> length xs"
(* your definition/proof here *)

text{*
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
(* your definition/proof here *)

text {*
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
*}

fun reverse :: "'a list \<Rightarrow> 'a list" where
(* your definition/proof here *)

text {*
Prove the following theorem. You will need an additional lemma.
*}
theorem "reverse (reverse xs) = xs"
(* your definition/proof here *)

text{*
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
*}

fun sum_upto :: "nat \<Rightarrow> nat" where
(* your definition/proof here *)

text {*
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
*}

lemma "sum_upto n = n * (n+1) div 2"
(* your definition/proof here *)

text{*
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
*}
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
(* your definition/proof here *)

text{*
Then define a function that sums up all values in a tree of natural numbers
*}

fun sum_tree :: "nat tree \<Rightarrow> nat" where
(* your definition/proof here *)

text{* and prove *}

lemma "sum_tree t = sum_list(contents t)"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions *}

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)

text{*
that traverse a tree and collect all stored values in the respective order in
a list. Prove *}

lemma "pre_order (mirror t) = rev (post_order t)"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Define a recursive function
*}

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
(* your definition/proof here *)

text{*
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
*}

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
(* your definition/proof here *)

text{*
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
*}

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
(* your definition/proof here *)

text{*
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
*}

lemma "itadd m n = add m n"
(* your definition/proof here *)

text{*
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
*}

fun nodes :: "tree0 \<Rightarrow> nat" where
(* your definition/proof here *)

text {*
Consider the following recursive function:
*}

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text {*
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
*}

text{*

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
*}

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text{*
Define a function @{text eval} that evaluates an expression at some value:
*}

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text{*
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
*}

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text{*
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
*}

fun coeffs :: "exp \<Rightarrow> int list" where
(* your definition/proof here *)

text{*
Prove that @{text coeffs} preserves the value of the expression:
*}

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
(* your definition/proof here *)

text{*
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
*}

end

