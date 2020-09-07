theory ishu_examples
  imports Main
begin


(*
proof step:

A A\<rightarrow>B
---- (modus ponens)
B

(?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q

P \<Longrightarrow> Q
----
P\<rightarrow>Q

tactic applies rules to some goal (or goals) and 
produces new goals (that hopefully help you finish the proof)

Once you have an empty list you showed your theorem!

Common way is reasoning backwards using tatics and facts/premises.
*)

lemma "(A \<and> B) \<longrightarrow> (B \<and> A)"
  thm impI
  apply (rule impI)
  thm conjI
  apply (rule conjI)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> (B \<and> A)"
  apply simp
done

(* sum (0 to n) = n(n+1)/2 *)
lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
  apply (induction n)
   apply simp
  apply simp
  done

end