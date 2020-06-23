theory proof_transition
imports Main
begin

(* Lemma definition semantics and a simple way to end proof with by*)

lemma "A" by sorry

lemma 
  shows "A"
  by sorry

lemma
  assumes n1: "A"
  shows n2: "A"
  by sorry

lemma
  shows n: "A\<Longrightarrow>A"
  by sorry

lemma
  assumes n1: "A"
  shows n3: "A"
  by (simp add: n1)

lemma
  shows n4: "A\<Longrightarrow>A"
  by simp

(*  Lemma definition semantics with assume *)

lemma
  assumes n1: "A"
  shows n5: "A"
proof -
  assume "A"
  from this show "A" (* failed to refine any pending goal*) by sorry
qed

lemma
  assumes n1: "A"
  shows n6: "A"
proof -
  from n1 show "A" by assumption
qed

lemma
  shows n7: "A \<Longrightarrow> A"
proof -
  assume l1: "A"
  from l1 show "A" by assumption
qed

(* *)

lemma
  assumes a1: "A"
  shows n8: "A"
proof -
  from a1 have l1: "A" by simp
  from l1 show "A" by simp
qed
  

end