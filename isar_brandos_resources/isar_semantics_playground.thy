theory isar_semantics_playground
imports Main
begin

lemma
  assumes n: "A" "C" and nn: "A"
  shows "A"
  by (simp add: nn)

(* what happens when name is repeated*)
lemma
  assumes n: "A" and n: "B"
  shows "A"
  thm n
  sorry

(* semantics of have *)

lemma
  assumes n: "A"
  shows "A"
proof -
  from n have goal: "A" by simp

  show ?thesis by sorry
qed

(* assumes in lemma *)

(* this shows n1 is available in the context *)
lemma
  assumes n1: "A" and n2: "B"
  shows "A"
proof -
  show "A" by (simp add: n1)
qed

lemma
  assumes n1: "A1" and n2: "A2"
  shows "A"
proof -
  show "A" by sorry
qed

(* semantics of assume *)

(* you can assume when the assumptiosn are on the shows *)
lemma 
  shows "A\<Longrightarrow>A"
proof -
  assume "A"
  from this show "A" by simp
qed

lemma 
  assumes "A"
  shows "A"
proof -
  have "A" by (simp add: assms)
  from this show "A" by (simp)
qed

lemma 
  assumes "A"
  shows "A"
proof -
  assume "A"
  from this show "A" by (simp)
qed

lemma 
  assumes "A"
  shows "A"
proof -
  show "A" by (simp add: assms)
qed

lemma
  assumes "A"
  shows "A"
proof -
  from assms show "A" by assumption
qed

(* fails, intorduces A twice as an assumption *)
lemma
  assumes "A"
  shows "A"
proof -
  assume "A"
  show "A\<Longrightarrow>A" by assumption
qed

lemma
  assumes "P \<or> Q"
  shows "G"
proof -
  have 0: "P \<or> Q" using assms by simp
  from this show "G"
  proof

(* semantics of show *)

(* fails*)
lemma "\<lbrakk>A1;A2\<rbrakk> \<Longrightarrow> G2"
proof -
  show G1

lemma "\<lbrakk>A1;A2\<rbrakk> \<Longrightarrow> G2"
proof-
  assume A1 A2
  from this show G2 by sorry
qed

(* fails *)
lemma shows "A\<Longrightarrow>G1" "B\<Longrightarrow>G2"
proof -
  assume A
  from this show G1 by sorry
  assume B
  from this show G2 by sorry
qed

lemma shows "A\<Longrightarrow>G1" "B\<Longrightarrow>G2"
proof -
  assume A
  from this show G1 by sorry
next
  assume B
  from this show G2 by sorry
qed

(* what updates term bidings *)

lemma shows "A"
proof -
  let ?x = "a"

lemma assumes "C" shows "A"
proof -
  have "B" by sorry
  assume "CC"
  have "BB" 
  proof -
    have "CCC" by sorry
    show "BB" by sorry
  qed

(* next semantics *)

lemma 
  assumes "A" 
  shows "A1\<Longrightarrow>G1" "A2\<Longrightarrow>G2"
proof -
  assume "A1"
  show "G1" by sorry
next
  assume "A2"
  show "G2" by sorry
qed



end