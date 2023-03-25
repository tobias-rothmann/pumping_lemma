theory Defs
  imports Main HOL.Finite_Set 
begin
section \<open>DFA Definition\<close>

subsection \<open>DFA Types\<close>

type_synonym state = int
type_synonym symbol = char
type_synonym transitions = "state \<Rightarrow> symbol \<Rightarrow> state"
type_synonym word = "symbol list"

record DFA = 
  Q:: "state set"
  \<Sigma>:: "symbol set"
  \<delta>:: "transitions"
  q\<^sub>0:: state
  F:: "state set"

subsection \<open>DFA  properties\<close>

definition Q_\<Sigma>_finite :: "DFA \<Rightarrow> bool" where
  "Q_\<Sigma>_finite dfa = (finite (Q dfa) \<and> finite (\<Sigma> dfa))"

definition \<delta>_total_on_Q_\<Sigma> :: "DFA \<Rightarrow> bool" where
  "\<delta>_total_on_Q_\<Sigma> dfa = (\<forall>s \<in> (Q dfa) . \<forall>c \<in> (\<Sigma> dfa). (\<delta> dfa) s c \<in> (Q dfa))" (*total und abgeschlossen*)

definition q\<^sub>0_in_Q :: "DFA \<Rightarrow> bool" where 
  "q\<^sub>0_in_Q dfa = ((q\<^sub>0 dfa) \<in> (Q dfa))"

definition F_sub_Q :: "DFA \<Rightarrow> bool" where 
  "F_sub_Q dfa = ((F dfa) \<subseteq> (Q dfa))"

subsection \<open>Definitions on DFA\<close>

inductive word :: "state \<Rightarrow> state \<Rightarrow> DFA \<Rightarrow> word \<Rightarrow> bool" where
empty:  "q\<in>(Q dfa) \<Longrightarrow> word q q dfa ''''" |
step: "\<lbrakk>word q q' dfa w ;c \<in> (\<Sigma> dfa); p \<in> (Q dfa); (\<delta> dfa) q' c = p\<rbrakk> \<Longrightarrow>  word q p dfa (w@[c])" |
back_step: "\<lbrakk>word q q' dfa w ;c \<in> (\<Sigma> dfa); p \<in> (Q dfa); (\<delta> dfa) p c = q\<rbrakk> \<Longrightarrow>  word p q' dfa (c#w)"

fun lang :: "DFA \<Rightarrow> word set" where
  "lang dfa = {w. \<exists>q \<in> (F dfa). word (q\<^sub>0 dfa) q dfa w }"

end