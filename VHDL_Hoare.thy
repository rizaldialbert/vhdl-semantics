(*
 * Copyright 2018-2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory VHDL_Hoare
  imports Femto_VHDL_raw
begin

text \<open>This theory is the first attempt for defining a Hoare logic for VHDL sequential statement.
As the exploration continues, I realise that we can only prove the soundness in this first attempt
but not the completeness. The second attempt is shown in @{theory_text "VHDL_Hoare_Complete"}. Even
though we cannot show that it is complete, many theorems and definitions in this theory are useful
for defining a sound and complete Hoare logic in @{theory_text "VHDL_Hoare_Complete"}.\<close>

subsection \<open>Hoare Logic for @{typ "'signal seq_stmt"}\<close>

type_synonym 'signal worldline = "'signal \<Rightarrow> nat \<Rightarrow> val"

text \<open>The type @{typ "'signal worldline"} represent the concept of ``worlds'' which are required
for the axiomatic semantics of VHDL specified in @{cite Breuer1995}. As can be seen from the
definition, this type represents a function with two arguments: @{term "signal :: 'signal"} and
@{term "time :: nat"} to a set of value.

Compared to the standard ``worlds'' for defining the axiomatic semantics of sequential programming
language --- e.g. @{typ "'variable \<Rightarrow> val"} --- we have added the notion of @{term "time :: nat"}
here. For example, when we do assignment in VHDL, we can specify the time when this assignment will
happen in the future. This construct is, of course, absent from the typical assignment in sequential
programming language where assignments happen instantaneously. It is due to this notion of time, we
add a suffix ``line'' in the type @{typ "'signal worldline"}.

What is the relationship between @{typ "'signal worldline"} with the context @{term "\<sigma> :: 'signal
state"}, @{term "\<gamma> :: 'signal event"}, @{term "\<theta> :: 'signal trans_raw"}, @{term "\<tau>' \<tau> :: 'signal
trans_raw"} in the semantics @{term "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"}? The answer is that the latter
is the refined version of the former. We shall show the formal relationship later in this theory.
\<close>

definition worldline_upd :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline"
  ("_[_, _:= _]") where
  "worldline_upd w s t v = (\<lambda>s' t'. if s' \<noteq> s \<or> t' < t then w s' t' else v)"

definition worldline_inert_upd :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline"
  ("_[_, _, _ := _]") where
  "worldline_inert_upd w s t dly v = (\<lambda>s' t'. if s' \<noteq> s \<or> t' < t then w s' t' else
                                              if t' < t + dly     then w s' t  else v)"

text \<open>These are the two constructs we can use to update or modify a @{typ "'signal worldline"}. Note
that the syntax between these two are quite similar. The only difference is the number of arguments
on the left of the equality sign: @{term "worldline_upd"} has two while @{term
"worldline_inert_upd"} has three. As the names suggest, they correspond to the transport delay
assignment @{term "Bassign_trans"} and inertial delay assignment @{term "Bassign_inert"}.\<close>

type_synonym 'signal assn = "'signal worldline \<Rightarrow> bool"

text \<open>The type @{typ "'signal assn"} represents a predicate over a worldline, i.e., a property
about a worldline. The pre- and post-condition of a VHDL sequential statement will be of this type.\<close>

definition state_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal state" where
  "state_of_world w t = (\<lambda>s. w s t)"

definition event_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal event" where
  "event_of_world w t = (if t = 0 then {s :: 'signal. w s 0 \<noteq> False} else {s :: 'signal. w s t \<noteq> w s (t - 1)})"

definition beh_of_world_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "beh_of_world_raw w t = (\<lambda>t'. if t' < t then (\<lambda>s. Some (w s t')) else Map.empty)"

(* lift_definition beh_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal transaction" is beh_of_world_raw
  unfolding beh_of_world_raw_def zero_map by auto

lemma [simp]:
  "beh_of_world w 0 = 0"
  by (transfer', auto simp add:  beh_of_world_raw_def zero_option_def zero_fun_def) *)

definition beval_world_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal bexp \<Rightarrow> val" where
  "beval_world_raw w t exp = beval_raw t (state_of_world w t) (event_of_world w t) (beh_of_world_raw w t) exp"

text \<open>As promised in the beginning of this theory, we show the first relationship from @{typ
"'signal worldline"} to the realm of @{typ "'signal state"}, @{typ "'signal event"}, and @{typ
"'signal trans_raw"}.

For @{term "state_of_world"}, the definition is obvious. We need a function abstraction --- instead
of simply giving an argument to function @{term "w :: 'signal worldline"} to return another function
--- here because the different order of the arguments: in @{typ "'signal worldline"} the name of the
signal comes before the time.

Event represents the set of signals whose values are different from the previous time. Here is the
dilemma: what happens at time @{term "0::nat"}? There is no such time as @{term "0 - 1"} as this
will evaluate to @{term "0"} in natural numbers. Nevertheless, event at time @{term "0 :: nat"}
has different interpretation: it is the set of signals whose values are different from the default
values, i.e., @{term "False :: val"}. The expression for else-statement in @{term "event_of_world"}
is obvious.

Note that @{term "beh_of_world"} requires a lift_definition instead of standard definition
construct; this is due to @{typ "'signal trans_raw"}. Its raw version @{term "beh_of_world_raw"}
only maps until the time @{term "t"} only. This is because behaviour is synonymous with history in
our definition and, according to the order of time, we do not have any ``mapping'' from time now
until the future.
\<close>

inductive
  seq_hoare :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool"
  ("\<turnstile>\<^sub>_ ({(1_)}/ (_)/ {(1_)})" 50) where
Null: "\<turnstile>\<^sub>t {P} Bnull {P}" |

Assign: "\<turnstile>\<^sub>t {\<lambda>w. P(w[sig, t + dly := beval_world_raw w t exp])} Bassign_trans sig exp dly {P}" |

AssignI: "\<turnstile>\<^sub>t {\<lambda>w. P(w[sig, t, dly := beval_world_raw w t exp])} Bassign_inert sig exp dly {P}" |

Comp: "\<lbrakk> \<turnstile>\<^sub>t {P} s1 {Q}; \<turnstile>\<^sub>t {Q} s2 {R}\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P} Bcomp s1 s2 {R}" |

If: "\<lbrakk>\<turnstile>\<^sub>t {\<lambda>w. P w \<and> beval_world_raw w t g} s1 {Q}; \<turnstile>\<^sub>t {\<lambda>w. P w \<and> \<not> beval_world_raw w t  g} s2 {Q}\<rbrakk>
        \<Longrightarrow>  \<turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}" |

Conseq: "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile>\<^sub>t {P} s {Q}; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} s {Q'}"

text \<open>The inductive definition @{term "seq_hoare"} is similar to the inductive definition @{term
"hoare"} in @{theory_text "Hoare"}. Rules other than @{thm "Assign"} and @{thm "AssignI"} are
standard; we explain those two only here. As can be seen, the construct @{term "worldline_upd"} and
@{term "worldline_inert_upd"} are designed for the purpose of defining the axiomatic semantics
of VHDL. We show how it makes sense later in the soundness property.\<close>

inductive_cases seq_hoare_ic: "\<turnstile>\<^sub>t {P} s {Q}"

lemma BnullE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bnull"
  shows "\<forall>w. P w \<longrightarrow> Q w"
  using assms
  by (induction rule:seq_hoare.induct, auto)

lemma BnullE':
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<forall>w. P w \<longrightarrow> Q w"
  using BnullE by blast

lemma BassignE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly := beval_world_raw w t exp])"
  using assms
  by (induction rule: seq_hoare.induct, auto)

lemma Bassign_inertE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t, dly := beval_world_raw w t exp])"
  using assms
  by (induction rule: seq_hoare.induct, auto)

lemma BcompE:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile>\<^sub>t {P} s1 {Q} \<and> \<turnstile>\<^sub>t {Q} s2 {R}"
  using assms Conseq
  by (induction rule:seq_hoare.induct, auto) (blast)

lemmas [simp] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If
lemmas [intro!] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If

lemma strengthen_pre:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P'} s {Q}"
  using assms by (blast intro: Conseq)

lemma weaken_post:
  assumes "\<forall>w. Q w \<longrightarrow> Q' w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P} s {Q'}"
  using assms by (blast intro: Conseq)

lemma Assign':
  assumes "\<forall>w. P w \<longrightarrow> Q (worldline_upd w sig (t + dly) (beval_world_raw w t exp))"
  shows "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  using assms by (simp add: strengthen_pre)

subsection \<open>Validity of Hoare proof rules\<close>

text "worldline_raw"

definition worldline_raw ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal worldline" where
  "worldline_raw t \<sigma> \<theta> \<tau> = (\<lambda>s' t'. if t' < t then signal_of False \<theta> s' t' else signal_of (\<sigma> s') \<tau> s' t')"

text \<open>@{term "worldline_raw"} is a constructor here. Note that we have used the same identifier (name)
for the constructor and the type here. This construct is the link from the operational semantics's
world such as @{typ "'signal state"}, @{typ "'signal trans_raw"} to the axiomatic semantics's
world @{typ "'signal worldline"}.

An observant reader might have noticed that there is no @{typ "'signal event"} when we construct
@{typ "'signal worldline"}. This is because, as Breuer and Kloos~@{cite "Breuer1995"} argued, the
notion of event can be reconstructed from the notion of @{typ "'signal worldline"}. Or,
alternatively, the notion of event is inherent in @{typ "'signal worldline"}. Simply find the
signals which have different values from those at the previous time correspondingly suffices for
reconstructing the event at every time point.\<close>

definition difference_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "difference_raw w t = (if t = 0 then 
                            (\<lambda>s. if w s t then Some True else None) 
                          else
                            (\<lambda>s. if w s t \<noteq> w s (t - 1) then Some (w s t) else None))"

definition derivative_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where "derivative_raw \<equiv> (\<lambda>w t n. if n \<le> t then Map.empty else difference_raw w n)"

definition derivative_hist_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where "derivative_hist_raw \<equiv> \<lambda>w t n. if t \<le> n then Map.empty else difference_raw w n"

text \<open> The function @{term "derivative_raw"} is a function to obtain the transaction
@{term "\<tau> :: 'signal trans_raw"} in the operational semantics @{term "b_seq_exec"}. Note that to
use @{typ "'signal worldline"} as a context to define the axiomatic semantics of VHDL, it is always
paired with a time variable @{term "t :: nat"}. This variable denotes the current time of the
computation; anything strictly before this time is a history (related to the notion of behaviour
@{term "\<theta> :: 'signal trans_raw"})  and anything after this time is a prediction (related to
the notion of transaction @{term "\<tau> :: 'signal trans_raw"}).

The naming ``derivative'' signifies that this function acts similarly to a derivative in the
real number calculus. Hence, the derivative here only record those values which are different
(via @{term "difference_raw"}) from the value at the previous time (hence the name ``difference''
as the derivative counterpart for discrete-time signal).

Why do we still have the suffix ``raw'' in @{term "derivative_raw"}? Because we will still lift
this definition further as will be explained in @{theory_text "VHDL_Hoare_Complete"}.
\<close>

lemma derivative_raw_zero:
  assumes "\<forall>n \<ge> d. \<forall>s. w s n = w s d" and "d \<le> t"
  shows "derivative_raw w t = 0"
proof  
  fix n :: nat
  have "n \<le> t \<or> t < n" by auto
  moreover
  { assume "n \<le> t"
    hence "derivative_raw w t n  = 0"
      unfolding derivative_raw_def by (auto simp add: zero_fun_def zero_option_def) }
  moreover
  { assume "t < n"
    hence "derivative_raw w t n = difference_raw w n"
      unfolding derivative_raw_def by auto
    also have "... = 0"
    proof -
      have "\<forall>s. w s n = w s d"
        using assms(1) `d \<le> t` `t < n`  by (meson le_eq_less_or_eq le_less_trans)
      moreover have "\<forall>s. w s (n - 1) = w s d"
        using assms(1) `d \<le> t` `t < n`
        by (metis Suc_diff_1 diff_is_0_eq' diff_less_mono leI less_Suc_eq_le not_less_zero)
      ultimately have "\<forall>s. w s n = w s (n - 1)"
        by auto
      thus ?thesis 
        using `t < n` unfolding difference_raw_def by (auto simp add: zero_option_def zero_fun_def)
    qed
    finally have "derivative_raw w t n = 0"
      by auto }
  ultimately show "derivative_raw w t n = 0 n"
    by (auto simp add: zero_fun_def)
qed

lemma
  "n < t \<Longrightarrow> (derivative_raw w t) n = 0"
   by (auto simp add:derivative_raw_def zero_fun_def zero_option_def)  

lemma lookup_derivative_in_between:
  "t < n \<Longrightarrow> derivative_raw w t n = difference_raw w n"
  by (auto simp add: derivative_raw_def)

lemma
  assumes "\<forall>n \<ge> d. \<forall>s. w s n = w s d" and "d < n"
  shows "derivative_raw w t n = 0"
proof -
  have "n \<le> t \<or> t < n" by auto
  moreover
  { assume "n \<le> t"
    hence "derivative_raw w t n = 0"
      unfolding derivative_raw_def by (auto simp add: zero_fun_def zero_option_def) }
  moreover
  { assume "t < n"
    hence "derivative_raw w t n = difference_raw w n"
      unfolding derivative_raw_def by auto
    also have "... = 0"
    proof -
      have "\<forall>s. w s n = w s d"
        using assms le_eq_less_or_eq by blast
      moreover have "\<forall>s. w s (n - 1) = w s d"
        using assms  by (metis Suc_diff_1 le_less_trans less_Suc_eq_le zero_le)
      ultimately have "\<forall>s. w s n = w s (n - 1)"
        by auto
      thus ?thesis
        using `t < n` unfolding difference_raw_def by (auto simp add: zero_fun_def zero_option_def)
    qed
    ultimately have "derivative_raw w t n = 0"
      by auto }
  ultimately show "derivative_raw w t n = 0"
    by auto
qed

lemma signal_of_derivative_hist_raw:
  assumes "t' < t"
  shows "signal_of False (derivative_hist_raw w t) s' t' = w s' t'"
  using assms
proof (induction t')               
  case 0
  have "derivative_hist_raw w t 0 = difference_raw w 0"
    using 0 by (auto simp add: derivative_hist_raw_def)
  have " w s' 0 \<or> \<not> w s' 0"
    by auto
  moreover
  { assume " w s' 0"
    hence "difference_raw w 0 s' = Some True"
      unfolding difference_raw_def by auto
    hence "derivative_hist_raw w t 0 s' = Some True"
      using `derivative_hist_raw w t 0 = difference_raw w 0` by auto
    hence ?case
      using `w s' 0` 
      by (intro trans_some_signal_of', simp) }
  moreover
  { assume "\<not> w s' 0"
    hence "difference_raw w 0 s' = None"
      unfolding difference_raw_def by auto
    hence "derivative_hist_raw w t 0 s' = None"
      using `derivative_hist_raw w t 0 = difference_raw w 0` by auto
    hence "signal_of False (derivative_hist_raw w t) s' 0 = False"
      by (intro signal_of_zero, simp add: zero_option_def)
    hence ?case
      using `\<not> w s' 0` by auto }
  ultimately show ?case by auto
next
  case (Suc t')
  have "w s' (Suc t') = w s' t' \<or> w s' (Suc t') \<noteq> w s' t'"
    by auto
  moreover
  { assume "w s' (Suc t') \<noteq> w s' t'"
    have "derivative_hist_raw w t (Suc t') = difference_raw w (Suc t')"
      using Suc by (auto simp add: derivative_hist_raw_def)
    moreover have "difference_raw w (Suc t') s' = Some (w s' (Suc t'))"
      using Suc `w s' (Suc t') \<noteq> w s' t'` unfolding difference_raw_def by auto
    ultimately have "derivative_hist_raw w t (Suc t') s' = Some (w s' (Suc t'))"
      by auto
    hence ?case
      by (intro trans_some_signal_of', simp) }
  moreover 
  { assume " w s' (Suc t') = w s' t'"
    have "derivative_hist_raw w t (Suc t') = difference_raw w (Suc t')"
      using Suc by (auto simp add : derivative_hist_raw_def)
    moreover have "difference_raw w (Suc t') s' = None"
      using Suc `w s' (Suc t') = w s' t'` unfolding difference_raw_def by auto
    ultimately have "derivative_hist_raw w t (Suc t') s' = None"
      by auto
    hence "signal_of False (derivative_hist_raw w t) s' (Suc t') =  signal_of False (derivative_hist_raw w t) s' t'"
      by (intro signal_of_suc_sig) (simp add: zero_option_def) 
    also have "... = w s' t'"
      using Suc by auto
    finally have ?case
      using `w s' (Suc t') = w s' t'` by auto }
  ultimately show ?case by auto
qed

lemma signal_of_derivative_hist_raw2:
  assumes "t \<le> t'" and "0 < t"
  shows "signal_of False (derivative_hist_raw w t) s' t' = w s' (t - 1)"
proof -
  have "t - 1 < t"
    using assms by auto
  have "signal_of False (derivative_hist_raw w t) s' t' = signal_of False (derivative_hist_raw w t) s' t"
    using assms 
    by (intro signal_of_less_ind')(auto simp add: derivative_hist_raw_def zero_option_def)
  also have "... = signal_of False (derivative_hist_raw w t) s' (t - 1)"
    by (intro signal_of_less_sig) (auto simp add: derivative_hist_raw_def zero_option_def)
  also have "... = w s' (t - 1)"
    using signal_of_derivative_hist_raw[OF `t - 1 < t`] by metis
  finally show "signal_of False (derivative_hist_raw w t) s' t' = w s' (t - 1)"
    by auto
qed

lemma signal_of_derivative_raw_t:
  assumes "\<sigma> s' = w s' t"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t = w s' t"
proof -
  have "derivative_raw w t t = Map.empty"
    using assms by (auto simp add: derivative_raw_def)
  have *: "\<And>n. 0 < n \<Longrightarrow> n \<le> t \<Longrightarrow>  derivative_raw w t n = 0"
    by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)  
  have "signal_of (\<sigma> s') (derivative_raw w t) s' t = signal_of (\<sigma> s') (derivative_raw w t) s' 0"
    using * by (cases "t = 0")(rule_tac[!] signal_of_less_ind, simp_all)
  also have "... = \<sigma> s'"
    by(intro signal_of_zero) (auto simp add: derivative_raw_def zero_option_def)
  finally show ?thesis     
    using assms by auto
qed

lemma signal_of_derivative_raw:
  assumes "t \<le> t'"
  assumes "w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' t'"
  using assms
proof (induction t')
  case 0
  hence "t = 0" by auto
  have lookup: "derivative_raw w 0 0 = Map.empty"
    by (auto simp add: derivative_raw_def)
  hence " signal_of (\<sigma> s') (derivative_raw w t) s' 0 =  signal_of (\<sigma> s') (derivative_raw w 0) s' 0"
    unfolding `t = 0` by auto
  also have "... = \<sigma> s'"
    using lookup signal_of_zero by (metis (no_types, lifting) zero_option_def)
  also have "... = w s' 0"
    using `w s' t = \<sigma> s'` `t = 0` by auto
  finally show ?case by auto
next
  case (Suc t')
  hence "Suc t' = t \<or> t < Suc t'"
    by auto
  moreover
  { assume "Suc t' = t"
    have lookup: "derivative_raw w t (Suc t') = Map.empty"
      unfolding `Suc t' = t` by (auto simp add: derivative_raw_def)
    have " \<And>n. 0 < n \<Longrightarrow> n \<le> Suc t' \<Longrightarrow> (derivative_raw w t) n = 0"
      unfolding `Suc t' = t` by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
    hence " signal_of (\<sigma> s') (derivative_raw w t) s' (Suc t') =  signal_of (\<sigma> s') (derivative_raw w t) s' 0"
      by (intro signal_of_less_ind, simp_all)
    also have "... = \<sigma> s'"
      by (metis (full_types, hide_lams) Suc.prems(2) \<open>Suc t' = t\<close> assms(2) calculation 
      signal_of_derivative_raw_t)
    also have "... = w s' (Suc t')"
      using `w s' t = \<sigma> s'` `Suc t' = t` by auto
    finally have ?case unfolding `Suc t' = t` by auto }
  moreover
  { assume "t < Suc t'"
    hence "t \<le> t'" 
      by auto
    hence lookup: " (derivative_raw w t) (Suc t') = difference_raw w (Suc t')"
      by (auto simp add: derivative_raw_def)
    have "w s' (Suc t') = w s' t' \<or> w s' (Suc t') \<noteq> w s' t'"
      by auto
    moreover
    { assume "w s' (Suc t') = w s' t'"
      hence "difference_raw w (Suc t') s' = None"
        unfolding difference_raw_def by auto
      hence "(derivative_raw w t) (Suc t') s' = None"
        using lookup by auto
      hence "signal_of (\<sigma> s') (derivative_raw w t) s' (Suc t') =  signal_of (\<sigma> s') (derivative_raw w t) s' t'"
        by(intro signal_of_suc_sig)(simp add: zero_option_def)    
      also have "... = w s' t'"
        using Suc(1)[OF `t \<le> t'` Suc(3)] by auto
      also have "... = w s' (Suc t')"
        using `w s' (Suc t') = w s' t'` by auto
      finally have ?case by auto }
    moreover
    { assume "w s' (Suc t') \<noteq> w s' t'"
      hence "difference_raw w (Suc t') s' = Some (w s' (Suc t'))"
        unfolding difference_raw_def by auto
      hence "(derivative_raw w t) (Suc t') s' = Some (w s' (Suc t'))"
        using lookup by auto
      hence ?case
        by (intro trans_some_signal_of') }
    ultimately have ?case by auto }
  ultimately show ?case by auto 
qed

lemma signal_of_derivative_raw2:
  assumes "\<forall>n\<ge>d. w s' n = w s' d"
  assumes "d \<le> t'"
  assumes "w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' d"
proof -
  have "\<And>n. d < n \<Longrightarrow> n \<le> t' \<Longrightarrow>  (derivative_raw w t) n s' = 0"
  proof -
    fix n
    assume "d < n" and "n \<le> t'"
    have "n \<le> t \<or> t < n" by auto
    moreover
    { assume "n \<le> t"
      hence "derivative_raw w t n s' = 0"
        unfolding derivative_raw_def by (auto simp add: zero_fun_def zero_option_def) }
    moreover
    { assume "t < n"
      have "w s' n = w s' d"
        using assms `d < n`  using less_imp_le_nat by blast
      also have "... = w s' (n-1)"
        using `d < n` assms(1) by (metis Suc_diff_1 less_Suc_eq_0_disj less_Suc_eq_le
        less_imp_Suc_add)
      finally have "w s' n = w s' (n - 1)"
        by auto
      hence "derivative_raw w t n s' = difference_raw w n s'"
        using `t < n` unfolding derivative_raw_def by auto
      also have "... = None"
        unfolding difference_raw_def using \<open>w s' n = w s' (n-1)\<close> `t < n` by auto 
      finally have "derivative_raw w t n s' = 0"
        unfolding zero_option_def by auto }
    ultimately show "derivative_raw w t n s' = 0"
      by auto
  qed
  from signal_of_less_ind'[where \<tau>=" (derivative_raw w t)", OF this]
  have *: "signal_of (\<sigma> s') (derivative_raw w t) s' t' = signal_of (\<sigma> s') (derivative_raw w t) s' d"
    using assms(2) using le_eq_less_or_eq by  auto
  have "t \<le> t' \<or> t' < t" by auto
  moreover
  { assume "t \<le> t'"
    have "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' t'"
      using signal_of_derivative_raw[OF `t \<le> t'`, of "w" "s'" "\<sigma>", OF assms(3)]  by auto
    also have "... = w s' d"
      using assms(1-2)  by blast
    finally have "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' d"
      by auto }
  moreover
  { assume "t' < t"
    have "signal_of (\<sigma> s') (derivative_raw w t) s' d = signal_of (\<sigma> s') (derivative_raw w t) s' 0"
    proof (intro  signal_of_less_ind')
      fix n
      assume "0 < n" and "n \<le> d"
      thus "derivative_raw  w t n s' = 0"
        unfolding derivative_raw_def using `d \<le> t'` `t' < t` by (auto simp add: zero_option_def)
    qed (auto)
    also have "... = \<sigma> s'"
      by (intro signal_of_zero)(auto intro!: signal_of_zero simp add: derivative_raw_def
      zero_option_def)
    also have "... = w s' t"
      using assms(3) by auto
    also have "... = w s' d"
      using assms(1) `t' < t` `d \<le> t'` by (meson less_trans not_le)
    finally have "signal_of (\<sigma> s') (derivative_raw w t) s' d = w s' d"
      by auto 
    hence "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' d"
      using * by auto }
  ultimately show ?thesis by auto 
qed

lemma signal_of_derivative_raw':
  assumes "t \<le> t'" and "t \<le> d"
  assumes "\<And>n s. d < n \<Longrightarrow> w s n = w s d"
  assumes "w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = w s' t'"
  using assms by (metis signal_of_derivative_raw)

lemma signal_of_derivative_raw_degree_lt_now:
  assumes "\<forall>n\<ge> d. \<forall>s. w s n = w s d"
  assumes "d < t"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = \<sigma> s'"
proof -
  have "derivative_raw w t = 0"
    using derivative_raw_zero assms by (simp add: derivative_raw_zero)
  moreover have "signal_of (\<sigma> s') 0 s' t' = \<sigma> s'"
    using signal_of_empty unfolding zero_fun_def by metis
  ultimately show ?thesis by auto
qed

lemma signal_of2_derivative_before_now:
  assumes "t' < t"
  shows "signal_of def (derivative_raw w t) s' t' = def"
proof -
  have *: "\<And>k. k < t \<Longrightarrow>  (derivative_raw w t) k = Map.empty"
    by (auto simp add: derivative_raw_def)
  hence "\<And>n. 0 < n \<Longrightarrow> n \<le> t' \<Longrightarrow>  (derivative_raw w t) n = 0"
    using `t' < t` unfolding derivative_raw_def by (auto simp add: zero_fun_def zero_option_def)
  hence "signal_of def (derivative_raw w t) s' t' = signal_of def (derivative_raw w t) s' 0"
    by (intro signal_of_less_ind, simp_all)
  also have "... = def"
    by (intro signal_of_zero, auto simp add: derivative_raw_def zero_option_def)
  finally show "signal_of def (derivative_raw w t) s' t' = def"
    by auto
qed

(* lemma exists_quiesce_worldline:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "\<exists>n. \<forall>k > n. \<forall>s. worldline t \<sigma> \<theta> \<tau> s k = worldline t \<sigma> \<theta> \<tau> s n"
proof (cases "\<tau> = 0")
  case True
  { fix k s
    assume "k > t"
    hence "worldline t \<sigma> \<theta> \<tau> s k = signal_of2 (\<sigma> s) \<tau> s k"
      unfolding worldline_def by auto
    also have "... = signal_of2 (\<sigma> s) \<tau> s t"
      unfolding `\<tau> = 0` apply transfer'  using signal_of_empty unfolding zero_fun_def by metis
    finally have "worldline t \<sigma> \<theta> \<tau> s k = signal_of2 (\<sigma> s) \<tau> s t"
      by auto }
  then show ?thesis
    (* by (meson worldline_def) *)
next
  case False
  have "t < Poly_Mapping.degree \<tau>"
    using trans_degree_gt_t[OF assms False] by auto
  { fix k s
    assume "k > Poly_Mapping.degree \<tau> - 1"
    hence expl: "worldline t \<sigma> \<theta> \<tau> s k = signal_of2 (\<sigma> s) \<tau> s k"
      unfolding worldline_def using `t < Poly_Mapping.degree \<tau>` by auto
    have expr: " worldline t \<sigma> \<theta> \<tau> s (Poly_Mapping.degree \<tau> - 1) = signal_of2 (\<sigma> s) \<tau> s (Poly_Mapping.degree \<tau> - 1)"
      unfolding worldline_def using `t < Poly_Mapping.degree \<tau>` by auto
    have "\<And>n. Poly_Mapping.degree \<tau> - 1 < n \<Longrightarrow> n \<le> k \<Longrightarrow> lookup \<tau> n = 0"
      by (simp add: beyond_degree_lookup_zero)
    hence " signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau> s (Poly_Mapping.degree \<tau> - 1)"
      by (meson \<open>Poly_Mapping.degree \<tau> - 1 < k\<close> signal_of2_less_ind)
    with expl and expr have "worldline t \<sigma> \<theta> \<tau> s k = worldline t \<sigma> \<theta> \<tau> s (Poly_Mapping.degree \<tau> - 1)"
      by auto }
  then show ?thesis
    by (meson worldline_def)
qed *)

(* lemma empty_transaction_deg_lt_t:
  fixes \<theta> \<sigma> t
  assumes "\<tau> = 0"
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  defines "w \<equiv> worldline t \<sigma> \<theta> \<tau>"
  defines "d \<equiv> (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n)"
  shows "d \<le> t"
proof -
  have "w = (\<lambda>s' t'. if t' < t then signal_of2 False \<theta> s' t' else signal_of2 (\<sigma> s') \<tau> s' t')"
    unfolding w_def worldline_def by auto
  also have "... = (\<lambda>s' t'. if t' < t then signal_of2 False \<theta> s' t' else \<sigma> s')"
    unfolding `\<tau> = 0` signal_of2_empty by auto
  finally have w_def': "w = (\<lambda>s' t'. if t' < t then signal_of2 False \<theta> s' t' else \<sigma> s')"
    by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not> d \<le> t" hence "t < d" by auto
    have *: "\<forall>k>d. \<forall>s. w s k = w s d"
      using LeastI_ex exists_quiesce_worldline[OF assms(2)] unfolding d_def w_def by smt
    have "\<not> (\<forall>k > t. \<forall>s. w s k = w s t)"
      using not_less_Least `t < d` unfolding d_def  by blast
    hence "\<exists>k > t. \<exists>s. w s k \<noteq> w s t"
      by blast
    then obtain k s where "k > t" and "w s k \<noteq> w s t"
      by auto
    moreover have "w s k = w s t"
      unfolding w_def' using `k > t` by auto
    ultimately show False by auto
  qed
qed *)

definition
seq_hoare_valid :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ {(1_)}/ (_)/ {(1_)}" 50)
  where "\<Turnstile>\<^sub>t {P} s {Q} \<longleftrightarrow>  (\<forall>\<sigma> \<tau> \<gamma> \<theta> \<tau>' w w'.  context_invariant t \<sigma> \<gamma> \<theta> \<tau>
                                            \<and>  w = worldline_raw t \<sigma> \<theta> \<tau>
                                            \<and>  P w
                                            \<and> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>> \<longrightarrow>\<^sub>s \<tau>')
                                            \<and>  w' = worldline_raw t \<sigma> \<theta> \<tau>' \<longrightarrow> Q w')"

text \<open>The definition @{term "seq_hoare_valid"} shall be the basis to define the soundness of the
Hoare logic rules. Note that the symbol of `\<Turnstile>` has @{term "t"} as its subscript which indicates
that the validity is a function of time. Here is the diagram explaining the definition of the
validity:
\<close>

(*
         P w             \<longrightarrow>               Q w
          \<up>                                 \<up>
 w = worldline t \<sigma> \<theta> \<tau>          w' = worldline t \<sigma> \<theta> \<tau>'
          \<up>                                 \<up>
          \<tau>              \<longrightarrow>\<^sub>c               \<tau>'
*)


subsection \<open>Soundness\<close>

lemma Bcomp_hoare_valid:
  assumes "\<Turnstile>\<^sub>t {P} s1 {Q}" and "\<Turnstile>\<^sub>t {Q} s2 {R}"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile>\<^sub>t {P} Bcomp s1 s2 {R}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a trans_raw"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline"
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> w = worldline_raw t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> \<tau>'"
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and "w = worldline_raw t \<sigma> \<theta> \<tau>" and "P w"
    and "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' " and 2: "w' = worldline_raw t \<sigma> \<theta> \<tau>'"
    by auto
  then obtain \<tau>'' where 0: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and 1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  define w'' where "w'' = worldline_raw t \<sigma> \<theta> \<tau>''"
  hence "Q w''"
    using `\<Turnstile>\<^sub>t {P} s1 {Q}` unfolding seq_hoare_valid_def
    using \<open>P w\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> \<open>w = worldline_raw t \<sigma> \<theta> \<tau>\<close>
    by blast
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 0] assms(3)
    by auto
  thus "R w'"
    using `\<Turnstile>\<^sub>t {Q} s2 {R}` `w'' = worldline_raw t \<sigma> \<theta> \<tau>''` `Q w''` 1 2 unfolding seq_hoare_valid_def
    by auto
qed

lemma Bnull_sound:
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bnull {Q}"
  by (auto dest!: BnullE' simp add: seq_hoare_valid_def)

lemma state_of_world:
  assumes "w = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  shows "state_of_world w t = \<sigma>"
proof
  fix x
  have "signal_of (\<sigma> x) \<tau> x t = \<sigma> x"
  proof -
    have True: "(to_trans_raw_sig \<tau> x) t = 0"
      using assms(2) by (auto simp add: to_trans_raw_sig_def zero_fun_def)
    hence "\<forall>k \<in> dom ((to_trans_raw_sig \<tau> x)). t \<le> k"
      using assms(2) unfolding to_trans_raw_sig_def
      by (metis domIff linear zero_option_def)
    moreover have "t \<notin> dom ( (to_trans_raw_sig \<tau> x))"
      using True  by (simp add: domIff zero_option_def)
    ultimately have "\<forall>k \<in> dom ( (to_trans_raw_sig \<tau> x)). t < k"
      using nat_less_le by auto
    hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) x t = None"
      by (auto simp add: inf_time_none_iff)
    thus "signal_of (\<sigma> x) \<tau> x t = \<sigma> x"
      unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
  qed
  thus "state_of_world w t x = \<sigma> x"
    unfolding state_of_world_def assms worldline_raw_def by auto
qed

lemma beval_beh_of_world:
  assumes "w = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "beval_raw t \<sigma> \<gamma> (beh_of_world_raw w t) exp = beval_raw t \<sigma> \<gamma> \<theta> exp"
  using assms
proof (induction exp)
  case (Bsig_delayed sig n)
  have "t , \<sigma> , \<gamma> , beh_of_world_raw w t \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b signal_of False (beh_of_world_raw w t) sig (t - n)"
    by auto
  have *: "beval_raw t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = signal_of False \<theta> sig (t - n)"
    by auto
  have "0 < n \<and> 0 < t \<or> (t \<noteq> 0 \<and> n = 0) \<or> t = 0"
    by auto
  moreover
  { assume "0 < n \<and> 0 < t"
    hence " (beh_of_world_raw w t) (t - n) = Some \<circ> (\<lambda>s. w s (t - n))"
      unfolding beh_of_world_raw_def comp_def by auto
    hence "signal_of False (beh_of_world_raw w t) sig (t - n) = w sig (t - n)"
      by (auto dest!:trans_some_signal_of)
    also have "... = signal_of False \<theta> sig (t - n)"
      using `0 < n \<and> 0 < t` unfolding assms worldline_raw_def by auto
    also have "... = beval_raw t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n)"
      using * by auto
    finally have "signal_of False (beh_of_world_raw w t) sig (t - n) = beval_raw t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n)"
      by auto
    hence ?case by auto }

  moreover
  { assume "t \<noteq> 0 \<and> n = 0 \<or> t = 0"
    moreover
    { assume "t = 0"
      hence "t - n = 0" by auto
      have "beh_of_world_raw w t = 0" unfolding `t = 0` 
        by (auto simp add: beh_of_world_raw_def zero_fun_def zero_option_def)
      hence "signal_of False (beh_of_world_raw w t) sig (t - n) = signal_of False 0 sig 0"
        unfolding `t - n = 0` by auto
      also have "... = False"
        using signal_of_empty[of "False" "sig" "0"] by auto
      finally have "signal_of False (beh_of_world_raw w t) sig (t - n) = False"
        by auto
      have "\<theta> = 0"
        using assms(2) unfolding `t = 0` by (auto simp add: zero_fun_def)
      hence "beval_raw t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = signal_of False \<theta> sig 0"
        using `t - n = 0` by auto
      also have "... = False"
        unfolding `\<theta> = 0` using signal_of_empty[of "False"] by metis
      finally have "beval_raw t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = False"
        by auto
      hence ?case
        using `signal_of False (beh_of_world_raw w t) sig (t - n) = False` by auto }
    moreover
    { assume "t \<noteq> 0 \<and> n = 0"
      have " \<theta> t = 0"
        using assms(2) by auto
      have " (beh_of_world_raw w t) t = 0"
        unfolding beh_of_world_raw_def
        by (metis (full_types) less_not_refl map_add_subsumed1 map_add_subsumed2 map_le_def
        zero_fun_def zero_option_def)
      have *: " (beh_of_world_raw w t) (t - 1) = Some o (\<lambda>s. w s (t - 1))"
        using `t \<noteq> 0 \<and> n = 0` unfolding beh_of_world_raw_def by auto
      have "signal_of False (beh_of_world_raw w t) sig (t - n) = signal_of False (beh_of_world_raw w t) sig t"
        using `t \<noteq> 0 \<and> n = 0` by auto
      also have "... = signal_of False (beh_of_world_raw w t) sig (t - 1)"
        using signal_of_less[where \<tau>="beh_of_world_raw w t", OF `(beh_of_world_raw w t) t = 0`] 
        by metis
      also have "... = w sig (t - 1)"
        using * by(auto dest!: trans_some_signal_of)
      also have "... = signal_of False \<theta> sig (t - 1)"
        using `t \<noteq> 0 \<and> n = 0` unfolding assms(1) worldline_raw_def by auto
      also have "... = signal_of False \<theta> sig t"
        using signal_of_less[where \<tau>="\<theta>", OF ` \<theta> t = 0`] by metis
      also have "... = signal_of False \<theta> sig (t - n)"
        using `t \<noteq> 0 \<and> n = 0` by auto
      finally have "signal_of False (beh_of_world_raw w t) sig (t - n) = signal_of False \<theta> sig (t - n)"
        by auto
      hence ?case
        by auto }
    ultimately have ?case by auto }
  ultimately show ?case by auto
qed (auto)

text \<open>Note that the definition of @{term "\<gamma>"} below will only be preserved by VHDL code which does
not contain a zero time signal assignment. That is, in every assignment statement, be it of transport
or inertial type, must have nonzero delay. Check @{thm "context_invariant"} and note the assumption
@{term "t < next_time t \<tau>'"}.\<close>

lemma beval_beval_world_raw:
  assumes "w = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes gam: "\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
  assumes beh: "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw w t exp"
proof -
  have "state_of_world w t = \<sigma>"
    using state_of_world[OF assms(1) assms(2)] by auto
  moreover have "event_of_world w t = \<gamma>"
  proof (cases "0 < t")
    case True
    fix s
    have "w s t = \<sigma> s"
      using `state_of_world w t = \<sigma>` unfolding state_of_world_def by auto
    moreover have "w s (t - 1) = signal_of False \<theta> s (t - 1)"
      unfolding assms(1) worldline_raw_def using True by auto
    ultimately show ?thesis
      unfolding event_of_world_def assms(3)
      by (smt Collect_cong \<open>state_of_world w t = \<sigma>\<close> assms(1) True diff_less less_numeral_extra(3)
          state_of_world_def worldline_raw_def zero_less_one)
  next
    case False
    hence "t = 0" by auto
    hence ev: "event_of_world w t = {s. w s 0 \<noteq> False}"
      unfolding event_of_world_def by auto
    have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s 0}"
      using `t = 0` gam by auto
    have "\<theta> = 0"
      using beh unfolding `t = 0` by (auto simp add: zero_fun_def)
    hence "\<And>s. signal_of False \<theta> s 0 = False"
      using signal_of_empty by metis
    hence "\<gamma> = {s. \<sigma> s \<noteq> False}"
      using \<gamma>_def' by auto
    moreover have "\<And>s.  w s 0 = \<sigma> s"
      using `state_of_world w t = \<sigma>` `t = 0` unfolding state_of_world_def by auto
    ultimately  have "\<gamma> = {s. w s 0 \<noteq> False}"
      by auto
    thus ?thesis  using ev by auto
  qed
  ultimately have " beval_raw t (state_of_world w t) (event_of_world w t) (beh_of_world_raw w t) exp =
                    beval_raw t \<sigma> \<gamma> (beh_of_world_raw w t) exp" by auto
  also have "... = beval_raw t \<sigma> \<gamma> \<theta> exp"
    using beval_beh_of_world[OF assms(1) beh] by auto
  finally show ?thesis
    unfolding beval_world_raw_def by auto
qed

lemma beval_beval_world_raw_ci:
  assumes "w = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau> "
  shows "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw w t exp"
proof -
  have 0: "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0" and
       1: "\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}" and
       3: "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  show ?thesis
    using beval_beval_world_raw[OF assms(1) 0 1 3] by auto
qed

lemma Bguarded_hoare_valid:
  assumes "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> beval_world_raw a t g} s1 {Q}" and "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> \<not> beval_world_raw a t g} s2 {Q}"
  shows "\<Turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a trans_raw"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline"
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> w = worldline_raw t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> \<tau>'"
  hence s: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and w: "w = worldline_raw t \<sigma> \<theta> \<tau>"
    and c: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and p: "P w" and w': "w' = worldline_raw t \<sigma> \<theta> \<tau>'"
    by auto
  have "beval_raw t \<sigma> \<gamma> \<theta> g \<or> \<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    by auto
  moreover
  { assume "beval_raw t \<sigma> \<gamma> \<theta> g "
    hence \<tau>'_def: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s by auto
    have "beval_world_raw w t g"
      using `beval_raw t \<sigma> \<gamma> \<theta> g` beval_beval_world_raw[OF w] c unfolding context_invariant_def
      by auto
    with `P w` have " Q w'"
      using assms(1) c w \<tau>'_def w' unfolding seq_hoare_valid_def by auto }
  moreover
  { assume "\<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    hence \<tau>'_def: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s by auto
    have "\<not> beval_world_raw w t g"
      using `\<not> beval_raw t \<sigma> \<gamma> \<theta> g` beval_beval_world_raw[OF w] c unfolding context_invariant_def
      by auto
    with `P w` have "Q w'"
      using assms(2) c w \<tau>'_def w' unfolding seq_hoare_valid_def by auto }
  ultimately show "Q w'" by auto
qed

lemma lift_trans_post_worldline_upd:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes \<tau>'_def: "\<tau>' = trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) \<tau> t dly"
  assumes "\<forall>i < t. \<tau> i = 0"
  assumes "0 < dly"
  shows "worldline_raw t \<sigma> \<theta> \<tau>' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp]"
proof (rule ext, rule ext)
  fix s' t'
  have "t' < t \<or> t' \<ge> t" by auto
  moreover
  { assume "t' < t"
    hence 0: " worldline_raw t \<sigma> \<theta> \<tau>' s' t' =  signal_of False \<theta> s' t'"
      unfolding worldline_raw_def by auto
    have "t' < t + dly"
      using `t' < t` by auto
    hence "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
      unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
    also have "... = signal_of False \<theta> s' t'"
      using `t' < t` unfolding worldline_raw_def by auto
    finally have "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = signal_of False \<theta> s' t'"
      by auto
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t'"
      using 0 by auto }
  moreover
  { assume "t' \<ge> t"
    hence 0: "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
      unfolding worldline_raw_def by auto
    have "t' < t + dly \<or> t' \<ge> t + dly"
      by auto
    moreover
    { assume "t' < t + dly"
      have "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
        using `t' < t + dly` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
      also have "... = signal_of (\<sigma> s') \<tau> s' t'"
        using `t' \<ge> t` unfolding worldline_raw_def by auto
      finally have 1: "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = signal_of (\<sigma> s') \<tau> s' t'"
        by auto
      have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        using `t' \<ge> t` unfolding worldline_raw_def by auto
      also have "... = signal_of (\<sigma> s') \<tau> s' t'"
        using signal_of_trans_post2[OF `t' < t + dly`] unfolding \<tau>'_def by metis
      also have "... = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t'"
        using 1 by auto
      finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t'"
        by auto }
    moreover
    { assume "t' \<ge> t + dly"
      have "s' = sig \<or> s' \<noteq> sig" by auto
      moreover
      { assume "s' = sig"
        hence 2: "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
          using `t' \<ge> t + dly` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
        have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        also have "... = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
          using signal_of_trans_post3[OF `t + dly \<le> t'`, of _ "\<sigma> s'" "sig"] unfolding \<tau>'_def
          `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>`  using \<open>s' = sig\<close> assms(3-4) by blast
        finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' "
          using 2 by auto }
      moreover
      { assume "s' \<noteq> sig"
        hence "sig \<noteq> s'" by auto
        hence "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
          unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_upd_def  by auto
        also have "... = signal_of (\<sigma> s') \<tau> s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        finally have 3: "\<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' = signal_of (\<sigma> s') \<tau> s' t'"
          by auto
        have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        also have "... = signal_of (\<sigma> s') \<tau> s' t'"
          unfolding \<tau>'_def using signal_of_trans_post[OF `sig \<noteq> s'`] by metis
        also have "... = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t'"
          using 3 by auto
        finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' "
          by auto }
      ultimately have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' "
        by auto }
    ultimately have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t' "
      by auto }
  ultimately show "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t + dly := beval_world_raw \<omega> t exp] s' t'"
    by auto
qed

lemma Bassign_trans_sound:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly := beval_world_raw w t exp])"
    by (auto dest!: BassignE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a trans_raw"
    fix w w' :: "'a worldline"
    fix \<gamma>
    assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    hence "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
      unfolding context_invariant_def by auto
    assume "w = worldline_raw t \<sigma> \<theta> \<tau>"
    assume "P w"
    assume "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
      by auto
    moreover have "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw w t exp"
      using `w = worldline_raw t \<sigma> \<theta> \<tau>` \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> beval_beval_world_raw_ci by blast
    ultimately have \<tau>'_def: "\<tau>' = trans_post_raw sig (beval_world_raw w t exp) (\<sigma> sig) \<tau> t dly"
      by auto
    have "worldline_raw t \<sigma> \<theta> \<tau>' = w[sig, t + dly := beval_world_raw w t exp]"
      using \<open>w = worldline_raw t \<sigma> \<theta> \<tau>\<close> \<tau>'_def lift_trans_post_worldline_upd `\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0` `0 < dly`
      by (metis less_imp_le_nat)
    with imp and `P w` have "Q(w[sig, t + dly := beval_world_raw w t exp])"
      by auto
    assume "w' = worldline_raw t \<sigma> \<theta> \<tau>'"
    hence "Q w'"
      using `Q(w[sig, t + dly := beval_world_raw w t exp])` `worldline_raw t \<sigma> \<theta> \<tau>' = w[sig, t + dly := beval_world_raw w t exp]`
      by auto }
  thus " \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
    unfolding seq_hoare_valid_def by auto
qed

lemma lift_inr_post_worldline_upd:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "0 < dly"
  shows "worldline_raw t \<sigma> \<theta> \<tau>' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp]"
proof (rule ext, rule ext)
  fix s' t'
  have "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    using assms(3) by auto
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw \<omega> t exp"
    using `\<omega> = worldline_raw t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (transfer', simp add: beval_beval_world_raw_ci)
  hence \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) \<tau> t dly"
    by (simp add: calculation)
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_seq_exec_preserves_context_invariant[OF assms(2-3)] `0 < dly` by auto

  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  have "s' \<noteq> sig \<or> t' < t \<or> s' = sig \<and> t \<le> t'"
    by auto
  moreover
  { assume "s' \<noteq> sig \<or> t' < t"
    moreover
    { assume "t' < t"
      hence 0: " worldline_raw t \<sigma> \<theta> \<tau>' s' t' =  signal_of False \<theta> s' t'"
        unfolding worldline_raw_def by auto
      have "t' < t + dly"
        using `t' < t` by auto
      hence "\<omega>[sig, t,  dly := beval_world_raw \<omega> t exp] s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
        unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_inert_upd_def  by (simp add: \<open>t' < t\<close>)
      also have "... = signal_of False \<theta> s' t'"
        using `t' < t` unfolding worldline_raw_def by auto
      finally have "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = signal_of False \<theta> s' t'"
        by auto
      hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t'"
        using 0 by auto }
    moreover
    { assume "s' \<noteq> sig"
      hence "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
        unfolding worldline_inert_upd_def `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` by auto
      also have "... = worldline_raw t \<sigma> \<theta> \<tau>' s' t'"
      proof -
        have "\<And>n. (to_trans_raw_sig \<tau> s') n = (to_trans_raw_sig \<tau>' s') n"
          using `s' \<noteq> sig` unfolding \<tau>'_def inr_post_raw_def 
        proof -
          fix n :: nat
          have f1: "\<And>a aa b ba f n na nb. (a::'a) = aa \<or> trans_post_raw a b ba f n na nb aa = f nb aa"
            by (metis (no_types) to_trans_raw_sig_def trans_post_raw_diff_sig)
          then have "(if True then trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) \<tau> t dly else trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly) n s' = \<tau> n s'"
            by (metis \<open>s' \<noteq> sig\<close>)
          moreover
          { assume "\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
            then have "purge_raw \<tau> t dly sig n s' = \<tau> n s' \<and> sig \<noteq> s' \<and> \<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
              by (metis \<open>s' \<noteq> sig\<close> purge_raw_does_not_affect_other_sig)
            then have "(if is_stable_raw dly \<tau> t sig (\<sigma> sig) then trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) \<tau> t dly else trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly) n s' = \<tau> n s'"
              using f1 by fastforce }
          ultimately show "to_trans_raw_sig \<tau> s' n = to_trans_raw_sig (if is_stable_raw dly \<tau> t sig (\<sigma> sig) then trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) \<tau> t dly else trans_post_raw sig (beval_world_raw \<omega> t exp) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly) s' n"
            by (simp add: to_trans_raw_sig_def)
        qed
        hence "signal_of (\<sigma> s') \<tau> s' t' = signal_of (\<sigma> s') \<tau>'  s' t'"
          by (meson signal_of_equal_when_trans_sig_equal_upto)
        thus ?thesis
          unfolding worldline_raw_def by auto
      qed
      finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t'"
        by auto }
    ultimately have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t'"
      by auto }
  moreover
  { assume "s' = sig \<and> t \<le> t'"
    hence "t + dly \<le> t' \<or> t' < t + dly" and "s' = sig" and "t \<le> t'"
      by auto
    moreover
    { assume "t + dly \<le> t'"
      hence 2: "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
          using `s' = sig` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_inert_upd_def by auto
      have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        using `t' \<ge> t` unfolding worldline_raw_def by auto
      also have "... = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
        using signal_of_inr_post[OF `t + dly \<le> t'`, of _ "\<sigma> s'" "sig"] unfolding \<tau>'_def
        `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>`  using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>s' = sig \<and> t \<le> t'\<close> `0 < dly`
        by simp
      finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
        using 2 by auto }
    moreover
    { assume "t' < t + dly"
      hence "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = \<omega> sig t"
        unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close> by auto
      also have "... = signal_of (\<sigma> sig) \<tau> sig t"
        unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_raw_def by auto
      also have "... = \<sigma> sig"
      proof -
        have True: "\<tau> t sig = None"
          using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0` by (auto simp add: zero_fun_def zero_option_def)
        have "\<And>k. k \<in>dom ((to_trans_raw_sig \<tau> sig)) \<Longrightarrow> t < k"
        proof (rule ccontr)
          fix k
          assume in_dom: "k \<in>dom ((to_trans_raw_sig \<tau> sig))"
          assume "\<not> t < k" hence "k \<le> t" by auto
          hence "\<tau> k sig = None"
            using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0` True  by (metis dual_order.antisym leI zero_fun_def zero_option_def)
          hence "k \<notin> dom ((to_trans_raw_sig \<tau> sig))"
            unfolding to_trans_raw_sig_def by auto
          with in_dom show "False" by auto
        qed
        hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) sig t = None"
          by (meson inf_time_none_iff)
        then show ?thesis
          unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
      qed
      finally have l: "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = \<sigma> sig"
        by auto
      have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        unfolding worldline_raw_def using `s' = sig \<and> t \<le> t'` by auto
      also have "... = \<sigma> s'"
        using signal_of_inr_post2[OF `t \<le> t'` `t' < t + dly` `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`, of "id"]
        unfolding \<tau>'_def using `s' = sig` by auto
      finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<sigma> s'"
        by auto
      with l have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
        using `s' = sig` by auto }
    ultimately have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
      by auto }
  ultimately show "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
    by auto
qed

lemma Bassign_inert_sound:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t, dly := beval_world_raw w t exp])"
    by (auto dest!: Bassign_inertE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a trans_raw"
    fix w w' :: "'a worldline"
    fix \<gamma>
    assume c: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    assume "w = worldline_raw t \<sigma> \<theta> \<tau>"
    assume "P w"
    assume ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    have "worldline_raw t \<sigma> \<theta> \<tau>' = w[sig, t, dly := beval_world_raw w t exp]"
      using lift_inr_post_worldline_upd[OF `w = worldline_raw t \<sigma> \<theta> \<tau>` c ex assms] by auto
    with imp and `P w` have "Q(w[sig, t, dly := beval_world_raw w t exp])"
      by auto
    assume "w' = worldline_raw t \<sigma> \<theta> \<tau>'"
    hence "Q w'"
      using `Q(w[sig, t, dly := beval_world_raw w t exp])` `worldline_raw t \<sigma> \<theta> \<tau>' = w[sig, t, dly:= beval_world_raw w t exp]`
      by auto }
  thus " \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
    unfolding seq_hoare_valid_def by auto
qed

lemma soundness:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "nonneg_delay s"
  shows "\<Turnstile>\<^sub>t {P} s {R}"
  using assms
proof (induction rule:seq_hoare.induct)
  case (AssignI t P sig dly exp)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound[OF `0 < dly`]  using seq_hoare.AssignI by fastforce
next
  case (Conseq P' P t s Q Q')
  then show ?case  by (auto simp add: seq_hoare_valid_def)
qed (auto simp add: Bnull_sound Bassign_trans_sound Bcomp_hoare_valid Bguarded_hoare_valid)

end