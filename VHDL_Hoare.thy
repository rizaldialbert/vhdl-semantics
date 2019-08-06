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
  "worldline_inert_upd w s t dly v = 
    (\<lambda>s' t'. let
                time = if w s t = v \<or> w s (t + dly) \<noteq> v then t + dly else GREATEST n. n \<le> t + dly \<and> (w s (n - 1) = (\<not> v)) \<and> w s n = v 
             in 
                if s' \<noteq> s \<or> t' < t then w s' t' else if t' < time then w s' t  else v)"

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

text \<open>non-stuttering\<close>

definition non_stuttering :: "'signal trans_raw_sig \<Rightarrow> 'signal state \<Rightarrow> 'signal \<Rightarrow> bool" where
  "non_stuttering \<tau> \<sigma> s \<equiv> (\<forall>k1 k2. k1 < k2 \<and> k1 \<in> keys (\<tau> s) \<and> k2 \<in> keys (\<tau> s) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (\<tau> s)) \<longrightarrow> \<tau> s k1 \<noteq> \<tau> s k2)
                         \<and> (keys (\<tau> s) \<noteq> {} \<longrightarrow> \<sigma> s \<noteq> the (\<tau> s (LEAST k. k \<in> keys (\<tau> s))))"

lemma two_successive_keys_diff_value:
  fixes \<tau> :: "'a trans_raw_sig"
  assumes "non_stuttering \<tau> \<sigma> s"
  assumes "t1 \<in> keys (\<tau> s)" and "t2 \<in> keys (\<tau> s)"
  defines "v1 \<equiv> the (\<tau> s t1)"
  defines "v2 \<equiv> the (\<tau> s t2)"
  assumes "\<forall>n>t1. n < t2 \<longrightarrow> \<tau> s n = 0"
  assumes "t1 < t2"
  shows "v1 \<noteq> v2"
proof -
  have "\<forall>k. t1 < k \<and> k < t2 \<longrightarrow> k \<notin> keys (\<tau> s)"
    using `\<forall>n>t1. n < t2 \<longrightarrow> \<tau> s n = 0`  by (simp add: keys_def)
  with assms(1-3) show ?thesis
    using `t1 < t2` unfolding v1_def v2_def non_stuttering_def 
  proof -
    assume a1: "(\<forall>k1 k2. k1 < k2 \<and> k1 \<in> Femto_VHDL_raw.keys (\<tau> s) \<and> k2 \<in> Femto_VHDL_raw.keys (\<tau> s) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> Femto_VHDL_raw.keys (\<tau> s)) \<longrightarrow> \<tau> s k1 \<noteq> \<tau> s k2) \<and> (Femto_VHDL_raw.keys (\<tau> s) \<noteq> {} \<longrightarrow> \<sigma> s \<noteq> the (\<tau> s (LEAST k. k \<in> Femto_VHDL_raw.keys (\<tau> s))))"
    have f2: "\<And>f. Femto_VHDL_raw.keys f = {n. f (n::nat) \<noteq> (None::bool option)}"
      by (simp add: keys_def zero_option_def)
    then have f3: "t2 \<in> {n. \<tau> s n \<noteq> None}"
      using \<open>t2 \<in> Femto_VHDL_raw.keys (\<tau> s)\<close> by presburger
    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
        f4: "\<And>n na. t1 \<in> Femto_VHDL_raw.keys (\<tau> s) \<and> nn n na \<in> Femto_VHDL_raw.keys (\<tau> s) \<and> (\<not> n < na \<or> n \<notin> Femto_VHDL_raw.keys (\<tau> s) \<or> \<tau> s n \<noteq> \<tau> s na \<or> na \<notin> Femto_VHDL_raw.keys (\<tau> s) \<or> nn n na < na) \<and> (\<not> n < na \<or> n \<notin> Femto_VHDL_raw.keys (\<tau> s) \<or> \<tau> s n \<noteq> \<tau> s na \<or> na \<notin> Femto_VHDL_raw.keys (\<tau> s) \<or> n < nn n na)"
        using a1 \<open>t1 \<in> Femto_VHDL_raw.keys (\<tau> s)\<close> by moura
    then have f5: "t1 \<in> {n. \<tau> s n \<noteq> None}"
      using f2 by metis
    have "\<tau> s t2 \<noteq> \<tau> s t1"
      using f4 f3 f2 by (metis \<open>\<forall>k. t1 < k \<and> k < t2 \<longrightarrow> k \<notin> Femto_VHDL_raw.keys (\<tau> s)\<close> \<open>t1 < t2\<close>)
    then show "the (\<tau> s t1) \<noteq> the (\<tau> s t2)"
      using f5 f3 by force
  qed
qed

lemma derivative_raw_of_worldline_specific:
  fixes \<sigma> :: "'a state"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows "derivative_raw w t = \<tau>"
proof (rule ext)
  fix k
  have "\<tau> t = 0"
    using assms(1) by auto
  have "k \<le> t \<or> t < k" by auto
  moreover
  { assume "k \<le> t"
    hence "(derivative_raw w t) k = 0"
      by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
    also have "... = \<tau> k"
      using assms(1) `k \<le> t` by auto
    finally have "derivative_raw w t k = \<tau> k"
      by auto }
  moreover
  { assume "t < k"
    hence "derivative_raw w t k = difference_raw w k"
      unfolding derivative_raw_def by auto
    also have "... = \<tau> k"
    proof (rule ext)
      fix s
      have "w s k \<noteq> w s (k - 1) \<or> w s k = w s (k - 1)"
        by auto
      moreover
      { assume "w s k \<noteq> w s (k - 1)"
        hence "signal_of (\<sigma> s) \<tau> s k \<noteq> signal_of (\<sigma> s) \<tau> s (k - 1)"
          unfolding w_def worldline_raw_def using `t < k` by auto
        have lnone: " (to_trans_raw_sig \<tau> s) k \<noteq> 0"
        proof (rule ccontr)
          assume "\<not>  (to_trans_raw_sig \<tau> s) k \<noteq> 0"
          hence " (to_trans_raw_sig \<tau> s) k = 0"
            by auto
          hence " \<tau> k s = 0"
             unfolding to_trans_raw_sig_def by auto
          hence "signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau> s (k - 1)"
            by (intro signal_of_less_sig)
          with `signal_of (\<sigma> s) \<tau> s k \<noteq> signal_of (\<sigma> s) \<tau> s (k - 1)` show False
            by auto
        qed
        then obtain val where "to_trans_raw_sig \<tau> s k = Some val"
          by (metis not_None_eq zero_fun_def zero_fun_def zero_option_def)
        hence "\<tau> k s = Some val"
          by (auto simp add: to_trans_raw_sig_def)
        hence inf: "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s k = Some k"
          by (auto intro!: some_inf_time'[where \<sigma>="(\<lambda>x. False)(s := val)"])
        have "difference_raw w k s = Some (w s k)"
          unfolding difference_raw_def using `w s k \<noteq> w s (k - 1)` using \<open>t < k\<close> by auto
        also have "... =  (to_trans_raw_sig \<tau> s) k"
          unfolding w_def worldline_raw_def using `t < k` unfolding Femto_VHDL_raw.to_signal_def 
          comp_def using inf \<open> (to_trans_raw_sig \<tau> s) k = Some val\<close> by auto
        also have "... = \<tau> k s"
          by (auto simp add: to_trans_raw_sig_def)
        finally have "difference_raw w k s =  \<tau> k s"
          by auto }
      moreover
      { assume "w s k = w s (k - 1)"
        hence sig_same: "signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau> s (k - 1)"
          unfolding w_def worldline_raw_def using `t < k` by auto
        have lnone: " (to_trans_raw_sig \<tau> s) k = None"
        proof (rule ccontr)
          assume " (to_trans_raw_sig \<tau> s) k \<noteq> None"
          then obtain val where " (to_trans_raw_sig \<tau> s) k = Some val"
            by blast
          hence " \<tau> k s = Some val"
            by (auto simp add: to_trans_raw_sig_def)
          hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s k = Some k"
            by (auto intro!: some_inf_time'[where \<sigma>="(\<lambda>x. False)(s := val)"])
          hence "signal_of (\<sigma> s) \<tau> s k = val"
            unfolding Femto_VHDL_raw.to_signal_def comp_def by (simp add: \<open> (to_trans_raw_sig \<tau> s) k = Some val\<close>)
          with sig_same have "signal_of (\<sigma> s) \<tau> s (k - 1) = val"
            by auto
          from signal_of_elim[OF this]
          have "(\<exists>m\<le>k - 1.  (to_trans_raw_sig \<tau> s) m = Some val) \<or>
                (\<forall>m\<le>k - 1.  (to_trans_raw_sig \<tau> s) m = None \<and> val = \<sigma> s)" 
            by (metis to_trans_raw_sig_def)
          moreover
          { assume "(\<exists>m\<le>k - 1.  (to_trans_raw_sig \<tau> s) m = Some val)"
            then obtain m where "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s (k-1) = Some m" and " (to_trans_raw_sig \<tau> s) m = Some val"
              using `signal_of (\<sigma> s) \<tau> s (k - 1) = val` unfolding Femto_VHDL_raw.to_signal_def comp_def
              by (smt \<open>to_trans_raw_sig \<tau> s k = Some val\<close> \<open>to_trans_raw_sig \<tau> s k \<noteq> None\<close>
              inf_time_noneE2 inf_time_some_exists keys_def mem_Collect_eq option.case_eq_if
              option.collapse zero_option_def)
            have "m < k"
              using inf_time_at_most[OF `Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s (k-1) = Some m`]
              \<open>t < k\<close> by linarith
            moreover have "m \<in> keys (to_trans_raw_sig \<tau> s)"
              using `to_trans_raw_sig \<tau> s m = Some val` unfolding keys_def by (auto simp add: zero_option_def)
            moreover have "k \<in> keys (to_trans_raw_sig \<tau> s)"
              using `\<tau> k s = Some val` unfolding keys_def to_trans_raw_sig_def by (auto simp add: zero_option_def)
            moreover have "\<forall>n. m < n \<and> n < k \<longrightarrow> n \<notin> keys (to_trans_raw_sig \<tau> s)"
            proof (rule ccontr)
              assume "\<not> (\<forall>n. m < n \<and> n < k \<longrightarrow> n \<notin> keys (to_trans_raw_sig \<tau> s))"
              then obtain n where "m < n" and "n < k" and "n \<in> keys (to_trans_raw_sig \<tau> s)"
                by auto
              with inf_time_someE[OF `Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s (k-1) = Some m`]
              show False
                unfolding dom_is_keys  by auto
            qed
            ultimately have "to_trans_raw_sig \<tau> s m \<noteq> to_trans_raw_sig \<tau> s k"
              using assms(4) unfolding non_stuttering_def by metis
            hence "Some val \<noteq> Some val"
              using \<open>(to_trans_raw_sig \<tau> s) m = Some val\<close> \<open>\<tau> k s = Some val\<close> 
              unfolding to_trans_raw_sig_def by auto
            hence False by auto }
          moreover
          { assume "(\<forall>m\<le>k - 1.  (to_trans_raw_sig \<tau> s) m = None \<and> val = \<sigma> s)"
            hence must_zero: "\<And>m. m < k \<Longrightarrow>  (to_trans_raw_sig \<tau> s) m = 0" and "val = \<sigma> s"
              by (auto simp add: zero_option_def)
            have "(LEAST n. n \<in> keys (to_trans_raw_sig \<tau> s)) = k"
            proof (rule Least_equality)
              show "k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> s)"
                using `\<tau> k s = Some val` unfolding to_trans_raw_sig_def keys_def 
                by (auto simp add: zero_option_def)
            next
              { fix y
                assume "\<not> k \<le> y" hence "y < k" by auto
                with must_zero have "y \<notin> keys (to_trans_raw_sig \<tau> s)"
                  by (simp add: keys_def) }
              thus "\<And>y. y \<in> keys (to_trans_raw_sig \<tau> s) \<Longrightarrow> k \<le> y"
                by auto
            qed
            moreover have "keys (to_trans_raw_sig \<tau> s) \<noteq> {}"
              using `\<tau> k s = Some val` \<open>Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s k = Some k\<close>
              inf_time_some_exists by fastforce
            ultimately have "\<sigma> s \<noteq> val"
              using assms(4) `\<tau> k s = Some val` unfolding non_stuttering_def 
              by (simp add: \<open>to_trans_raw_sig \<tau> s k = Some val\<close>)
            hence False 
              using `val = \<sigma> s` by auto }
          ultimately show False by auto
        qed
        hence "difference_raw w k s = \<tau> k s"
          unfolding difference_raw_def using `w s k = w s (k - 1)` `t < k`
          by (auto simp add:to_trans_raw_sig_def) }
      ultimately show "difference_raw w k s = \<tau> k s"
        by auto
    qed
    finally have "derivative_raw w t k = \<tau> k"
      by auto }
  ultimately show " derivative_raw w t k = \<tau> k"
    by auto
qed

lemma current_sig_and_prev_same:
  assumes "signal_of def \<theta> s k = signal_of def \<theta> s (k - 1)"
  assumes "0 < k"
  assumes "non_stuttering (to_trans_raw_sig \<theta>) state s"
  assumes "state s = def"
  shows "\<theta> k s = 0"
proof (rule ccontr)
  assume "\<theta> k s \<noteq> 0"
  then obtain val where "\<theta> k s = Some val"
    by (metis not_None_eq zero_fun_def zero_fun_def zero_option_def)
  hence "signal_of def \<theta> s k = val"
    using trans_some_signal_of'[of "\<theta>" "k" "s" "def_state(s := val)" "def"] by auto
  have "the (to_trans_raw_sig \<theta> s k) = val"
    using `\<theta> k s = Some val` by (auto simp add: to_trans_raw_sig_def)
  have "k \<in> dom (to_trans_raw_sig \<theta> s)"
    using ` \<theta> k s = Some val` by ( auto simp add: to_trans_raw_sig_def)
  hence "k \<in> keys (to_trans_raw_sig \<theta> s)"
    by (auto simp add: keys_def to_trans_raw_sig_def zero_option_def)
  obtain k' where "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<theta>) s (k - 1) = None \<or> 
                   Femto_VHDL_raw.inf_time (to_trans_raw_sig \<theta>) s (k - 1) = Some k'"
    using option.exhaust_sel by blast
  moreover
  { assume inf_none: "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<theta>) s (k - 1) = None"
    hence noneE: "\<forall>t\<in>dom ( (to_trans_raw_sig \<theta> s)). (k - 1) < t"
      by (simp add: inf_time_none_iff)
    have *: "\<forall>n. n < k \<longrightarrow>  (to_trans_raw_sig \<theta> s) n = 0"
    proof (rule ccontr)
      assume "\<not> (\<forall>n. n < k \<longrightarrow>  (to_trans_raw_sig \<theta> s) n = 0)"
      then obtain n where "n < k" and " (to_trans_raw_sig \<theta> s) n \<noteq> 0"
        by auto
      hence "n \<in> dom ( (to_trans_raw_sig \<theta> s))"
        by (simp add: domIff zero_option_def)
      hence "k - 1 < n" using noneE by auto
      with `n < k` show False by auto
    qed
    have "signal_of def \<theta> s (k - 1) = def"
      using inf_none unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
    have "k \<in> keys (to_trans_raw_sig \<theta> s)"
      using ` \<theta> k s = Some val`   \<open>signal_of def \<theta> s (k - 1) = def\<close>
      \<open>signal_of def \<theta> s k = signal_of def \<theta> s (k - 1)\<close> inf_none inf_time_less
      some_inf_time' \<open>k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<theta> s)\<close> by blast
    hence "keys (to_trans_raw_sig \<theta> s) \<noteq> {}"
      by auto
    moreover have "(LEAST n. n \<in> keys (to_trans_raw_sig \<theta> s)) = k"
    proof (rule Least_equality)
      { fix y
        assume "\<not> k \<le> y" hence "y < k" by auto
        hence "y \<notin> keys (to_trans_raw_sig \<theta> s)"
          using * by (simp add: keys_def) }
      thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<theta> s) \<Longrightarrow> k \<le> y"
        by auto
    qed (simp add: `k \<in> keys (to_trans_raw_sig \<theta> s)`)
    ultimately have "state s \<noteq> the (\<theta> k s)"
      using assms(3) unfolding non_stuttering_def by (simp add: to_trans_raw_sig_def)
    hence "val \<noteq> def"
      using assms(3-4) by (simp add: \<open>\<theta> k s = Some val\<close>)
    hence "signal_of def \<theta> s k \<noteq> signal_of def \<theta> s (k - 1)"
      using `signal_of def \<theta> s k = val` `signal_of def \<theta> s (k - 1) = def`
      by auto
    with `signal_of def \<theta> s k = signal_of def \<theta> s (k - 1)` have "False" by auto }
  moreover
  { assume inf_some: "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<theta>) s (k - 1) = Some k'"
    have "\<forall>t\<in>dom ( (to_trans_raw_sig \<theta> s)). t \<le> k-1 \<longrightarrow> t \<le> k'"
      using inf_time_someE[OF inf_some] by auto
    hence "\<forall>n>k'. n < k \<longrightarrow>  (to_trans_raw_sig \<theta> s) n = None"
      by (metis diff_Suc_1 domIff le_add1 less_imp_Suc_add not_le)
    have "k' < k"
      using inf_time_at_most[OF inf_some] \<open>0 < k\<close> by linarith
    have "k' \<in> dom ( (to_trans_raw_sig \<theta> s))"
      by (metis (full_types) dom_def inf_some inf_time_some_exists keys_def zero_option_def)
    hence "k' \<in> keys (to_trans_raw_sig \<theta> s)"
      by (auto simp add: keys_def to_trans_raw_sig_def zero_option_def)
    obtain val' where " (to_trans_raw_sig \<theta> s) k' = Some val'"
      using `k' \<in> dom ( (to_trans_raw_sig \<theta> s))` by auto
    hence "the ( (to_trans_raw_sig \<theta> s) k') = val'"
      by ( auto simp add: to_trans_raw_sig_def)
    hence "val \<noteq> val'"
      using two_successive_keys_diff_value[OF `non_stuttering (to_trans_raw_sig \<theta>) state s`
      `k' \<in> keys (to_trans_raw_sig \<theta> s)` `k \<in> keys (to_trans_raw_sig \<theta> s)` _ `k' < k`]
      `\<forall>n>k'. n < k \<longrightarrow>  (to_trans_raw_sig \<theta> s) n = None` `the ( (to_trans_raw_sig \<theta> s) k) = val`
      unfolding zero_option_def by auto
    hence "signal_of def \<theta> s (k - 1) = val'"
      using inf_some `the ( (to_trans_raw_sig \<theta> s) k') = val'`
      unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
    with `signal_of def \<theta> s k = val` have "False"
      using `val \<noteq> val'` `signal_of def \<theta> s k = signal_of def \<theta> s (k - 1)` by auto }
  ultimately show False by auto
qed

text \<open>Here is an important result. In case that the history @{term "\<theta> :: 'a trans_raw"} is
non-stuttering, the derivative raw of the worldline @{term "w = worldline_raw t \<sigma> \<theta> \<tau>"} is exactly the
history @{term "\<theta>"}.\<close>

lemma derivative_is_history:
  fixes \<sigma> :: "'a state"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes *: "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def_state s"
  shows "derivative_hist_raw w t = \<theta>"
proof (rule ext)
  fix k
  have "k = 0 \<or> 0 < k \<and> k < t \<or> t < k \<or> t = k"
    by auto
  moreover
  { assume "t < k"
    hence "derivative_hist_raw w t k = Map.empty"
      by (auto simp add: derivative_hist_raw_def)
    also have "... = \<theta> k"
      using * `t < k` unfolding zero_fun_def zero_option_def by auto
    finally have "derivative_hist_raw w t k = \<theta> k"
      using `t < k` by auto }
  moreover
  { assume "0 < k \<and> k < t"
    hence "(derivative_hist_raw w t) k = difference_raw w k"
      by (auto simp add: derivative_hist_raw_def)
    also have "... = \<theta> k"
      unfolding difference_raw_def
    proof (rule ext)
      fix s
      have "non_stuttering (to_trans_raw_sig \<theta>) def_state s"
        using assms(4) by auto
      have "w s k = w s (k - 1) \<or> w s k \<noteq> w s (k - 1)"
        by auto
      moreover
      { assume "w s k = w s (k - 1)"
        have "signal_of False \<theta> s k = signal_of False \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `w s k = w s (k - 1)` unfolding w_def worldline_raw_def by auto
        have "\<theta> k s = 0"
          using current_sig_and_prev_same \<open>0 < k \<and> k < t\<close> \<open>non_stuttering (to_trans_raw_sig \<theta>)
          def_state s\<close> \<open>signal_of False \<theta> s k = signal_of False \<theta> s (k - 1)\<close> by fastforce
        hence "(if w s k \<noteq> w s (k - 1) then Some (w s k) else None) =  \<theta> k s"
          using `w s k = w s (k-1)` by (auto simp add: zero_option_def) }
      moreover
      { assume "w s k \<noteq> w s (k - 1)"
        have "signal_of False \<theta> s k \<noteq> signal_of False \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `w s k \<noteq> w s (k - 1)` unfolding w_def worldline_raw_def by auto
        hence "\<theta> k s \<noteq> 0"
          using signal_of_less_sig  by fastforce
        have "the (\<theta> k s) = signal_of False \<theta> s k "
          by (metis \<open>\<theta> k s \<noteq> 0\<close> \<open>non_stuttering (to_trans_raw_sig \<theta>) def_state s\<close> option.collapse
          trans_some_signal_of' zero_option_def)
        also have "... = w s k"
          unfolding w_def worldline_raw_def using `0 < k \<and> k < t` by auto
        finally have "(if w s k \<noteq> w s (k - 1) then Some (w s k) else None) =\<theta> k s"
          using `w s k \<noteq> w s (k - 1)` by (smt \<open>\<theta> k s \<noteq> 0\<close> option.collapse zero_option_def) }
      ultimately show "(if k = 0 then \<lambda>s. if w s k then Some True else None else (\<lambda>s. if w s k \<noteq> w s (k - 1) then Some (w s k) else None)) s = \<theta> k s"
        using `0 < k \<and> k < t` by auto
    qed
    finally have "derivative_hist_raw w t k = \<theta> k"
      using `0 < k \<and> k < t` by auto }
  moreover
  { assume "t = k"
    hence "\<theta> k = 0"
      using * by auto
    hence "derivative_hist_raw w t k = \<theta> k"
      using `t = k` by (auto simp add: derivative_hist_raw_def zero_fun_def zero_option_def) }
  moreover
  { assume "k = 0"
    have "t = 0 \<or> 0 < t" by auto
    moreover
    { assume "t = 0"
      hence " derivative_hist_raw w t k = \<theta> k"
        using * by (auto simp add: derivative_hist_raw_def zero_fun_def zero_option_def) }
    moreover
    { assume "0 < t"
      hence " derivative_hist_raw w t k = difference_raw w 0"
        unfolding `k = 0` by (auto simp add: derivative_hist_raw_def)
      also have "... = \<theta> 0"
      proof (rule ext)
        fix s
        have "non_stuttering (to_trans_raw_sig \<theta>) def_state s"
          using assms(4) by auto
        obtain val where " \<theta> 0 s = None \<or>  \<theta> 0 s = Some val"
          by (meson not_None_eq)
        moreover
        { assume "\<theta> 0 s = None"
          have "w s 0 = signal_of False \<theta> s 0"
            unfolding w_def worldline_raw_def using `0 < t` by auto
          also have "... = False"
            using ` \<theta> 0 s = None` signal_of_empty by (metis signal_of_zero zero_option_def)
          finally have "w s 0 = False"
            by auto
          hence "difference_raw w 0 s = None"
            unfolding difference_raw_def by auto
          also have "... =  \<theta> 0 s"
            using ` \<theta> 0 s = None` by auto
          finally have "difference_raw w 0 s =  \<theta> 0 s"
            by auto }
        moreover
        { assume " \<theta> 0 s = Some val"
          hence " (to_trans_raw_sig \<theta> s) 0 \<noteq> None"
            by (auto simp add: to_trans_raw_sig_def)
          have "0 \<in> keys (to_trans_raw_sig \<theta> s)"
            using ` \<theta> 0 s = Some val`
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          hence "keys (to_trans_raw_sig \<theta> s) \<noteq> {}"
            by auto
          hence "val = True"
            using `non_stuttering (to_trans_raw_sig \<theta>) def_state s` 
            unfolding non_stuttering_def  
            by (metis (full_types) Least_eq_0 \<open>0 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<theta> s)\<close> \<open>\<theta> 0
            s = Some val\<close> option.sel to_trans_raw_sig_def)
          hence "w s 0 = signal_of False \<theta> s 0"
            unfolding w_def worldline_raw_def using `0 < t` by auto
          also have "... = True"
            using ` \<theta> 0 s = Some val` unfolding `val = True`  
            by (meson trans_some_signal_of')
          finally have "w s 0 = True"
            by auto
          hence "difference_raw w 0 s = Some True"
            unfolding difference_raw_def by auto
          also have "... =  \<theta> 0 s"
            using ` \<theta> 0 s = Some val` unfolding `val = True` by auto
          finally have "difference_raw w 0 s =  \<theta> 0 s"
            by auto }
        ultimately show "difference_raw w 0 s = \<theta> 0 s"
          by auto
      qed
      finally have "(derivative_hist_raw w t) k = \<theta> k"
        unfolding `k = 0` by auto }
    ultimately have "(derivative_hist_raw w t) k = \<theta> k"
      by auto }
  ultimately show "(derivative_hist_raw w t) k = \<theta> k"
    by auto
qed

text \<open>Similar to @{thm "derivative_is_history"}, the derivative of a worldline constructed by the
constructor @{term "worldline t \<sigma> \<theta> \<tau>"} is exactly the transaction @{term "\<tau>"} provided that the
transaction @{term "\<tau>"} is non-stuttering with respect to the initial state @{term "\<sigma> :: 'a
state"}.\<close>

lemma derivative_raw_of_worldline:
  fixes \<sigma> :: "'a state"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows "derivative_raw w t = \<tau>"
proof (cases "\<tau> = 0", rule_tac[!] ext)
  case True
  fix n
  have "n \<le> t \<or> t < n" by auto
  moreover
  { assume "n \<le> t"
    hence "derivative_raw w t n = \<tau> n"
      unfolding derivative_raw_def using True by (auto simp add: zero_fun_def zero_option_def) }
  moreover
  { assume "t < n"
    hence "derivative_raw w t n = difference_raw w n"
      unfolding derivative_raw_def by auto
    { fix s
      have "worldline_raw t \<sigma> \<theta> \<tau> s n = signal_of (\<sigma> s) \<tau> s n"
        unfolding worldline_raw_def using `t < n` by auto
      also have "... = \<sigma> s"
        unfolding True by (rule signal_of_empty)    
      finally have "worldline_raw t \<sigma> \<theta> \<tau> s n = \<sigma> s"
        by auto }
    hence *: "\<And>s. worldline_raw t \<sigma> \<theta> \<tau> s n = \<sigma> s"
      by auto
    { fix s
      have "worldline_raw t \<sigma> \<theta> \<tau> s (n-1) = signal_of (\<sigma> s) \<tau> s (n-1)"
        unfolding worldline_raw_def using `t < n` by auto
      also have "... = \<sigma> s"
        unfolding True by (rule signal_of_empty)    
      finally have "worldline_raw t \<sigma> \<theta> \<tau> s (n-1) = \<sigma> s"
        by auto }
    hence "\<And>s. worldline_raw t \<sigma> \<theta> \<tau> s (n-1) = \<sigma> s"
      by auto
    with * have "\<And>s. w s n = w s (n-1)"
      unfolding w_def by auto
    hence "difference_raw w n = Map.empty"
      using `t < n` unfolding difference_raw_def by auto
    also have "... = \<tau> n"
      using True by (auto simp add: zero_fun_def zero_option_def)
    finally have "derivative_raw w t n = \<tau> n"
      using `derivative_raw w t n = difference_raw w n` by auto }
  ultimately show "derivative_raw w t n = \<tau> n"
    by auto
next
  case False
  fix x
  from derivative_raw_of_worldline_specific[OF assms(1-2) assms(4)]  show "derivative_raw w t x = \<tau> x "
    using assms(3) nat_less_le by auto
qed

lemma preempted_keys_subset_of:
  fixes dly t :: nat 
  fixes sig :: "'signal"
  fixes \<tau> :: "'signal trans_raw"
  defines "\<tau>' \<equiv> preempt_raw sig \<tau> (t + dly)"
  shows "k \<in> keys (to_trans_raw_sig \<tau>' sig) \<Longrightarrow> k \<in> keys (to_trans_raw_sig \<tau> sig)"
    unfolding \<tau>'_def preempt_raw_def
proof -
  assume "k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig (\<lambda>t'. if t + dly \<le> t' then (\<tau> t')(sig := None) else \<tau> t') sig)"
  then have f1: "(if t + dly \<le> k then (\<tau> k)(sig := None) else \<tau> k) sig \<noteq> None"
    by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
  then have "\<not> t + dly \<le> k"
    by force
  then show ?thesis
    using f1 by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
qed

lemma preempt_raw_preserves_non_stuttering:
  fixes dly t :: nat 
  fixes sig :: "'signal'"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>' \<equiv> preempt_raw sig \<tau> (t + dly)"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> sig"
proof - 
  { fix k1 k2 
    assume "k1 \<in> keys (to_trans_raw_sig \<tau>' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>' sig)"
    hence "k1 \<in> keys (to_trans_raw_sig \<tau> sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau> sig)"
      by (simp add: \<tau>'_def preempted_keys_subset_of)+
    have "k2 < t + dly"
      using `k2 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def
      keys_def using leI zero_option_def by fastforce
    assume "k1 < k2"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
    have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
    proof (rule ccontr)
      assume "\<not> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig))"
      then obtain k where "k1 < k" and "k < k2" and "k \<in> keys (to_trans_raw_sig \<tau> sig)"
        by auto
      have "k2 \<le> t + dly"
        using `k2 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def
      proof -
        assume a1: "k2 \<in> Femto_VHDL_raw.keys (\<lambda>n. (if t + dly \<le> n then (\<tau> n)(sig := None) else \<tau> n) sig)"
        have "\<And>f. Femto_VHDL_raw.keys f = {n. f (n::nat) \<noteq> (None::bool option)}"
          by (simp add: keys_def zero_option_def)
        then have "\<not> t + dly \<le> k2"
          using a1 by force
        then show ?thesis
          by (meson nat_le_linear)
      qed
      hence "k < t + dly"
        using `k < k2` by auto
      hence "k \<in> keys (to_trans_raw_sig \<tau>' sig)"
        using `k \<in> keys (to_trans_raw_sig \<tau> sig)` unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def
        by (simp add: keys_def)
      thus False
        using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)` `k1 <k` `k < k2`
        by auto
    qed
    hence "to_trans_raw_sig \<tau> sig k1 \<noteq> to_trans_raw_sig \<tau> sig k2"
      using assms(1) `k1 < k2` `k1 \<in> keys (to_trans_raw_sig \<tau> sig)` `k2 \<in> keys (to_trans_raw_sig \<tau> sig)`
      unfolding non_stuttering_def by auto
    moreover have "to_trans_raw_sig \<tau> sig k2 = to_trans_raw_sig \<tau>' sig k2"
      using `k2 < t + dly` unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def by auto
    moreover have "to_trans_raw_sig \<tau> sig k1 = to_trans_raw_sig \<tau>' sig k1"
      using `k1 < k2` `k2 < t + dly` unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def
      by auto
    ultimately have "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
      by auto }
  note first_po = this
  { assume *: "keys (to_trans_raw_sig \<tau>' sig) \<noteq> {}"
    hence "keys (to_trans_raw_sig \<tau> sig) \<noteq> {}"
      unfolding \<tau>'_def to_trans_raw_sig_def preempt_raw_def
    proof -
      have "\<forall>f n. (n::nat) \<notin> {n. f n \<noteq> (0::bool option)} \<or> None \<noteq> f n"
        using zero_option_def by auto
      then have "\<exists>n. \<tau> n sig \<noteq> 0"
        by (metis (no_types) \<open>Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig) \<noteq> {}\<close> \<tau>'_def ex_in_conv keys_def preempted_keys_subset_of to_trans_raw_sig_def zero_option_def)
      then show "Femto_VHDL_raw.keys (\<lambda>n. \<tau> n sig) \<noteq> {}"
        by (simp add: keys_def)
    qed
    hence **: "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau> sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau> sig)))"
      using assms(1) unfolding non_stuttering_def by auto
    have subset: "keys (to_trans_raw_sig \<tau>' sig) \<subseteq> keys (to_trans_raw_sig \<tau> sig)"
      unfolding \<tau>'_def preempt_raw_def to_trans_raw_sig_def keys_def
      by (simp add: Collect_mono zero_option_def)
    define least_key' where "least_key' = (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>' sig))"
    have "least_key' \<in> keys (to_trans_raw_sig \<tau>' sig)"
    proof -
      have "\<exists>k. k \<in> keys (to_trans_raw_sig \<tau>' sig)"
        using * by auto
      thus ?thesis
        by (metis LeastI_ex least_key'_def)
    qed
    have "least_key' < t + dly"
    proof (rule ccontr)
      assume "\<not> least_key' < t + dly"
      hence "t + dly \<le> least_key'" by auto
      hence "\<tau>' least_key' sig = None"
        unfolding \<tau>'_def preempt_raw_def by auto
      hence "least_key' \<notin> keys (to_trans_raw_sig \<tau>' sig)"
        by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
      with `least_key' \<in> keys (to_trans_raw_sig \<tau>' sig)` show False
        by auto
    qed
    have "(LEAST n. n \<in> keys (to_trans_raw_sig \<tau> sig)) = least_key'"
    proof (rule Least_equality)  
      show "least_key' \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
        using `least_key' \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)` subset
        by auto
    next
      { fix y
        assume "\<not> least_key' \<le> y" hence "y < least_key'" by auto
        hence "y \<notin> keys (to_trans_raw_sig \<tau>' sig)"
          unfolding least_key'_def using not_less_Least by blast
        have "y < t + dly"
          using `y < least_key'` `least_key' < t + dly` by auto
        hence "y \<notin> keys (to_trans_raw_sig \<tau> sig)"
            using `y \<notin> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def preempt_raw_def
            by (simp add: keys_def to_trans_raw_sig_def) }
      thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<Longrightarrow> least_key' \<le> y"
        by auto
    qed
    hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>' sig least_key')"
      using ** `least_key' < t + dly` 
      by (metis \<tau>'_def not_le preempt_raw_def to_trans_raw_sig_def) }
  with first_po show ?thesis
    unfolding non_stuttering_def by auto
qed

lemma purge_trans_post_preserve_non_stuttering:
  fixes \<tau> sig t dly cur_val
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>'  \<equiv> purge_raw \<tau> t dly sig (\<sigma> sig) cur_val"
  defines "\<tau>'' \<equiv> trans_post_raw sig cur_val (\<sigma> sig) \<tau>' t dly"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "0 < dly"
  shows "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> sig"
proof (cases "cur_val = \<sigma> sig")
  case False  
  let ?s1 = "signal_of (\<sigma> sig) \<tau> sig t"            
  let ?s2 = "signal_of (\<sigma> sig) \<tau> sig (t + dly)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (t + dly)"        
  have "(?s1 = cur_val \<or> ?s2 = (\<not> cur_val)) \<or> (?s1 = (\<not> cur_val) \<and> ?s2 = cur_val)"
    by auto
  moreover
  { assume "?s1 = cur_val \<or> ?s2 = (\<not> cur_val)"
    hence lookup: "\<tau>' = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t <.. t + dly} "
      unfolding \<tau>'_def purge_raw_def by auto
    hence "\<tau> t sig = None"
      using assms(4)  by (simp add: zero_fun_def zero_option_def)
    have "post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
    proof -
      have *: "(\<forall>i>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau>' i sig = None)"
        using lookup unfolding override_on_def by transfer' auto
      hence "\<tau>' t sig = None"
        using lookup `\<tau> t sig = None` unfolding override_on_def by auto
      hence "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau>' i sig = None)"
        using *  using le_eq_less_or_eq by blast
      thus ?thesis
        using post_necessary_raw_correctness2 False 
        by (metis "*" \<open>\<tau>' t sig = None\<close> \<tau>'_def assms(4) leI order_refl purge_preserve_trans_removal_nonstrict)
    qed
    hence lookup2: "\<tau>'' = post_raw sig cur_val \<tau>' (t + dly)"
      unfolding \<tau>''_def trans_post_raw_def by auto
    have *: "\<forall>k \<in> keys (to_trans_raw_sig \<tau>'' sig). k = t + dly"
    proof 
      fix k
      assume "k \<in> keys (to_trans_raw_sig \<tau>'' sig)"      
      have "k \<in> keys (to_trans_raw_sig \<tau>' sig) \<or> k = t + dly"
      proof (rule ccontr)
        assume "\<not> (k \<in> keys (to_trans_raw_sig \<tau>' sig) \<or> k = t + dly)"
        hence "k \<notin> keys (to_trans_raw_sig \<tau>' sig)" and "k \<noteq> t + dly"
          by auto
        hence "k < t + dly \<or> k > t + dly"
          by auto
        moreover
        { assume "k > t + dly"
          hence "\<tau>'' k sig = None"
            unfolding lookup2 post_raw_def by auto
          hence "k \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          with `k \<in> keys (to_trans_raw_sig \<tau>'' sig)` have False
            by auto }
        moreover
        { assume "k < t + dly"
          hence "\<tau>'' k sig = \<tau>' k sig"
            unfolding lookup2 post_raw_def by auto
          also have "... = None"
            unfolding lookup using \<open>k < t + dly\<close> assms(4) 
            by (metis \<open>\<not> (k \<in> keys (to_trans_raw_sig \<tau>' sig) \<or> k = t + dly)\<close> domIff dom_def keys_def
            lookup to_trans_raw_sig_def zero_option_def)
          finally have "\<tau>'' k  sig = None"
            by auto
          hence "k \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          with `k \<in> keys (to_trans_raw_sig \<tau>'' sig)` have False
            by auto }
        ultimately show False
          by auto
      qed
      moreover have "k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
      proof (rule ccontr)
        assume "\<not> k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
        hence "k \<in> keys (to_trans_raw_sig \<tau>' sig)"
          by auto
        have "k > t + dly"
        proof (rule ccontr)
          assume "\<not> k > t + dly"
          hence "k \<le> t + dly"
            by auto
          hence "\<tau>' k sig = None"
            unfolding lookup using assms(4)
            by (metis (mono_tags, lifting) One_nat_def \<open>\<tau> t sig = None\<close> add.right_neutral
            fun_upd_same greaterThanAtMost_iff leI less_Suc_eq_le nat_add_left_cancel_le
            override_on_apply_in override_on_apply_notin zero_less_one)
          hence "k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          with `k \<in> keys (to_trans_raw_sig \<tau>' sig)` show False by auto
        qed
        hence "\<tau>'' k sig = None"
          unfolding lookup2 post_raw_def  by auto
        hence "k \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
          by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
        with `k \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False 
          by auto
      qed
      ultimately show "k = t + dly"
        by auto
    qed
    have "\<tau>'' (t + dly) sig \<noteq> None"
      unfolding lookup2 post_raw_def  by simp
    hence "t + dly \<in> keys (to_trans_raw_sig \<tau>'' sig)"
      by (metis domIff dom_def keys_def to_trans_raw_sig_def zero_option_def)
    { fix k1 k2 :: nat
      assume "k1 < k2"
      assume "k1 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)"
      assume "k2 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)"
      hence "k1 = k2"
        using `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` using *  by metis
      with `k1 < k2` have False by auto
      hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
        by auto }
    hence first_po: "(\<forall>k1 k2.
        k1 < k2 \<and>
        k1 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig) \<and>
        k2 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow>
        to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2)"
      by auto
    have "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}"
      using \<open>t + dly \<in> keys (to_trans_raw_sig \<tau>'' sig)\<close> by auto
    have "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)) = t + dly"
      unfolding *  by (meson "*" LeastI \<open>t + dly \<in> keys (to_trans_raw_sig \<tau>'' sig)\<close>)
    hence "the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig))) = cur_val"
      using * unfolding to_trans_raw_sig_def lookup2 post_raw_def by simp 
    hence " \<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)))"
      using False by auto
    with first_po have ?thesis
      unfolding non_stuttering_def by auto }
  moreover
  { assume "?s1 = (\<not> cur_val) \<and> ?s2 = cur_val"
    hence lookup: "\<tau>' = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t <..< the ?k2} \<union> {the ?k2 <.. t + dly}) "
      unfolding \<tau>'_def purge_raw_def Let_def by auto
    hence "\<tau> t sig = None"
      using assms(4)  by (simp add: zero_fun_def zero_option_def)
    have "?s1 \<noteq> cur_val" and "?s2 \<noteq> (\<not> cur_val) "
      using`?s1 = (\<not> cur_val) \<and> ?s2 = cur_val` by auto
    have *: "\<exists>n>t. n \<le> t + dly \<and> \<tau> n sig = Some cur_val"
      using switch_signal_ex_mapping[of "\<sigma>", OF `?s1 \<noteq> cur_val` `?s2 \<noteq> (\<not> cur_val)`]
      assms(4)  by (simp add: zero_fun_def)
    obtain time where "?k2 = Some time \<and> time \<le> t + dly"
      by (metis False \<open>signal_of (\<sigma> sig) \<tau> sig t = (\<not> cur_val) \<and> signal_of (\<sigma> sig) \<tau> sig (t + dly)
      = cur_val\<close> comp_def inf_time_at_most option.case_eq_if option.collapse to_signal_def)
    hence time_greatest: "time = (GREATEST l. l \<in> keys (to_trans_raw_sig \<tau> sig) \<and> l \<le> t + dly)"
      by (simp add: inf_time_when_exist)
    have "time \<in> keys (to_trans_raw_sig \<tau> sig)"
      using GreatestI_ex_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> t + dly"] *
      by (meson \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close>
      inf_time_some_exists)
    hence "t < time"
      using assms(4) 
      by (metis domIff dom_def keys_def not_less to_trans_raw_sig_def zero_fun_def zero_option_def)
    have time_greatest': "\<forall>n > time. n < t + dly \<longrightarrow> \<tau> n sig = None"
      unfolding time_greatest
      using Greatest_le_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> t + dly" and b="t + dly"]
      by (metis (mono_tags) domIff dom_def keys_def nat_le_linear not_le to_trans_raw_sig_def zero_option_def)
    have "\<tau> time sig = Some cur_val"
    proof (rule ccontr)
      assume "\<not> \<tau> time sig = Some cur_val"
      hence "\<tau> time sig = Some (\<not> cur_val)"
      proof -
        have "to_trans_raw_sig \<tau> sig time \<noteq> 0"
          using \<open>time \<in> keys (to_trans_raw_sig \<tau> sig)\<close> keys_def by blast
        then have "\<tau> time sig \<noteq> None"
          by (simp add: to_trans_raw_sig_def zero_option_def)
        then show ?thesis
          using \<open>\<tau> time sig \<noteq> Some cur_val\<close> by force
      qed
      have "inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time"
      proof (intro inf_time_someI)
        show "time \<in> dom (to_trans_raw_sig \<tau> sig)"
          by (simp add: \<open>\<tau> time sig = Some (\<not> cur_val)\<close> domIff to_trans_raw_sig_def)
      next
        show "time \<le> t + dly"
          using \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close> by blast
      next
        show "\<forall>ta\<in>dom (to_trans_raw_sig \<tau> sig). ta \<le> t + dly \<longrightarrow> ta \<le> time"
          using time_greatest' 
          by (meson \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close>
          inf_time_someE)
      qed
      hence "?s2 = (\<not> cur_val)"
        using \<open>\<tau> time sig = Some (\<not> cur_val)\<close> unfolding to_signal_def comp_def
        by (simp add: to_trans_raw_sig_def)
      with `?s2 \<noteq> (\<not> cur_val)` show False by auto
    qed
    have not_nec: "time < t + dly \<Longrightarrow> \<not> post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
    proof -
      assume "time < t + dly"
      have "(\<exists>i\<le>t + (dly - 1). \<tau>' i sig = Some cur_val \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau>' j sig = None))"
      proof (intro exI[where x="time"], intro conjI)
        show "time \<le> t + (dly - 1)"
          using \<open>time < t + dly\<close> by linarith
      next
        show "\<tau>' time sig = Some cur_val"
          by (simp add: \<open>\<tau> time sig = Some cur_val\<close> \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) =
          Some time \<and> time \<le> t + dly\<close> local.lookup)
      next
        show "\<forall>j>time. j \<le> t + (dly - 1) \<longrightarrow> \<tau>' j sig = None"
          by (metis (mono_tags, lifting) Suc_diff_1 add_Suc_right assms(5) fun_upd_triv
          le_imp_less_Suc local.lookup override_on_apply_in override_on_apply_notin
          time_greatest')
      qed
      thus "\<not> post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
        unfolding post_necessary_raw_correctness by auto 
    qed
    have nec: "time = t + dly \<Longrightarrow> post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
    proof -
      assume "time = t + dly"
      hence "\<tau>' = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t <..< t + dly})"
        unfolding lookup 
        using \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close> by auto
      hence "\<forall>i\<le>t + (dly - 1). \<tau>' i sig = None"
        using assms(4) 
        by (metis (no_types, lifting) Suc_diff_1 \<open>\<tau> t sig = None\<close> \<open>inf_time (to_trans_raw_sig \<tau>)
        sig (t + dly) = Some time \<and> time \<le> t + dly\<close> \<open>time = t + dly\<close> \<tau>'_def add_Suc_right
        add_diff_cancel_right' assms(5) fun_upd_same greaterThanLessThan_iff le_diff_conv
        le_imp_less_Suc not_less override_on_apply_in purge_preserve_trans_removal_nonstrict)
      hence "(\<forall>i\<le>t + (dly - 1). \<tau>' i sig = None) \<and> cur_val \<noteq> \<sigma> sig"
        using False by blast
      thus "post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
        unfolding post_necessary_raw_correctness2 by auto 
    qed
    have "time < t + dly \<or> time = t + dly"
      using \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close>
      le_neq_implies_less by blast
    moreover
    { assume "time < t + dly"
      hence "\<not> post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
        using not_nec by auto
      hence "\<tau>'' = preempt_raw sig \<tau>' (t + dly)"
        unfolding \<tau>''_def trans_post_raw_def by auto
      have *: "\<forall>k \<in> keys (to_trans_raw_sig \<tau>'' sig). k = the ?k2"
      proof 
        fix k
        assume "k \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        hence in_prime: "k \<in> keys (to_trans_raw_sig \<tau>' sig)"
          unfolding `\<tau>'' = preempt_raw sig \<tau>' (t + dly)`  by (simp add: preempted_keys_subset_of)
        hence "k \<notin> {t <..< the ?k2} \<and> k \<notin> {the ?k2 <.. t + dly}"
          unfolding lookup
        proof -
          assume "k \<in> keys (to_trans_raw_sig (override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t<..<the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))} \<union> {the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))<..t + dly})) sig)"
          then have "override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t<..<the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))} \<union> {the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))<..t + dly}) k sig \<noteq> None"
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          then show ?thesis
            by force
        qed
        have "\<not> k \<le> t"
          using `k \<in> keys (to_trans_raw_sig \<tau>' sig)` assms(4) 
          by (metis \<tau>'_def domIff dom_def keys_def purge_raw_before_now_unchanged
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence "k = the ?k2 \<or> k \<ge> t + dly"
          using \<open>k \<notin> {t<..<the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))} \<and> k \<notin> {the (inf_time
          (to_trans_raw_sig \<tau>) sig (t + dly))<..t + dly}\<close> by auto
        moreover have "\<not> k \<ge> t + dly"
          using \<open>k \<in> keys (to_trans_raw_sig \<tau>'' sig)\<close>  unfolding `\<tau>'' = preempt_raw sig \<tau>' (t + dly)`  preempt_raw_def 
        proof -
          assume "k \<in> keys (to_trans_raw_sig (\<lambda>t'. if t + dly \<le> t' then (\<tau>' t')(sig := None) else \<tau>' t') sig)"
          then have "(if t + dly \<le> k then (\<tau>' k)(sig := None) else \<tau>' k) sig \<noteq> None"
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          then show ?thesis
            by force
        qed
        ultimately show "k = the ?k2"
          by auto
      qed
      { fix k1 k2 :: nat
        assume "k1 < k2"
        assume "k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        hence "k1 = k2"
          using *  by metis
        with `k1 < k2` have False by auto
        assume "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))"
        hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
          using `False` by auto  }
      hence first_po: "(\<forall>k1 k2.
        k1 < k2 \<and> k1 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> k2 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow>
        to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2)"
        by auto
      have "time \<in> keys (to_trans_raw_sig \<tau>' sig)"
      proof -
        have "\<tau>' time sig = \<tau> time sig"
          unfolding lookup using `time < t + dly` `t < time` `?k2 = Some time \<and> time \<le> t + dly`
          by auto
        with \<open>\<tau> time sig = Some cur_val\<close> have "\<tau>' time sig \<noteq> 0"
          by (simp add: zero_option_def)
        thus ?thesis
          unfolding keys_def to_trans_raw_sig_def by auto
      qed
      moreover have "\<tau>'' time sig = \<tau>' time sig"
        unfolding `\<tau>'' = preempt_raw sig \<tau>' (t + dly)`  preempt_raw_def 
        using `time < t + dly` by auto
      ultimately have "time \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        by (simp add: keys_def to_trans_raw_sig_def)
      hence "keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}"
        by (metis (full_types) domIff dom_def empty_iff keys_def to_trans_raw_sig_def
        zero_option_def)
      have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = time"
        using * `?k2 = Some time \<and> time \<le> t + dly` 
        by (simp add: Least_equality \<open>time \<in> keys (to_trans_raw_sig \<tau>'' sig)\<close>)
      moreover have "\<tau>' time sig = \<tau> time sig"
        unfolding lookup 
        by (simp add: \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close>)
      ultimately have " \<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
        using False `\<tau>'' time sig = \<tau>' time sig` `\<tau> time sig = Some cur_val`
        by (metis option.sel to_trans_raw_sig_def)
      hence ?thesis
        using first_po unfolding non_stuttering_def by auto }
    moreover
    { assume "time = t + dly"
      hence "post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
        using nec by auto
      hence \<tau>''_new_def: "\<tau>'' = post_raw sig cur_val \<tau>' (t + dly)"
        unfolding \<tau>''_def trans_post_raw_def by auto
      have *: "\<forall>k \<in> keys (to_trans_raw_sig \<tau>'' sig). k = t + dly"
      proof 
        fix k
        assume k_in_keys: "k \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        have "k \<le> t + dly"
        proof (rule ccontr)
          assume "\<not> k \<le> t + dly"
          hence "t + dly < k"
            by auto
          hence "\<tau>'' k sig = None"
            unfolding \<tau>''_new_def post_raw_def by auto
          hence "k \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
            unfolding to_trans_raw_sig_def  by (simp add: keys_def zero_option_def)
          with k_in_keys show False
            by auto
        qed
        moreover have "t < k"
        proof (rule ccontr)
          assume "\<not> t < k"
          hence "k \<le> t"
            by auto
          hence "\<tau>'' k sig = \<tau>' k sig"
            unfolding \<tau>''_new_def post_raw_def  using assms(5) by auto
          also have "... = \<tau> k sig"
            unfolding lookup using `k \<le> t` 
            by (metis \<tau>'_def local.lookup purge_raw_before_now_unchanged)
          also have "... = None"
            using assms(4) `k \<le> t`  using \<open>\<tau> t sig = None\<close> by auto
          finally have "\<tau>'' k sig = None"
            by auto
          with k_in_keys show False
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
        qed
        ultimately show "k = t + dly"
          using k_in_keys unfolding \<tau>''_new_def to_trans_raw_sig_def post_raw_def 
        proof -
          assume a1: "k \<in> keys (\<lambda>n. (if n = t + dly then \<tau>' n(sig \<mapsto> cur_val) else if t + dly < n then (\<tau>' n)(sig := None) else \<tau>' n) sig)"
          assume a2: "t < k"
          have f3: "(if k = t + dly then \<tau>' k(sig \<mapsto> cur_val) else if t + dly < k then (\<tau>' k)(sig := None) else \<tau>' k) sig \<noteq> 0"
            using a1 by (simp add: keys_def)
          have f4: "\<forall>n. if n = t + dly then (if n = t + dly then \<tau>' n(sig \<mapsto> cur_val) else if t + dly < n then (\<tau>' n)(sig := None) else \<tau>' n) sig = (\<tau>' n(sig \<mapsto> cur_val)) sig else if t + dly < n then (if n = t + dly then \<tau>' n(sig \<mapsto> cur_val) else if t + dly < n then (\<tau>' n)(sig := None) else \<tau>' n) sig = ((\<tau>' n)(sig := None)) sig else (if n = t + dly then \<tau>' n(sig \<mapsto> cur_val) else if t + dly < n then (\<tau>' n)(sig := None) else \<tau>' n) sig = \<tau>' n sig"
            by presburger
          { assume "\<not> t + dly < k"
            moreover
            { assume "(if k = t + dly then \<tau>' k(sig \<mapsto> cur_val) else if t + dly < k then (\<tau>' k)(sig := None) else \<tau>' k) sig = \<tau>' k sig"
              have "\<not> k < t + dly"
                using f3 a2 \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close> \<open>time = t + dly\<close> local.lookup zero_option_def by auto
              then have ?thesis
                using \<open>k \<le> t + dly\<close> le_neq_implies_less by blast }
            ultimately have ?thesis
              using f4 by meson }
          then show ?thesis
            using f3 zero_option_def by fastforce
        qed
      qed
    { fix k1 k2 :: nat
      assume "k1 < k2"
      assume "k1 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)"
      assume "k2 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)"
      hence "k1 = k2"
        using `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)`  * by metis
      with `k1 < k2` have False by auto
      hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
        by auto }
    hence first_po: "(\<forall>k1 k2.
        k1 < k2 \<and>
        k1 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig) \<and>
        k2 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow>
        to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2)"
      by auto
    have "keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}"
    proof -
      have "\<tau>'' (t + dly) sig = Some cur_val"
        unfolding \<tau>''_new_def post_raw_def by auto
      thus ?thesis
        by (metis domIff dom_def empty_iff keys_def option.distinct(1) to_trans_raw_sig_def zero_option_def)
    qed
    have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly"
      by (smt "*" Collect_empty_eq LeastI \<open>keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}\<close> keys_def mem_Collect_eq)
    hence "the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig))) = cur_val"
      unfolding \<tau>''_new_def post_raw_def  by (simp add: to_trans_raw_sig_def)
    hence " \<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>'' sig)))"
      using False by auto
    with first_po have ?thesis
      unfolding non_stuttering_def by auto }
  ultimately have ?thesis
    by auto }
  ultimately show ?thesis
    by auto
next
  case True
  let ?s1 = "signal_of (\<sigma> sig) \<tau> sig t"            
  let ?s2 = "signal_of (\<sigma> sig) \<tau> sig (t + dly)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (t + dly)"
  have "(?s1 = cur_val \<or> ?s2 = (\<not> cur_val)) \<or> (?s1 = (\<not> cur_val) \<and> ?s2 = cur_val)"
    by auto
  moreover
  { assume "?s1 = cur_val \<or> ?s2 = (\<not> cur_val)"
    hence lookup: "\<tau>' = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t <.. t + dly} "
      unfolding \<tau>'_def purge_raw_def by auto
    have "\<tau> t sig = None"
      using assms(4) by (auto simp add: zero_fun_def zero_option_def)
    have "\<forall>n \<le> t. \<tau> n = 0"
      using assms(4) by (auto simp add: zero_option_def)
    have "\<not> post_necessary_raw (dly - 1) \<tau>' t sig cur_val (\<sigma> sig)"
    proof -
      have *: "(\<forall>i. i \<le> t + (dly - 1) \<longrightarrow> \<tau>' i sig = None)"
        using lookup unfolding override_on_def 
        by (simp add: assms(4) not_less zero_fun_def zero_option_def)
      thus ?thesis
        using post_necessary_raw_correctness True 
        by (metis assms(1) le_add2 not_add_less1 signal_of_intro)
    qed
    hence lookup2: "\<tau>'' = preempt_raw sig \<tau>' (t + dly)"
      unfolding \<tau>''_def  trans_post_raw_def by auto
    hence "to_trans_raw_sig \<tau>'' sig = 0"
      using `\<forall>n \<le> t. \<tau> n = 0` `\<tau> t sig = None` lookup
      unfolding preempt_raw_def to_trans_raw_sig_def override_on_def zero_fun_def zero_option_def
      by (intro ext, simp)
    with True have ?thesis
      unfolding non_stuttering_def Let_def keys_def by (simp add: zero_fun_def) }
  moreover
  { assume "?s1 = (\<not> cur_val) \<and> ?s2 = cur_val"
    have "inf_time (to_trans_raw_sig \<tau>) sig t = None"
      unfolding sym[OF inf_time_none_iff] using assms(4)
      by (metis domIff not_less to_trans_raw_sig_def zero_fun_def zero_option_def)
    hence "signal_of (\<sigma> sig) \<tau> sig t = (\<sigma> sig)"
      unfolding to_signal_def comp_def by auto
    also have "... = cur_val"
      using True by auto
    finally have "signal_of (\<sigma> sig) \<tau> sig t = cur_val"
      by auto
    with \<open>?s1 = (\<not> cur_val) \<and> ?s2 = cur_val\<close> have False 
      by auto
    hence ?thesis
      by auto }
  ultimately show ?thesis
    by auto 
qed 

lemma post_raw_preserves_non_stuttering:
  fixes dly t val
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>' \<equiv> post_raw sig val \<tau> (t + dly)"
  assumes "post_necessary_raw (dly-1) \<tau> t sig val (\<sigma> sig)"
  assumes "\<forall>n \<le> t. \<tau> n = 0"
  assumes "0 < dly"
  shows   "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> sig"
proof -
  have cases: "(\<exists>i\<ge>t. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None)) \<or> 
        (\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau> i sig = None) \<and> val \<noteq> \<sigma> sig"
    using assms(3) unfolding post_necessary_raw_correctness2 
    by (metis assms(4) less_imp_le_nat not_less option.distinct(1) zero_fun_def zero_option_def)
  { fix k1 k2
    assume "k1 \<in> keys (to_trans_raw_sig \<tau>' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>' sig)"
    assume "k1 < k2"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
    have "k2 \<le> t + dly"
      using `k2 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def
    proof -
      assume a1: "k2 \<in> Femto_VHDL_raw.keys (\<lambda>n. (if n = t + dly then \<tau> n(sig \<mapsto> val) else if t + dly < n then (\<tau> n)(sig := None) else \<tau> n) sig)"
      have "\<And>f. Femto_VHDL_raw.keys f = {n. f (n::nat) \<noteq> (None::bool option)}"
        by (simp add: keys_def zero_option_def)
      then show ?thesis
        using a1 by fastforce
    qed
    hence "k2 = t + dly \<or> k2 < t + dly"
      by auto
    moreover
    { assume "k2 = t + dly"
      hence "to_trans_raw_sig \<tau>' sig k2 = Some val"
        unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def by auto
      consider (case1) "(\<exists>i\<ge>t. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None))"
             | (case2) "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau> i sig = None) \<and> val \<noteq> \<sigma> sig"
        using cases by auto
      hence "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
      proof (cases)
        case case1
        then obtain i where "i\<ge>t" and "i \<le> t + (dly-1)" and "\<tau> i sig = Some (\<not> val)" and 
          "\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None" by auto
        have "k1 < t + dly" 
          using `k1 < k2` `k2 \<le> t + dly` by auto
        have "k1 \<in> keys (to_trans_raw_sig \<tau> sig)"
          using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def to_trans_raw_sig_def post_raw_def
        proof -
          assume a1: "k1 \<in> Femto_VHDL_raw.keys (\<lambda>n. (if n = t + dly then \<tau> n(sig \<mapsto> val) else if t + dly < n then (\<tau> n)(sig := None) else \<tau> n) sig)"
          have "\<not> t + dly \<le> k1"
            by (meson \<open>k1 < t + dly\<close> not_le)
          then show "k1 \<in> Femto_VHDL_raw.keys (\<lambda>n. \<tau> n sig)"
            using a1 by (simp add: keys_def)
        qed
        have *: "\<forall>j>k1. j < t + dly \<longrightarrow> \<tau> j sig = None"
          using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)` unfolding `k2 = t + dly`
          \<tau>'_def post_raw_def to_trans_raw_sig_def  by (simp add: keys_def zero_option_def)
        have "i = k1"
        proof (rule ccontr)
          assume "\<not> i = k1" hence "i < k1 \<or> k1 < i" by auto
          moreover
          { assume "i < k1"
            hence "\<exists>j>i. j \<le> t + (dly-1) \<and> \<tau> j sig \<noteq> None"
              using `k1 < k2` `k2 = t + dly` `k1 \<in> keys (to_trans_raw_sig \<tau> sig)`
              apply(intro exI[where x="k1"])
              unfolding to_trans_raw_sig_def keys_def
              by (smt Suc_diff_1 \<open>t \<le> i\<close> add_Suc_right dual_order.order_iff_strict less_Suc_eq_le
              less_add_same_cancel1 less_trans mem_Collect_eq zero_option_def)
            with `\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None` have "False" by auto }
          moreover
          { assume "k1 < i"
            hence "\<exists>j>k1. j < t + dly \<and> \<tau> j sig \<noteq> None"
              using `i \<le> t + (dly-1)` `\<tau> i sig = Some (\<not> val)` 
              by (intro exI[where x="i"])(metis (no_types, hide_lams) One_nat_def Suc_diff_1 add.right_neutral add_Suc_right
              assms(4) diff_is_0_eq' less_Suc_eq_le nat_le_linear not_le option.distinct(1)
              zero_fun_def zero_option_def)
            with * have False by auto }
          ultimately show False by auto
        qed
        thus "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
          using `i = k1` `\<tau> i sig = Some (\<not> val)` `to_trans_raw_sig \<tau>' sig k2 = Some val`
          by (metis \<open>k1 < k2\<close> \<open>k2 = t + dly\<close> \<tau>'_def less_irrefl_nat less_trans option.inject
          post_raw_def to_trans_raw_sig_def)
      next
        case case2      
        have "k1 < t + dly" 
          using `k1 < k2` `k2 \<le> t + dly` by auto
        moreover have "k1 \<in> keys (to_trans_raw_sig \<tau> sig)"
          using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def to_trans_raw_sig_def post_raw_def
        proof -
          assume a1: "k1 \<in> Femto_VHDL_raw.keys (\<lambda>n. (if n = t + dly then \<tau> n(sig \<mapsto> val) else if t + dly < n then (\<tau> n)(sig := None) else \<tau> n) sig)"
          have "\<not> t + dly \<le> k1"
            by (meson \<open>k1 < t + dly\<close> not_le)
          then show "k1 \<in> Femto_VHDL_raw.keys (\<lambda>n. \<tau> n sig)"
            using a1 by (simp add: keys_def)
        qed
        moreover hence "t < k1"
          using assms(4)  
          by (metis domIff dom_def keys_def leI to_trans_raw_sig_def zero_fun_def zero_option_def)
        ultimately have "\<exists>i\<ge>t. i \<le> t + (dly - 1) \<and> \<tau> i sig \<noteq> None"
          apply (intro exI[where x="k1"])
          unfolding to_trans_raw_sig_def keys_def by (simp add: zero_option_def)
        with case2 have "False" by auto
        then show ?thesis by auto
      qed }
    moreover
    { assume "k2 < t + dly"
      hence "k2 \<in> keys (to_trans_raw_sig \<tau> sig)"
        using `k2 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def
        by (simp add: keys_def)
      moreover have "k1 \<in> keys (to_trans_raw_sig \<tau> sig)"
        using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` `k1 < k2` `k2 < t + dly` 
        unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def by (simp add: keys_def)
      moreover have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
        using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)` `k1 < k2` `k2 < t +dly`
        unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def  by (simp add: keys_def)
      ultimately have "to_trans_raw_sig \<tau> sig k1 \<noteq> to_trans_raw_sig \<tau> sig k2"
        using assms(1) `k1 < k2` unfolding non_stuttering_def by auto
      moreover have "to_trans_raw_sig \<tau> sig k1 = to_trans_raw_sig \<tau>' sig k1" and 
        "to_trans_raw_sig \<tau> sig k2 = to_trans_raw_sig \<tau>' sig k2"
        using `k1 < k2` `k2 < t +dly` unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def
        by auto
      ultimately have "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
        by auto }
    ultimately have "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
      by auto }
  note first_po = this
  { assume "keys (to_trans_raw_sig \<tau>' sig) \<noteq> {}"
    { assume "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau> i sig = None) \<and> val \<noteq> \<sigma> sig"
      hence *: "(\<forall>i. i \<le> t + (dly - 1) \<longrightarrow> \<tau>' i sig = None)" and "val \<noteq> \<sigma> sig"
        unfolding \<tau>'_def post_raw_def using `0 < dly` assms(4) 
        by (smt Suc_diff_1 add_Suc_right fun_upd_same le_add1 le_imp_less_Suc less_irrefl_nat nat_le_linear)+
      have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>' sig)) = t + dly"
      proof (intro Least_equality)
        show "t + dly \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)"
          unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def keys_def by (auto simp add: zero_option_def)
      next
        { fix y
          assume "\<not> t + dly \<le> y" hence "y < t + dly" by auto
          hence "\<tau>' y sig = None"
            using * by auto
          hence "y \<notin> keys (to_trans_raw_sig \<tau>' sig)"
            using * unfolding \<tau>'_def to_trans_raw_sig_def keys_def post_raw_def 
            by (auto simp add: zero_option_def) }
        thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig) \<Longrightarrow> t + dly \<le> y"
          by auto
      qed
      hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)))"
        using \<tau>'_def `val \<noteq> \<sigma> sig` unfolding post_raw_def to_trans_raw_sig_def by auto }
    moreover
    { assume "(\<exists>i\<ge>t. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None))"
      then obtain i where "i \<ge> t" and "i \<le> t + (dly - 1)" and "\<tau> i sig = Some (\<not> val)" and 
        "\<forall>j>i. j < t + (dly - 1) \<longrightarrow> \<tau> j sig = None" by auto
      hence **: "i \<in> keys (to_trans_raw_sig \<tau> sig)"
        unfolding keys_def to_trans_raw_sig_def by (auto simp add: zero_option_def)
      hence *: "i \<in> keys (to_trans_raw_sig \<tau>' sig)"
        using `i \<le> t + (dly - 1)` `0 < dly` unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def
        keys_def by auto
      define least_key where "least_key = (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>' sig))"
      have "least_key \<le> t + (dly - 1)"
        using Least_le[where P="\<lambda>k. k \<in> keys (to_trans_raw_sig \<tau>' sig)", OF *] `i \<le> t + (dly-1)`
        unfolding least_key_def by auto
      have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau> sig)) = least_key"
      proof (rule Least_equality)
        have "least_key \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)"
          using LeastI[where P="\<lambda>k. k \<in> keys (to_trans_raw_sig \<tau>' sig)", OF *]
          unfolding least_key_def by auto
        then obtain val' where "\<tau>' least_key sig = Some val'"
          unfolding keys_def to_trans_raw_sig_def by (auto simp add: zero_option_def)
        hence "\<tau> least_key sig = Some val'"
          unfolding \<tau>'_def post_raw_def using `least_key \<le> t + (dly - 1)` `0 < dly`
          by (smt Suc_diff_1 add_Suc_right fun_upd_same le_imp_less_Suc not_le option.distinct(1)
          order_refl)
        thus " least_key \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
          unfolding to_trans_raw_sig_def keys_def by (auto simp add: zero_option_def)
      next
        { fix y 
          assume "\<not> least_key \<le> y" hence "y < least_key" by auto
          hence "y \<notin> keys (to_trans_raw_sig \<tau>' sig)"
            using not_less_Least unfolding least_key_def by auto
          have "y < t + (dly - 1)"
            using `y < least_key` `least_key \<le> t + (dly - 1)` by auto
          hence "\<tau>' y sig = \<tau> y sig"
            unfolding \<tau>'_def post_raw_def by auto
          hence "y \<notin> keys (to_trans_raw_sig \<tau> sig)"
            using `y \<notin> keys (to_trans_raw_sig \<tau>' sig)`  by (simp add: keys_def to_trans_raw_sig_def) }
        thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<Longrightarrow> least_key \<le> y"
          by auto
      qed
      note least_key_alt_def = sym[OF this]
      have ***: "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau> sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)))"
        using assms(1) unfolding non_stuttering_def  using "**" by blast
      have "the (to_trans_raw_sig \<tau> sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig))) = 
            the (to_trans_raw_sig \<tau> sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)))"
        using least_key_alt_def unfolding least_key_def by auto
      also have "... = the (to_trans_raw_sig \<tau> sig least_key)"
        unfolding least_key_def by auto
      also have "... = the (to_trans_raw_sig \<tau>' sig least_key)"
        unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def using `least_key \<le> t + (dly -1)` 
        `0 < dly` by auto
      finally have "the (to_trans_raw_sig \<tau> sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig))) =
                    the (to_trans_raw_sig \<tau>' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)))"
        unfolding least_key_def by auto
      with *** have "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)))"
        by auto }
    ultimately have "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>' sig (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau>' sig)))"
      using cases by auto }
  note second_po = this
  with first_po show ?thesis
    unfolding non_stuttering_def by auto
qed

lemma trans_post_preserves_non_stuttering:
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay cs"
  assumes "cs = Bassign_trans sig e dly"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bassign_trans sig e dly)
  hence \<tau>'_def: "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
    by auto
  have prev_zero: "\<And>n. n < t \<Longrightarrow> to_trans_raw_sig \<tau> s n = 0"
    using Bassign_trans(3) unfolding to_trans_raw_sig_def
    by (auto simp add: zero_fun_def zero_option_def)
  have "0 < dly"
    using Bassign_trans by auto
  have "sig \<noteq> s \<or> sig = s" by auto
  moreover
  { assume "sig \<noteq> s"
    hence "to_trans_raw_sig \<tau>' s = to_trans_raw_sig \<tau> s"
      using \<tau>'_def unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def post_raw_def  
      by auto
    hence ?case
      using Bassign_trans(1) unfolding non_stuttering_def Let_def by auto }
  moreover
  { assume "sig = s"
    have "post_necessary_raw (dly-1) \<tau> t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)\<or>
          \<not> post_necessary_raw (dly-1) \<tau> t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)" by auto
    moreover
    { assume notnec: "\<not> post_necessary_raw (dly-1) \<tau> t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)"
      have look: " \<tau>' = preempt_raw sig ( \<tau>) (t + dly)"
        using notnec unfolding \<tau>'_def trans_post_raw_def by auto
      hence ?case
        using preempt_raw_preserves_non_stuttering[OF Bassign_trans(1)]  by (simp add: \<open>sig = s\<close>) }
    moreover
    { assume nec: "post_necessary_raw (dly-1) \<tau> t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)"
      hence lookup: "\<tau>' = post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) \<tau> (t + dly)"
        unfolding \<tau>'_def by (auto simp add: trans_post_raw_def)
      hence ?case
        using post_raw_preserves_non_stuttering[OF Bassign_trans(1)]
        using Bassign_trans.prems(3) \<open>0 < dly\<close> \<open>sig = s\<close> calculation(2) by blast }
    ultimately have ?case by auto }
  ultimately show ?case by auto
next
  case (Bcomp cs1 cs2)
  have False
    using `Bcomp cs1 cs2 = Bassign_trans sig e dly` by auto
  then show ?case by auto
next
  case (Bguarded x1 cs1 cs2)
  have "False"
    using `Bguarded x1 cs1 cs2 = Bassign_trans sig e dly` by auto
  then show ?case by auto
next
  case (Bassign_inert x1 x2 x3)
  then show ?case by auto
next
  case Bnull
  then show ?case by auto
qed


lemma b_seq_exec_preserves_non_stuttering:
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay cs"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  define \<tau>'' where "\<tau>'' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence *: "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using Bcomp(1)[OF Bcomp(3)] Bcomp(4-) by auto
  have "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def using Bcomp.prems(2) by auto
  moreover have "\<And>n. n < t \<Longrightarrow> \<tau>'' n = 0"
    using b_seq_exec_preserve_trans_removal[OF Bcomp(5)] unfolding \<tau>''_def by auto
  ultimately show ?case
    using Bcomp(2)[OF *] Bcomp(6) 
    by (metis Bcomp.prems(3) \<tau>''_def dual_order.order_iff_strict nonneg_delay.simps(2) nonneg_delay_same)
next
  case (Bguarded x1 cs1 cs2)
  then show ?case 
    by (metis (full_types) b_seq_exec.simps(3) nonneg_delay.simps(3))
next
  case (Bassign_trans sig e dly)
  thus ?case by (meson trans_post_preserves_non_stuttering)
next
  case (Bassign_inert sig e dly)
  hence \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence \<tau>'_def': "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e)) t dly"
    using \<tau>'_def unfolding inr_post_raw_def by auto
  let ?\<tau> = "purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e)"
  have "s = sig \<or> s \<noteq> sig"
    by auto
  moreover
  { assume "s \<noteq> sig"
    hence "\<And>n. to_trans_raw_sig \<tau>' s n = to_trans_raw_sig \<tau> s n"
      using \<tau>'_def' 
      by (metis purge_raw_does_not_affect_other_sig to_trans_raw_sig_def trans_post_raw_diff_sig)
    hence "to_trans_raw_sig \<tau>' s = to_trans_raw_sig \<tau> s"
      by blast
    hence ?case
      using Bassign_inert(1) unfolding non_stuttering_def Let_def by auto }
  moreover
  { assume "s = sig"
    moreover have 3: "\<And>n. n \<le> t \<Longrightarrow> ?\<tau> n = 0"
      using Bassign_inert(3)  by (simp add: purge_preserve_trans_removal_nonstrict)
    obtain cs2 where cs2_def: "cs2 = Bassign_trans sig e dly"
      by auto
    hence 2: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2, ?\<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using \<tau>'_def' by auto
    have 4: "nonneg_delay cs2"
      unfolding cs2_def using Bassign_inert(4) by auto
    have ?case
      using purge_trans_post_preserve_non_stuttering[OF Bassign_inert(1)]
      unfolding \<tau>'_def' `s = sig` using Bassign_inert.prems(3) \<open>0 < dly\<close> 
      by blast }
    ultimately show ?case by auto
next
  case Bnull
  then show ?case by auto
qed

text \<open>end of non stuttering\<close>


definition
seq_hoare_valid :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ {(1_)}/ (_)/ {(1_)}" 50)
where "\<Turnstile>\<^sub>t {P} s {Q} \<longleftrightarrow>  (\<forall>\<sigma> \<tau> \<gamma> \<theta> \<tau>' w w'.  context_invariant t \<sigma> \<gamma> \<theta> \<tau>
                                            \<and> (\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s) 
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
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>) \<and> w = worldline_raw t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> \<tau>'"
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and "w = worldline_raw t \<sigma> \<theta> \<tau>" and "P w" and "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    and "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' " and 2: "w' = worldline_raw t \<sigma> \<theta> \<tau>'"
    by auto
  then obtain \<tau>'' where 0: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and 1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  define w'' where "w'' = worldline_raw t \<sigma> \<theta> \<tau>''"
  hence "Q w''"
    using `\<Turnstile>\<^sub>t {P} s1 {Q}` unfolding seq_hoare_valid_def
    using \<open>P w\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> \<open>w = worldline_raw t \<sigma> \<theta> \<tau>\<close>
    \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
    by blast
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 0] assms(3)
    by auto
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  proof -
    have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
      using b_seq_exec_preserves_non_stuttering[OF _ 0] `All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)`
      `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` assms(3)  by (simp add: context_invariant_def)
    thus ?thesis
      using b_seq_exec_preserves_non_stuttering[OF _ 1] 
      `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` assms(3)  
      by (meson calculation context_invariant_def nonneg_delay.simps(2))
  qed
  ultimately show "R w'"
    using `\<Turnstile>\<^sub>t {Q} s2 {R}` `w'' = worldline_raw t \<sigma> \<theta> \<tau>''` `Q w''` 1 2 unfolding seq_hoare_valid_def
    by (metis (full_types, hide_lams) "0" \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> All (non_stuttering
    (to_trans_raw_sig \<tau>) \<sigma>) \<and> w = worldline_raw t \<sigma> \<theta> \<tau> \<and> P w \<and> t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>>
    \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> \<tau>'\<close> assms(3) b_seq_exec_preserves_non_stuttering
    context_invariant_def nonneg_delay.simps(2))
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
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>) \<and> w = worldline_raw t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> \<tau>'"
  hence s: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and w: "w = worldline_raw t \<sigma> \<theta> \<tau>"
    and c: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and p: "P w" and w': "w' = worldline_raw t \<sigma> \<theta> \<tau>'" and 
      "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
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
      using assms(1) c w \<tau>'_def w' \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> 
      unfolding seq_hoare_valid_def by auto }
  moreover
  { assume "\<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    hence \<tau>'_def: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s by auto
    have "\<not> beval_world_raw w t g"
      using `\<not> beval_raw t \<sigma> \<gamma> \<theta> g` beval_beval_world_raw[OF w] c unfolding context_invariant_def
      by auto
    with `P w` have "Q w'"
      using assms(2) c w \<tau>'_def w' \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
      unfolding seq_hoare_valid_def by auto }
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
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
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
          by (metis purge_raw_does_not_affect_other_sig to_trans_raw_sig_def trans_post_raw_diff_sig)
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
    have "(\<omega> sig t = beval_world_raw \<omega> t exp \<or> \<omega> sig (t + dly) \<noteq> beval_world_raw \<omega> t exp)
         \<or> (\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp)"
      by auto
    moreover
    { assume "\<omega> sig t = beval_world_raw \<omega> t exp \<or> \<omega> sig (t + dly) \<noteq> beval_world_raw \<omega> t exp"
      have "t + dly \<le> t' \<or> t' < t + dly" and "s' = sig" and "t \<le> t'"
        using leI \<open>s' = sig \<and> t \<le> t'\<close> by auto
      moreover
      { assume "t + dly \<le> t'"
        hence 2: "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
            using `s' = sig` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_inert_upd_def  
            using \<open>\<omega> sig t = beval_world_raw \<omega> t exp \<or> \<omega> sig (t + dly) \<noteq> beval_world_raw \<omega> t exp\<close> assms(1) by auto
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
          unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close> 
          using \<open>\<omega> sig t = beval_world_raw \<omega> t exp \<or> \<omega> sig (t + dly) \<noteq> beval_world_raw \<omega> t exp\<close> by auto
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
        proof -
          have 0: "signal_of (\<sigma> s') \<tau> s' t = (beval_world_raw \<omega> t exp) \<or> signal_of (\<sigma> s') \<tau> s' (t + dly) = (\<not> beval_world_raw \<omega> t exp)"
            using `\<omega> sig t = beval_world_raw \<omega> t exp \<or> \<omega> sig (t + dly) \<noteq> beval_world_raw \<omega> t exp` \<open>s' = sig\<close>
            unfolding assms(1) worldline_raw_def by auto            
          thus ?thesis
            using signal_of_inr_post3[OF `t \<le> t'` `t' < t + dly` `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`] \<open>s' = sig\<close>
            unfolding \<tau>'_def 
            by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>s' = sig \<and> t \<le> t'\<close> \<open>t' < t + dly\<close> signal_of_inr_post3)
        qed
        finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<sigma> s'"
          by auto
        with l have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
          using `s' = sig` by auto }
      ultimately have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
        by auto }
    moreover
    { assume "\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp"
      hence sig_not_eq: "signal_of (\<sigma> sig) \<tau> sig t \<noteq> beval_world_raw \<omega> t exp" and 
            sig_eq: "signal_of (\<sigma> sig) \<tau> sig (t + dly) = beval_world_raw \<omega> t exp"
        unfolding assms(1) worldline_raw_def by auto
      hence exist_mapping: "\<exists>k > t. k\<le>t + dly \<and> \<tau> k sig = Some (beval_world_raw \<omega> t exp)"
        using switch_signal_ex_mapping[of "\<sigma>", OF sig_not_eq] `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`
        by (simp add: zero_fun_def)
      let ?time = "GREATEST n. n \<le> t + dly \<and> (\<omega> sig (n - 1) = (\<not> beval_world_raw \<omega> t exp)) \<and> \<omega> sig n = (beval_world_raw \<omega> t exp)"
      have "?time \<le> t' \<or> t' < ?time" and "s' = sig" and "t \<le> t'"
        using \<open>s' = sig \<and> t \<le> t'\<close> by auto
      moreover
      { assume "?time \<le> t'"
        hence 2: "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
            using `s' = sig` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> \<tau>` worldline_inert_upd_def  
            using \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp\<close>
            \<open>s' = sig \<and> t \<le> t'\<close> assms(1) by auto
        have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        also have "... = beval_world_raw \<omega> t exp"
          unfolding \<tau>'_def \<open>s' = sig\<close>
        proof (rule signal_of_inr_post4)
          show "signal_of (\<sigma> sig) \<tau> sig t \<noteq> beval_world_raw \<omega> t exp"
            using \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp\<close>
            by (simp add: assms(1) worldline_raw_def)
        next
          show "post_necessary_raw dly \<tau> t sig (\<not> beval_world_raw \<omega> t exp) (\<sigma> sig)"
            using \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp\<close>
            by (simp add: assms(1) worldline_raw_def)
        next
          have "?time = (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp))" (is "_ = ?time2")
          proof (rule Greatest_equality)
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)" and b="t + dly"]
              exist_mapping by auto
            have "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n
              sig = Some (beval_world_raw \<omega> t exp)) sig = Some (beval_world_raw \<omega> t exp)\<close> leI
              option.distinct(1) zero_fun_def zero_option_def)
            have "signal_of (\<sigma> sig) \<tau> sig ?time2 = beval_world_raw \<omega> t exp"
              using trans_some_signal_of'[of "\<tau>", OF `\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)`]
              by auto
            hence "\<omega> sig ?time2 = beval_world_raw \<omega> t exp"
              using `t < ?time2` unfolding assms(1) worldline_raw_def by auto
            have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
            proof (cases "\<exists>n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None")
              case False
              hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time2 - 1 \<Longrightarrow> \<tau> n sig = 0"
                by (auto simp add: zero_option_def)
              have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) = signal_of (\<sigma> sig) \<tau> sig t"
                using signal_of_less_ind'[of "t" "?time2 - 1" "\<tau>" "sig", OF none] `t < ?time2`
                by auto
              also have "... \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
                using sig_not_eq by auto
              finally show "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
                by auto
            next
              case True
              let ?key1 = "(GREATEST n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None)"
              from True have "t < ?key1" and "?key1 < ?time2" and "\<tau> ?key1 sig \<noteq> None"
                using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
              have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time2 \<Longrightarrow> \<tau> n sig = None"
                using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time2 \<and> \<tau> x sig \<noteq> None" and b="?time2"]
                by (smt \<open>t < (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some
                (beval_world_raw \<omega> t exp)) \<and> \<tau> n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
              have inf_some: "inf_time (to_trans_raw_sig \<tau>) sig (?time2 - 1) = Some ?key1"
              proof (rule inf_time_someI)
                show "?key1 \<in> dom (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
              next
                show "?key1 \<le> ?time2 - 1"
                  using `?key1 < ?time2`  by linarith
              next
                { fix ta
                  assume "ta \<in> dom (to_trans_raw_sig \<tau> sig)"
                  assume "ta \<le> ?time2 - 1"
                  assume "?key1 < ta"
                  hence "\<tau> ta sig = None"
                    using *[OF `?key1 < ta`] `ta \<le> ?time2 - 1` by simp
                  hence "ta \<notin> dom (to_trans_raw_sig \<tau> sig)"
                    by (simp add: domIff to_trans_raw_sig_def)
                  with `ta \<in> dom (to_trans_raw_sig \<tau> sig)` have False by auto }
                thus "\<forall>ta \<in> dom (to_trans_raw_sig \<tau> sig). ta \<le> ?time2 - 1 \<longrightarrow> ta \<le> ?key1"
                  using not_le_imp_less by blast
              qed
              have "\<tau> ?key1 sig \<noteq> \<tau> ?time2 sig"
              proof -
                have "?key1 \<in> keys (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "?time2 \<in> keys (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)` 
                  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "\<forall>k. ?key1 < k \<and> k < ?time2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
                  using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                  zero_option_def)
                ultimately show ?thesis
                  using `?key1 < ?time2` assms(5) unfolding non_stuttering_def 
                  by (simp add: to_trans_raw_sig_def)
              qed
              hence "\<tau> ?key1 sig = Some (\<not> beval_world_raw \<omega> t exp)"
                using \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) sig =
                Some (beval_world_raw \<omega> t exp)\<close> \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly
                \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> by auto
              thus ?thesis
                unfolding to_signal_def comp_def using inf_some 
                by (simp add: to_trans_raw_sig_def)
            qed
            hence "\<omega> sig (?time2 - 1) \<longleftrightarrow>  \<not> beval_world_raw \<omega> t exp"
              using `t < ?time2` unfolding assms(1) worldline_raw_def  by (simp add: leD)
            thus "?time2 \<le> t + dly \<and> \<omega> sig (?time2 - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega> sig ?time2 = beval_world_raw \<omega> t exp"
              using \<open>(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) \<le> t + dly\<close>
              \<open>\<omega> sig (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) =
              beval_world_raw \<omega> t exp\<close> by blast
          next
            fix y
            assume "y \<le> t + dly \<and> \<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega> sig y = beval_world_raw \<omega> t exp"
            hence "y \<le> t + dly" and "\<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp)" and "\<omega> sig y = beval_world_raw \<omega> t exp"
              by auto
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)" and b="t + dly"]
              exist_mapping by auto
            hence "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> leI
              option.distinct(1) zero_fun_def zero_option_def)            
            have "y \<le> t \<or> t < y"
              by auto
            moreover
            { assume "y \<le> t"
              hence "y < ?time2"
                using `t < ?time2` by linarith }
            moreover
            { assume "t < y"
              hence "\<omega> sig (y - 1) = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                unfolding assms(1) worldline_raw_def by auto
              hence 0: "... \<noteq> beval_world_raw \<omega> t exp"
                using `\<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp)` by auto
              have "\<omega> sig y = signal_of (\<sigma> sig) \<tau> sig y"
                unfolding assms(1) worldline_raw_def using `t < y` by auto
              hence 1: "... = beval_world_raw \<omega> t exp"
                using `\<omega> sig y = beval_world_raw \<omega> t exp` `t < y` by auto
              have "\<tau> y sig = Some (beval_world_raw \<omega> t exp)"
              proof (rule ccontr)
                assume "\<not> \<tau> y sig = Some (beval_world_raw \<omega> t exp)"
                hence "\<tau> y sig = None \<or> \<tau> y sig = Some (\<not> beval_world_raw \<omega> t exp)"
                  using domIff by fastforce
                moreover
                { assume "\<tau> y sig = None"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                    by (intro signal_of_less_sig)(simp add: zero_option_def)
                  with 0 1 have False by auto }
                moreover
                { assume "\<tau> y sig = Some (\<not> beval_world_raw \<omega> t exp)"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = (\<not> beval_world_raw \<omega> t exp)"
                    using trans_some_signal_of'  by fastforce
                  with 1 have False by auto }
                ultimately show False by auto
              qed
              with `y \<le> t + dly` have "y \<le> ?time2"
                by (metis (mono_tags, lifting) Greatest_le_nat) }
            ultimately show "y \<le> ?time2"
              by auto
          qed
          thus "(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) \<le> t'"
            using \<open>(GREATEST n. n \<le> t + dly \<and> \<omega> sig (n - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega> sig n
            = beval_world_raw \<omega> t exp) \<le> t'\<close> by linarith
        next
          show "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
            using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> by auto
        qed
        also have "... = beval_world_raw (worldline_raw t \<sigma> \<theta> \<tau>) t exp"
          by (simp add: assms(1))
        finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
          using 2 by auto }
      moreover
      { assume " t' < ?time"
        hence "\<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' = \<omega> sig t"
          unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close> 
          using \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t exp\<close> by auto
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
          unfolding \<tau>'_def \<open>s' = sig\<close>
        proof(rule signal_of_inr_post2)
          show "t \<le> t'"
            by (simp add: \<open>s' = sig \<and> t \<le> t'\<close>)
        next
          show "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
            using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> by blast
        next
          show "\<sigma> sig = (\<not> beval_world_raw \<omega> t exp)"
            using \<open>\<omega> sig t = signal_of (\<sigma> sig) \<tau> sig t\<close> \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig
            (t + dly) = beval_world_raw \<omega> t exp\<close> \<open>signal_of (\<sigma> sig) \<tau> sig t = \<sigma> sig\<close> by blast
        next
          show "signal_of (\<sigma> sig) \<tau> sig (t + dly) = beval_world_raw \<omega> t exp"
            by (metis \<open>\<omega> sig t \<noteq> beval_world_raw \<omega> t exp \<and> \<omega> sig (t + dly) = beval_world_raw \<omega> t
            exp\<close> assms(1) not_add_less1 worldline_raw_def)
        next
          have "?time = (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp))" (is "_ = ?time2")
          proof (rule Greatest_equality)
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)" and b="t + dly"]
              exist_mapping by auto
            have "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n
              sig = Some (beval_world_raw \<omega> t exp)) sig = Some (beval_world_raw \<omega> t exp)\<close> leI
              option.distinct(1) zero_fun_def zero_option_def)
            have "signal_of (\<sigma> sig) \<tau> sig ?time2 = beval_world_raw \<omega> t exp"
              using trans_some_signal_of'[of "\<tau>", OF `\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)`]
              by auto
            hence "\<omega> sig ?time2 = beval_world_raw \<omega> t exp"
              using `t < ?time2` unfolding assms(1) worldline_raw_def by auto
            have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
            proof (cases "\<exists>n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None")
              case False
              hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time2 - 1 \<Longrightarrow> \<tau> n sig = 0"
                by (auto simp add: zero_option_def)
              have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) = signal_of (\<sigma> sig) \<tau> sig t"
                using signal_of_less_ind'[of "t" "?time2 - 1" "\<tau>" "sig", OF none] `t < ?time2`
                by auto
              also have "... \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
                using sig_not_eq by auto
              finally show "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<longleftrightarrow> \<not> beval_world_raw \<omega> t exp"
                by auto
            next
              case True
              let ?key1 = "(GREATEST n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None)"
              from True have "t < ?key1" and "?key1 < ?time2" and "\<tau> ?key1 sig \<noteq> None"
                using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
              have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time2 \<Longrightarrow> \<tau> n sig = None"
                using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time2 \<and> \<tau> x sig \<noteq> None" and b="?time2"]
                by (smt \<open>t < (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some
                (beval_world_raw \<omega> t exp)) \<and> \<tau> n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
              have inf_some: "inf_time (to_trans_raw_sig \<tau>) sig (?time2 - 1) = Some ?key1"
              proof (rule inf_time_someI)
                show "?key1 \<in> dom (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
              next
                show "?key1 \<le> ?time2 - 1"
                  using `?key1 < ?time2`  by linarith
              next
                { fix ta
                  assume "ta \<in> dom (to_trans_raw_sig \<tau> sig)"
                  assume "ta \<le> ?time2 - 1"
                  assume "?key1 < ta"
                  hence "\<tau> ta sig = None"
                    using *[OF `?key1 < ta`] `ta \<le> ?time2 - 1` by simp
                  hence "ta \<notin> dom (to_trans_raw_sig \<tau> sig)"
                    by (simp add: domIff to_trans_raw_sig_def)
                  with `ta \<in> dom (to_trans_raw_sig \<tau> sig)` have False by auto }
                thus "\<forall>ta \<in> dom (to_trans_raw_sig \<tau> sig). ta \<le> ?time2 - 1 \<longrightarrow> ta \<le> ?key1"
                  using not_le_imp_less by blast
              qed
              have "\<tau> ?key1 sig \<noteq> \<tau> ?time2 sig"
              proof -
                have "?key1 \<in> keys (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "?time2 \<in> keys (to_trans_raw_sig \<tau> sig)"
                  using `\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)` 
                  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "\<forall>k. ?key1 < k \<and> k < ?time2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
                  using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                  zero_option_def)
                ultimately show ?thesis
                  using `?key1 < ?time2` assms(5) unfolding non_stuttering_def 
                  by (simp add: to_trans_raw_sig_def)
              qed
              hence "\<tau> ?key1 sig = Some (\<not> beval_world_raw \<omega> t exp)"
                using \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) sig =
                Some (beval_world_raw \<omega> t exp)\<close> \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly
                \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> by auto
              thus ?thesis
                unfolding to_signal_def comp_def using inf_some 
                by (simp add: to_trans_raw_sig_def)
            qed
            hence "\<omega> sig (?time2 - 1) \<longleftrightarrow>  \<not> beval_world_raw \<omega> t exp"
              using `t < ?time2` unfolding assms(1) worldline_raw_def  by (simp add: leD)
            thus "?time2 \<le> t + dly \<and> \<omega> sig (?time2 - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega> sig ?time2 = beval_world_raw \<omega> t exp"
              using \<open>(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) \<le> t + dly\<close>
              \<open>\<omega> sig (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)) =
              beval_world_raw \<omega> t exp\<close> by blast
          next
            fix y
            assume "y \<le> t + dly \<and> \<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega> sig y = beval_world_raw \<omega> t exp"
            hence "y \<le> t + dly" and "\<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp)" and "\<omega> sig y = beval_world_raw \<omega> t exp"
              by auto
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (beval_world_raw \<omega> t exp)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp)" and b="t + dly"]
              exist_mapping by auto
            hence "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> leI
              option.distinct(1) zero_fun_def zero_option_def)            
            have "y \<le> t \<or> t < y"
              by auto
            moreover
            { assume "y \<le> t"
              hence "y < ?time2"
                using `t < ?time2` by linarith }
            moreover
            { assume "t < y"
              hence "\<omega> sig (y - 1) = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                unfolding assms(1) worldline_raw_def by auto
              hence 0: "... \<noteq> beval_world_raw \<omega> t exp"
                using `\<omega> sig (y - 1) = (\<not> beval_world_raw \<omega> t exp)` by auto
              have "\<omega> sig y = signal_of (\<sigma> sig) \<tau> sig y"
                unfolding assms(1) worldline_raw_def using `t < y` by auto
              hence 1: "... = beval_world_raw \<omega> t exp"
                using `\<omega> sig y = beval_world_raw \<omega> t exp` `t < y` by auto
              have "\<tau> y sig = Some (beval_world_raw \<omega> t exp)"
              proof (rule ccontr)
                assume "\<not> \<tau> y sig = Some (beval_world_raw \<omega> t exp)"
                hence "\<tau> y sig = None \<or> \<tau> y sig = Some (\<not> beval_world_raw \<omega> t exp)"
                  using domIff by fastforce
                moreover
                { assume "\<tau> y sig = None"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                    by (intro signal_of_less_sig)(simp add: zero_option_def)
                  with 0 1 have False by auto }
                moreover
                { assume "\<tau> y sig = Some (\<not> beval_world_raw \<omega> t exp)"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = (\<not> beval_world_raw \<omega> t exp)"
                    using trans_some_signal_of'  by fastforce
                  with 1 have False by auto }
                ultimately show False by auto
              qed
              with `y \<le> t + dly` have "y \<le> ?time2"
                by (metis (mono_tags, lifting) Greatest_le_nat) }
            ultimately show "y \<le> ?time2"
              by auto
          qed            
          thus "t' < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (beval_world_raw \<omega> t exp))"
            using \<open>t' < (GREATEST n. n \<le> t + dly \<and> \<omega> sig (n - 1) = (\<not> beval_world_raw \<omega> t exp) \<and> \<omega>
            sig n = beval_world_raw \<omega> t exp)\<close> by linarith
        qed
        finally have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<sigma> s'"
          by auto
        with l have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t' "
          using `s' = sig` by auto }
      ultimately  have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t'"
        by auto }
    ultimately  have "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = \<omega>[sig, t, dly := beval_world_raw \<omega> t exp] s' t'"
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
    assume "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    assume "w = worldline_raw t \<sigma> \<theta> \<tau>"
    assume "P w"
    assume ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    have "worldline_raw t \<sigma> \<theta> \<tau>' = w[sig, t, dly := beval_world_raw w t exp]"
      using lift_inr_post_worldline_upd[OF `w = worldline_raw t \<sigma> \<theta> \<tau>` c ex assms] \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
      by auto
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