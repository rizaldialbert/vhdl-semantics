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

type_synonym 'signal worldline      = "'signal \<Rightarrow> nat \<Rightarrow> val"
type_synonym 'signal worldline_init = "'signal state \<times> ('signal \<Rightarrow> nat \<Rightarrow> val)"


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
trans_raw"} in the semantics @{term "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"}? The answer is that the latter
is the refined version of the former. We shall show the formal relationship later in this theory.
\<close>

definition worldline_upd :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline_init"
  ("_[_, _:= _]") where
  "worldline_upd w s t v = (fst w, \<lambda>s' t'. if s' \<noteq> s \<or> t' < t then snd w s' t' else v)"

definition worldline_inert_upd :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline_init"
  ("_[_, _, _ := _]") where
  "worldline_inert_upd w s t dly v = (fst w,
    (\<lambda>s' t'. let
                time = if snd w s t = v \<or> snd w s (t + dly) \<noteq> v then t + dly
                       else GREATEST n. n \<le> t + dly \<and> (snd w s (n - 1) \<noteq> v) \<and> snd w s n = v
             in
                if s' \<noteq> s \<or> t' < t then snd w s' t' else if t' < time then snd w s' t  else v))"

definition to_worldline_init_bit :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> 'signal worldline_init" where
  "to_worldline_init_bit w sig b = ((fst w)(sig := to_bit b (fst w sig)),  
                                    (snd w)(sig := to_bit b o (snd w sig)))"

fun worldline_inert_upd2 :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline_init"
  where
  "worldline_inert_upd2 w s t dly (Bv v) = worldline_inert_upd w s t dly (Bv v)"
| "worldline_inert_upd2 w s t dly (Lv sign bs) = 
      (fst w, (snd w)(s := \<lambda>n.  let 
                                    w' = \<lambda>b. snd (worldline_inert_upd (to_worldline_init_bit w s b) s t dly (Bv (bs ! b))); 
                                    time = if \<exists>n. t < n \<and> n \<le> t + dly \<and> (\<exists>b \<in> set [0..< length bs] . w' b s (n - 1) \<noteq> w' b s n) then 
                                              LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b \<in> set [0..< length bs] . w' b s (n - 1) \<noteq> w' b s n)
                                           else t + dly
                                in if n < t then snd w s n else if n < time then snd w s t else Lv sign (map (\<lambda>b. bval_of (snd (worldline_inert_upd (to_worldline_init_bit w s b) s t dly (Bv (bs ! b))) s n)) [0..<length bs]))) "

text \<open>These are the two constructs we can use to update or modify a @{typ "'signal worldline"}. Note
that the syntax between these two are quite similar. The only difference is the number of arguments
on the left of the equality sign: @{term "worldline_upd"} has two while @{term
"worldline_inert_upd"} has three. As the names suggest, they correspond to the transport delay
assignment @{term "Bassign_trans"} and inertial delay assignment @{term "Bassign_inert"}.\<close>

type_synonym 'signal assn = "'signal worldline_init \<Rightarrow> bool"

subsection \<open>Validity of Hoare proof rules\<close>

definition worldline_raw ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal worldline_init" where
  "worldline_raw t \<sigma> \<theta> def \<tau> = (def, \<lambda>s' t'. if t' < t then signal_of (def s') \<theta> s' t' else signal_of (\<sigma> s') \<tau> s' t')"

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

definition difference_raw :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "difference_raw w t = (if t = 0 then
                          (\<lambda>s. if snd w s t \<noteq> fst w s then Some (snd w s t) else None)
                         else
                          (\<lambda>s. if snd w s t \<noteq> snd w s (t - 1) then Some (snd w s t) else None))"

lemma difference_raw_alt_def:
  "difference_raw w t = (let
                            base = if t = 0 then fst w else (\<lambda>s. snd w s (t - 1))
                         in
                            (\<lambda>s. if snd w s t \<noteq> base s then Some (snd w s t) else None))"
  unfolding difference_raw_def Let_def by auto

definition derivative_raw :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where "derivative_raw \<equiv> (\<lambda>w t n. if n \<le> t then Map.empty else difference_raw w n)"

definition derivative_hist_raw :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
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
  assumes "\<forall>n \<ge> d. \<forall>s. snd w s n = snd w s d" and "d \<le> t"
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
      have "\<forall>s. snd w s n = snd w s d"
        using assms(1) `d \<le> t` `t < n`  by (meson le_eq_less_or_eq le_less_trans)
      moreover have "\<forall>s. snd w s (n - 1) = snd w s d"
        using assms(1) `d \<le> t` `t < n`
        by (metis Suc_diff_1 diff_is_0_eq' diff_less_mono leI less_Suc_eq_le not_less_zero)
      ultimately have "\<forall>s. snd w s n = snd w s (n - 1)"
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
  assumes "\<forall>n \<ge> d. \<forall>s. snd w s n = snd w s d" and "d < n"
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
      have "\<forall>s. snd w s n = snd w s d"
        using assms le_eq_less_or_eq by blast
      moreover have "\<forall>s. snd w s (n - 1) = snd w s d"
        using assms  by (metis Suc_diff_1 le_less_trans less_Suc_eq_le zero_le)
      ultimately have "\<forall>s. snd w s n = snd w s (n - 1)"
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
  fixes w :: "'signal worldline_init"
  assumes "t' < t"
  shows "signal_of (fst w s') (derivative_hist_raw w t) s' t' = snd w s' t'"
  using assms
proof (induction t')
  case 0
  have *: "derivative_hist_raw w t 0 = difference_raw w 0"
    using 0 by (auto simp add: derivative_hist_raw_def difference_raw_def)
  have "snd w s' 0 \<noteq> fst w s' \<or> snd w s' 0 = fst w s'"
    by auto
  moreover
  { assume "snd w s' 0 = fst w s'"
    hence "inf_time (to_trans_raw_sig (derivative_hist_raw w t)) s' 0 = None"
      unfolding sym[OF inf_time_none_iff] to_trans_raw_sig_def
      by (smt \<open>derivative_hist_raw w t 0 = difference_raw w 0\<close> difference_raw_def domIff neq0_conv)
    hence "signal_of (fst w s') (derivative_hist_raw w t) s' 0 = fst w s'"
      unfolding to_signal_def comp_def by auto
    also have "... = snd w s' 0"
      using `snd w s' 0 = fst w s'` by auto
    finally have ?case
      by auto }
  moreover
  { assume "snd w s' 0 \<noteq> fst w s'"
    have "inf_time (to_trans_raw_sig (derivative_hist_raw w t)) s' 0 = Some 0"
    proof (intro inf_time_someI)
      show "0 \<in> dom (to_trans_raw_sig (derivative_hist_raw w t) s')"
        unfolding to_trans_raw_sig_def dom_def mem_Collect_eq * difference_raw_def
        using `snd w s' 0 \<noteq> fst w s'` by auto
    qed (auto)
    hence "signal_of (fst w s') (derivative_hist_raw w t) s' 0 = the (to_trans_raw_sig (derivative_hist_raw w t) s' 0)"
      unfolding to_signal_def comp_def by auto
    also have "... = snd w s' 0"
      unfolding to_trans_raw_sig_def * difference_raw_def using `snd w s' 0 \<noteq> fst w s'`
      by auto
    finally have ?case
      by auto }
  ultimately show ?case
    by blast
next
  case (Suc t')
  have "snd w s' (Suc t') = snd w s' t' \<or> snd w s' (Suc t') \<noteq> snd w s' t'"
    by auto
  moreover
  { assume "snd w s' (Suc t') \<noteq> snd w s' t'"
    have "derivative_hist_raw w t (Suc t') = difference_raw w (Suc t')"
      using Suc by (auto simp add: derivative_hist_raw_def)
    moreover have "difference_raw w (Suc t') s' = Some (snd w s' (Suc t'))"
      using Suc `snd w s' (Suc t') \<noteq> snd w s' t'` unfolding difference_raw_def by auto
    ultimately have "derivative_hist_raw w t (Suc t') s' = Some (snd w s' (Suc t'))"
      by auto
    hence ?case
      by (intro trans_some_signal_of', simp) }
  moreover
  { assume " snd w s' (Suc t') = snd w s' t'"
    have "derivative_hist_raw w t (Suc t') = difference_raw w (Suc t')"
      using Suc by (auto simp add : derivative_hist_raw_def)
    moreover have "difference_raw w (Suc t') s' = None"
      using Suc `snd w s' (Suc t') = snd w s' t'` unfolding difference_raw_def by auto
    ultimately have "derivative_hist_raw w t (Suc t') s' = None"
      by auto
    hence "signal_of (fst w s') (derivative_hist_raw w t) s' (Suc t') =  signal_of (fst w s') (derivative_hist_raw w t) s' t'"
      by (intro signal_of_suc_sig) (simp add: zero_option_def)
    also have "... = snd w s' t'"
      using Suc  Suc_lessD by blast
    finally have ?case
      using `snd w s' (Suc t') = snd w s' t'` by auto }
  ultimately show ?case
    by blast
qed

lemma signal_of_derivative_hist_raw2:
  assumes "t \<le> t'" and "0 < t"
  shows "signal_of (fst w s') (derivative_hist_raw w t) s' t' = snd w s' (t - 1)"
proof -
  have "t - 1 < t"
    using assms by auto
  have "signal_of (fst w s') (derivative_hist_raw w t) s' t' = signal_of (fst w s') (derivative_hist_raw w t) s' t"
    using assms
    by (intro signal_of_less_ind')(auto simp add: derivative_hist_raw_def zero_option_def)
  also have "... = signal_of (fst w s') (derivative_hist_raw w t) s' (t - 1)"
    by (intro signal_of_less_sig) (auto simp add: derivative_hist_raw_def zero_option_def)
  also have "... = snd w s' (t - 1)"
    using signal_of_derivative_hist_raw[OF `t - 1 < t`] by metis
  finally show "signal_of (fst w s') (derivative_hist_raw w t) s' t' = snd w s' (t - 1)"
    by auto
qed

lemma signal_of_derivative_hist_raw3:
  assumes "0 \<le> t'" 
  shows   "signal_of (fst w s') (derivative_hist_raw w 0) s' t' = fst w s'"
proof -
  have "derivative_hist_raw w 0 = (\<lambda>n. Map.empty)"
    unfolding derivative_hist_raw_def by auto
  hence "inf_time (to_trans_raw_sig (derivative_hist_raw w 0)) s' t' = inf_time (to_trans_raw_sig (\<lambda>n. Map.empty)) s' t'"
    by auto
  also have "... = inf_time (\<lambda>n. Map.empty) s' t'"
    unfolding to_trans_raw_sig_def by auto
  also have "... = None"
    using inf_time_none_iff by force
  finally show ?thesis
    unfolding to_signal_def comp_def by auto
qed

lemma signal_of_derivative_raw_t:
  assumes "\<sigma> s' = snd w s' t"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t = snd w s' t"
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
  assumes "snd w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' t'"
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
  also have "... = snd w s' 0"
    using `snd w s' t = \<sigma> s'` `t = 0` by auto
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
    also have "... = snd w s' (Suc t')"
      using `snd w s' t = \<sigma> s'` `Suc t' = t` by auto
    finally have ?case unfolding `Suc t' = t` by auto }
  moreover
  { assume "t < Suc t'"
    hence "t \<le> t'"
      by auto
    hence lookup: " (derivative_raw w t) (Suc t') = difference_raw w (Suc t')"
      by (auto simp add: derivative_raw_def)
    have "snd w s' (Suc t') = snd w s' t' \<or> snd w s' (Suc t') \<noteq> snd w s' t'"
      by auto
    moreover
    { assume "snd w s' (Suc t') = snd w s' t'"
      hence "difference_raw w (Suc t') s' = None"
        unfolding difference_raw_def by auto
      hence "(derivative_raw w t) (Suc t') s' = None"
        using lookup by auto
      hence "signal_of (\<sigma> s') (derivative_raw w t) s' (Suc t') =  signal_of (\<sigma> s') (derivative_raw w t) s' t'"
        by(intro signal_of_suc_sig)(simp add: zero_option_def)
      also have "... = snd w s' t'"
        using Suc(1)[OF `t \<le> t'` Suc(3)] by auto
      also have "... = snd w s' (Suc t')"
        using `snd w s' (Suc t') = snd w s' t'` by auto
      finally have ?case by auto }
    moreover
    { assume "snd w s' (Suc t') \<noteq> snd w s' t'"
      hence "difference_raw w (Suc t') s' = Some (snd w s' (Suc t'))"
        unfolding difference_raw_def by auto
      hence "(derivative_raw w t) (Suc t') s' = Some (snd w s' (Suc t'))"
        using lookup by auto
      hence ?case
        by (intro trans_some_signal_of') }
    ultimately have ?case by blast }
  ultimately show ?case by auto
qed

lemma signal_of_derivative_raw2:
  assumes "\<forall>n\<ge>d. snd w s' n = snd w s' d"
  assumes "d \<le> t'"
  assumes "snd w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' d"
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
      have "snd w s' n = snd w s' d"
        using assms `d < n`  using less_imp_le_nat by blast
      also have "... = snd w s' (n-1)"
        using `d < n` assms(1) by (metis Suc_diff_1 less_Suc_eq_0_disj less_Suc_eq_le
        less_imp_Suc_add)
      finally have "snd w s' n = snd w s' (n - 1)"
        by auto
      hence "derivative_raw w t n s' = difference_raw w n s'"
        using `t < n` unfolding derivative_raw_def by auto
      also have "... = None"
        unfolding difference_raw_def using \<open>snd w s' n = snd w s' (n-1)\<close> `t < n` by auto
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
    have "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' t'"
      using signal_of_derivative_raw[OF `t \<le> t'`, of "w" "s'" "\<sigma>", OF assms(3)]  by auto
    also have "... = snd w s' d"
      using assms(1-2)  by blast
    finally have "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' d"
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
    also have "... = snd w s' t"
      using assms(3) by auto
    also have "... = snd w s' d"
      using assms(1) `t' < t` `d \<le> t'` by (meson less_trans not_le)
    finally have "signal_of (\<sigma> s') (derivative_raw w t) s' d = snd w s' d"
      by auto
    hence "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' d"
      using * by auto }
  ultimately show ?thesis by auto
qed

lemma signal_of_derivative_raw':
  assumes "t \<le> t'" and "t \<le> d"
  assumes "\<And>n s. d < n \<Longrightarrow> snd w s n = snd w s d"
  assumes "snd w s' t = \<sigma> s'"
  shows "signal_of (\<sigma> s') (derivative_raw w t) s' t' = snd w s' t'"
  using assms by (metis signal_of_derivative_raw)

lemma signal_of_derivative_raw_degree_lt_now:
  assumes "\<forall>n\<ge> d. \<forall>s. snd w s n = snd w s d"
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

text \<open>non-stuttering\<close>

definition non_stuttering :: "'signal trans_raw_sig \<Rightarrow> 'signal state \<Rightarrow> 'signal \<Rightarrow> bool" where
  "non_stuttering \<tau> \<sigma> s \<equiv> (\<forall>k1 k2.
                                    k1 < k2 \<and> k1 \<in> keys (\<tau> s) \<and> k2 \<in> keys (\<tau> s)
                                 \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (\<tau> s)) \<longrightarrow> \<tau> s k1 \<noteq> \<tau> s k2)
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
    assume a1: "(\<forall>k1 k2. k1 < k2 \<and> k1 \<in> keys (\<tau> s) \<and> k2 \<in> keys (\<tau> s) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (\<tau> s)) \<longrightarrow> \<tau> s k1 \<noteq> \<tau> s k2) \<and> (keys (\<tau> s) \<noteq> {} \<longrightarrow> \<sigma> s \<noteq> the (\<tau> s (LEAST k. k \<in> keys (\<tau> s))))"
    have "\<And>n f. (n::nat) \<notin> {n. f n \<noteq> (None::val option)} \<or> f n \<noteq> None"
      by fastforce
    then show "the (\<tau> s t1) \<noteq> the (\<tau> s t2)"
      using a1 by (metis \<open>\<forall>k. t1 < k \<and> k < t2 \<longrightarrow> k \<notin> keys (\<tau> s)\<close> \<open>t1 < t2\<close> \<open>t1 \<in> keys (\<tau> s)\<close> \<open>t2 \<in> keys (\<tau> s)\<close> keys_def option.collapse zero_option_def)
  qed
qed

lemma derivative_raw_of_worldline_specific:
  fixes \<sigma> :: "'a state"
  fixes def \<theta>
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> def \<tau>"
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
      have "snd w s k \<noteq> snd w s (k - 1) \<or> snd w s k = snd w s (k - 1)"
        by auto
      moreover
      { assume "snd w s k \<noteq> snd w s (k - 1)"
        hence "signal_of (\<sigma> s) \<tau> s k \<noteq> signal_of (\<sigma> s) \<tau> s (k - 1)"
          unfolding w_def worldline_raw_def using `t < k`  by (simp add: discrete)
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
          by (auto intro!: some_inf_time'[where \<sigma>="def(s := val)"])
        have "difference_raw w k s = Some (snd w s k)"
          unfolding difference_raw_def using `snd w s k \<noteq> snd w s (k - 1)` using \<open>t < k\<close> by auto
        also have "... =  (to_trans_raw_sig \<tau> s) k"
          unfolding w_def worldline_raw_def using `t < k` unfolding Femto_VHDL_raw.to_signal_def
          comp_def using inf \<open> (to_trans_raw_sig \<tau> s) k = Some val\<close> by auto
        also have "... = \<tau> k s"
          by (auto simp add: to_trans_raw_sig_def)
        finally have "difference_raw w k s =  \<tau> k s"
          by auto }
      moreover
      { assume "snd w s k = snd w s (k - 1)"
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
            by (auto intro!: some_inf_time'[where \<sigma>="def(s := val)"])
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
              using assms(3) unfolding non_stuttering_def by metis
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
              using assms(3) `\<tau> k s = Some val` unfolding non_stuttering_def
              using \<open>to_trans_raw_sig \<tau> s k = Some val\<close> by auto
            hence False
              using `val = \<sigma> s` by auto }
          ultimately show False by auto
        qed
        hence "difference_raw w k s = \<tau> k s"
          unfolding difference_raw_def using `snd w s k = snd w s (k - 1)` `t < k`
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

\<comment> \<open>It does not make any sense to have @{term "\<theta> 0 \<noteq> 0"} in the theorem below. Suppose that it is so.
Hence we have the history at zero is different from the initial state @{term "def"}. This means that
there is a delta delay transition at time zero for setting the new value at zero. Why don't we set
the time we wish at time zero directly in @{term "def"}?\<close>

lemma derivative_is_history:
  fixes \<sigma> :: "'a state"
  fixes def \<tau>
  assumes *: "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
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
      have "non_stuttering (to_trans_raw_sig \<theta>) def s"
        using assms(3) by auto
      have "snd w s k = snd w s (k - 1) \<or> snd w s k \<noteq> snd w s (k - 1)"
        by auto
      moreover
      { assume "snd w s k = snd w s (k - 1)"
        have "signal_of (def s) \<theta> s k = signal_of (def s) \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `snd w s k = snd w s (k - 1)` unfolding w_def worldline_raw_def by auto
        have "\<theta> k s = 0"
          using current_sig_and_prev_same \<open>0 < k \<and> k < t\<close>
          \<open>non_stuttering (to_trans_raw_sig \<theta>) def s\<close> \<open>signal_of (def s) \<theta> s k = signal_of (def s) \<theta> s (k - 1)\<close>
          by fastforce
        hence "(if snd w s k \<noteq> snd w s (k - 1) then Some (snd w s k) else None) =  \<theta> k s"
          using `snd w s k = snd w s (k-1)` by (auto simp add: zero_option_def) }
      moreover
      { assume "snd w s k \<noteq> snd w s (k - 1)"
        have "signal_of (def s) \<theta> s k \<noteq> signal_of (def s) \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `snd w s k \<noteq> snd w s (k - 1)` unfolding w_def worldline_raw_def
          by (simp add: less_imp_diff_less)
        hence "\<theta> k s \<noteq> 0"
          using signal_of_less_sig  by fastforce
        have "the (\<theta> k s) = signal_of (def s) \<theta> s k "
        proof -
          obtain m where "\<theta> k s = Some m"
            using `\<theta> k s \<noteq> 0`  zero_option_def by fastforce
          then obtain \<sigma> where "\<theta> k s = Some (\<sigma> s)"
            by simp
          thus ?thesis
            using trans_some_signal_of' by fastforce
        qed
        also have "... = snd w s k"
          unfolding w_def worldline_raw_def using `0 < k \<and> k < t` by auto
        finally have "(if snd w s k \<noteq> snd w s (k - 1) then Some (snd w s k) else None) =\<theta> k s"
          using `snd w s k \<noteq> snd w s (k - 1)` by (smt \<open>\<theta> k s \<noteq> 0\<close> option.collapse zero_option_def) }
      ultimately show "(if k = 0 then \<lambda>s. if snd w s k \<noteq> get_time w s then Some (snd w s k) else None else (\<lambda>s. if snd w s k \<noteq> snd w s (k - 1) then Some (snd w s k) else None)) s = \<theta> k s"
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
        have "non_stuttering (to_trans_raw_sig \<theta>) def s"
          using assms(3) by auto
        obtain val where " \<theta> 0 s = None \<or>  \<theta> 0 s = Some val"
          by (meson not_None_eq)
        moreover
        { assume "\<theta> 0 s = None"
          have "snd w s 0 = signal_of (def s) \<theta> s 0"
            unfolding w_def worldline_raw_def using `0 < t` by auto
          also have "... = def s"
            using ` \<theta> 0 s = None` signal_of_empty by (metis signal_of_zero zero_option_def)
          finally have "snd w s 0 = def s"
            by auto
          hence "difference_raw w 0 s = None"
            unfolding difference_raw_def
            by (simp add: w_def worldline_raw_def)
          also have "... =  \<theta> 0 s"
            using ` \<theta> 0 s = None` by auto
          finally have "difference_raw w 0 s =  \<theta> 0 s"
            by auto }
        moreover
        { assume "\<theta> 0 s = Some val"
          hence " (to_trans_raw_sig \<theta> s) 0 \<noteq> None"
            by (auto simp add: to_trans_raw_sig_def)
          have "0 \<in> keys (to_trans_raw_sig \<theta> s)"
            using ` \<theta> 0 s = Some val`
            by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
          hence "keys (to_trans_raw_sig \<theta> s) \<noteq> {}"
            by auto
          hence "val \<noteq> def s"
            using `non_stuttering (to_trans_raw_sig \<theta>) def s`
            unfolding non_stuttering_def
            by (metis (full_types) Least_eq_0 \<open>0 \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<theta> s)\<close> \<open>\<theta> 0
            s = Some val\<close> option.sel to_trans_raw_sig_def)
          hence "snd w s 0 = signal_of (def s) \<theta> s 0"
            unfolding w_def worldline_raw_def using `0 < t` by auto
          also have "... \<noteq> def s"
            using ` \<theta> 0 s = Some val` unfolding `val \<noteq> def s`
            by (metis (mono_tags) \<open>val \<noteq> def s\<close> le_zero_eq signal_of_val_eq to_trans_raw_sig_def)
          finally have "snd w s 0 \<noteq> def s"
            by auto
          hence "difference_raw w 0 s =  Some (snd w s 0)"
            unfolding difference_raw_def
            by (simp add: w_def worldline_raw_def)
          also have "... = Some (signal_of (def s) \<theta> s 0)"
            unfolding w_def worldline_raw_def using \<open>0 < t\<close> by auto
          also have "... = \<theta> 0 s"
            using `\<theta> 0 s = Some val`
            by (metis (mono_tags) leD order_refl signal_of_intro to_trans_raw_sig_def)
          finally have "difference_raw w 0 s = \<theta> 0 s"
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
  fixes def \<theta>
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  defines "w \<equiv> worldline_raw t \<sigma> \<theta> def \<tau>"
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
      have "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s n = signal_of (\<sigma> s) \<tau> s n"
        unfolding worldline_raw_def using `t < n` by auto
      also have "... = \<sigma> s"
        unfolding True by (rule signal_of_empty)
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s n = \<sigma> s"
        by auto }
    hence *: "\<And>s. snd (worldline_raw t \<sigma> \<theta> def \<tau>) s n = \<sigma> s"
      by auto
    { fix s
      have "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s (n-1) = signal_of (\<sigma> s) \<tau> s (n-1)"
        unfolding worldline_raw_def using `t < n` by auto
      also have "... = \<sigma> s"
        unfolding True by (rule signal_of_empty)
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s (n-1) = \<sigma> s"
        by auto }
    hence "\<And>s. snd (worldline_raw t \<sigma> \<theta> def \<tau>) s (n-1) = \<sigma> s"
      by auto
    with * have "\<And>s. snd w s n = snd w s (n-1)"
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
  show "derivative_raw w t x = \<tau> x "
    using assms(3) nat_less_le
    by (simp add: derivative_raw_of_worldline_specific assms(1) w_def)
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
        using \<open>k2 < t + dly\<close> le_less by blast
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
      proof -
        have "\<And>n. n \<notin> {n. to_trans_raw_sig \<tau>' sig n \<noteq> 0} \<or> n \<in> {n. to_trans_raw_sig \<tau> sig n \<noteq> 0}"
          by (metis \<tau>'_def keys_def preempted_keys_subset_of)
        then have f1: "\<And>n. to_trans_raw_sig \<tau>' sig n = 0 \<or> to_trans_raw_sig \<tau> sig n \<noteq> 0"
          by blast
        have "\<exists>n. to_trans_raw_sig \<tau>' sig n \<noteq> 0"
          using "*" keys_def by fastforce
        then show ?thesis
          using f1 by (metis (lifting) to_trans_raw_sig_def)
      qed
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
  shows "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> sig"
proof (cases "cur_val = \<sigma> sig")
  case False
  let ?s1 = "signal_of (\<sigma> sig) \<tau> sig t"
  let ?s2 = "signal_of (\<sigma> sig) \<tau> sig (t + dly)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (t + dly)"
  have "(?s1 = cur_val \<or> ?s2 \<noteq> cur_val) \<or> (?s1 \<noteq>  cur_val \<and> ?s2 = cur_val)"
    by auto
  moreover
  { assume "?s1 = cur_val \<or> ?s2 \<noteq> cur_val"
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
  { assume "?s1 \<noteq> (cur_val) \<and> ?s2 = cur_val"
    hence lookup: "\<tau>' = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t <..< the ?k2} \<union> {the ?k2 <.. t + dly}) "
      unfolding \<tau>'_def purge_raw_def Let_def by auto
    hence "\<tau> t sig = None"
      using assms(4)  by (simp add: zero_fun_def zero_option_def)
    have "?s1 \<noteq> cur_val" and "?s2 = cur_val "
      using`?s1 \<noteq> cur_val \<and> ?s2 = cur_val` by auto
    have *: "\<exists>n>t. n \<le> t + dly \<and> \<tau> n sig = Some cur_val"
      using switch_signal_ex_mapping[of "\<sigma>", OF `?s1 \<noteq> cur_val` `?s2 = cur_val`]
      assms(4)  by (simp add: zero_fun_def)
    obtain time where "?k2 = Some time \<and> time \<le> t + dly"
      by (metis False \<open>signal_of (\<sigma> sig) \<tau> sig t \<noteq> cur_val \<and> signal_of (\<sigma> sig) \<tau> sig (t + dly)
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
      hence "\<tau> time sig \<noteq> Some cur_val"
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
          by (metis \<open>time \<in> keys (to_trans_raw_sig \<tau> sig)\<close> dom_def keys_def zero_option_def)
      next
        show "time \<le> t + dly"
          using \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close> by blast
      next
        show "\<forall>ta\<in>dom (to_trans_raw_sig \<tau> sig). ta \<le> t + dly \<longrightarrow> ta \<le> time"
          using time_greatest'
          by (meson \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time \<and> time \<le> t + dly\<close>
          inf_time_someE)
      qed
      hence "?s2 \<noteq> cur_val"
        using \<open>\<tau> time sig \<noteq> Some cur_val\<close> unfolding to_signal_def comp_def
        by (metis \<open>time \<in> keys (to_trans_raw_sig \<tau> sig)\<close> domIff dom_def keys_def option.exhaust_sel
        option.simps(5) to_trans_raw_sig_def zero_option_def)
      with `?s2 = cur_val` show False by auto
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
          by (smt Suc_diff_1 \<open>t < time\<close> \<open>time < t + dly\<close> add_Suc_right fun_upd_triv le_imp_less_Suc
          less_add_same_cancel1 less_trans lookup override_on_apply_in override_on_apply_notin
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
        by (smt Suc_diff_1 \<open>\<tau> t sig = None\<close> \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some time
        \<and> time \<le> t + dly\<close> \<open>t < time\<close> \<open>time = t + dly\<close> \<tau>'_def add_Suc_right add_diff_cancel_left'
        add_diff_cancel_right' fun_upd_eqD fun_upd_triv greaterThanLessThan_iff le_diff_conv
        le_imp_less_Suc not_less override_on_apply_in purge_preserve_trans_removal_nonstrict
        zero_less_diff)
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
            unfolding \<tau>''_new_def post_raw_def  using "*" by auto
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
  have "(?s1 = cur_val \<or> ?s2 \<noteq> cur_val) \<or> (?s1 \<noteq> cur_val \<and> ?s2 = cur_val)"
    by auto
  moreover
  { assume "?s1 = cur_val \<or> ?s2 \<noteq> cur_val"
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
  { assume "?s1 \<noteq> cur_val \<and> ?s2 = cur_val"
    have "inf_time (to_trans_raw_sig \<tau>) sig t = None"
      unfolding sym[OF inf_time_none_iff] using assms(4)
      by (metis domIff not_less to_trans_raw_sig_def zero_fun_def zero_option_def)
    hence "signal_of (\<sigma> sig) \<tau> sig t = (\<sigma> sig)"
      unfolding to_signal_def comp_def by auto
    also have "... = cur_val"
      using True by auto
    finally have "signal_of (\<sigma> sig) \<tau> sig t = cur_val"
      by auto
    with \<open>?s1 \<noteq> cur_val \<and> ?s2 = cur_val\<close> have False
      by auto
    hence ?thesis
      by auto }
  ultimately show ?thesis
    by auto
qed

lemma purge'_trans_post_preserve_non_stuttering_bv:
  fixes \<tau> sig t dly cur_val b
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>'  \<equiv> purge_raw' \<tau> t dly sig (\<sigma> sig) (Bv b)"
  defines "\<tau>'' \<equiv> trans_post_raw sig (Bv b) (\<sigma> sig) \<tau>' t dly"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  shows "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> sig"
  using purge_trans_post_preserve_non_stuttering assms
  unfolding purge_raw'_def by auto

(* lemma signal_of_to_trans_raw_bit:
  assumes "signal_of def \<tau> sig t = Lv sign bs"
  shows   "signal_of (Bv (lval_of def ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = Bv (bs ! b)"
proof -
  have "signal_of (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b' \<Rightarrow> b')) (to_trans_raw_bit def \<tau> b sig) sig t = Bv (bs ! b)"
    using to_bit_signal_of' assms  by (metis to_bit.simps(2)) 
  thus ?thesis
    sledgehammer
 *)

(* lemma keys_unchanged_to_trans_raw_bit:
  assumes "\<forall>k. k \<in> keys (to_trans_raw_sig \<tau> sig) \<longrightarrow> (type_of o the) (\<tau> k sig) \<noteq> Bty"
  shows   "\<forall>k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig) \<longleftrightarrow> k \<in> keys (to_trans_raw_sig \<tau> sig)"
  using assms
  unfolding to_trans_raw_sig_def to_trans_raw_bit_def keys_def by (auto simp add: zero_fun_def zero_option_def split: option.splits val.splits)
 *)

lemma purge'_trans_post_preserve_non_stuttering_lv:
  fixes \<tau> sig t dly cur_val sign bs
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>'  \<equiv> purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)"
  defines "\<tau>'' \<equiv> trans_post_raw sig (Lv sign bs) (\<sigma> sig) \<tau>' t dly"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  shows "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> sig"
proof -
  have 1: "\<tau>' = combine_trans_bit \<tau>
          (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
               (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))
          sign sig t dly"
    unfolding \<tau>'_def purge_raw'_def by auto
  have "post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig) \<or> 
     \<not> post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig)"
    by auto
  moreover
  { assume "post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig)"
    hence 0: "\<tau>'' = post_raw sig (Lv sign bs) \<tau>' (t + dly)" and "signal_of (\<sigma> sig) \<tau>' sig (t + (dly - 1)) \<noteq> Lv sign bs"
      unfolding \<tau>''_def trans_post_raw_def by auto
    have ?thesis
      unfolding non_stuttering_def 
    proof (rule, rule, rule, rule)
      fix k1 k2
      assume "k1 < k2 \<and> k1 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> k2 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))"
      hence "k1 < k2" and "k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)" and 
        2: "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))" by auto
      have "k2 \<le> t + dly"
      proof (rule ccontr)
        assume "\<not> k2 \<le> t + dly" hence "t + dly < k2" by auto
        hence "\<tau>'' k2 sig = None"
          using `\<tau>'' = post_raw sig (Lv sign bs) \<tau>' (t + dly)` unfolding post_raw_def by auto
        with `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False 
          unfolding to_trans_raw_sig_def keys_def zero_option_def by auto
      qed
      have "k1 \<in> keys (to_trans_raw_sig \<tau>' sig)"
        using `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` unfolding 0 post_raw_def to_trans_raw_sig_def keys_def zero_option_def
        using \<open>k1 < k2\<close> \<open>k2 \<le> t + dly\<close> by auto
      have 3: "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig))"
        using `k2 \<le> t + dly` 0 2 `k1 < k2` unfolding post_raw_def 
        by (metis domIff dom_def dual_order.asym keys_def less_le_trans to_trans_raw_sig_def zero_option_def)
      have "k2 < t \<or> k2 \<ge> t"
        by auto
      moreover
      { assume "k2 < t"
        hence "\<tau>'' k2 sig = \<tau>' k2 sig"
          using 0 unfolding post_raw_def by auto
        also have "... = \<tau> k2 sig"
          using 1 `k2 < t` unfolding combine_trans_bit_def Let_def by auto
        finally have "\<tau>'' k2 sig = \<tau> k2 sig"
          by auto
        hence "False"
          by (metis (full_types) \<open>k1 < k2 \<and> k1 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> k2 \<in> keys
          (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))\<close>
          \<open>k2 < t\<close> assms(4) domIff dom_def keys_def less_imp_le_nat to_trans_raw_sig_def
          zero_fun_def zero_option_def)
        hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
          by auto }
      moreover
      { assume "k2 \<ge> t"
        have "dly = 0 \<or> dly \<noteq> 0"
          by auto
        moreover
        { assume "dly = 0"
          hence "k2 = t" 
            using \<open>k2 \<le> t + dly\<close> \<open>t \<le> k2\<close> by linarith
          have "k1 < t"
            using `k1 < k2` `k2 = t` by auto
          hence "\<tau>''  k1 sig = \<tau>' k1 sig"
            using 0 unfolding post_raw_def by auto
          also have "... = \<tau> k1 sig"
            using `k1 < t` unfolding 1 combine_trans_bit_def Let_def by auto
          also have "... = 0"
            using `k1 < t` assms(4) by (auto simp add: zero_fun_def zero_option_def)
          finally have "\<tau>'' k1 sig = 0"
            by auto
          hence "k1 \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
            unfolding to_trans_raw_sig_def keys_def by auto
          with `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` have False
            by auto
          hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
            by auto }
        moreover
        { assume "dly \<noteq> 0"
          have "k2 = t + dly \<or> k2 < t + dly"
            using `k2 \<le> t + dly` by auto
          moreover
          { assume "k2 = t + dly"
            hence "\<tau>'' k2 sig = Some (Lv sign bs)"
              unfolding 0 post_raw_def by auto
            have "t < k1"
            proof (rule ccontr)
              assume "\<not> t < k1" hence "k1 \<le> t" by auto
              hence "\<tau>'' k1 sig = \<tau>' k1 sig"
                using ` dly \<noteq> 0` unfolding 0 post_raw_def by auto
              also have "... = \<tau> k1 sig"
                unfolding 1 combine_trans_bit_def using `k1 \<le> t` by auto
              also have "... = 0"
                using assms(4)  by (simp add: \<open>k1 \<le> t\<close> zero_fun_def)
              finally have "\<tau>'' k1 sig = 0"
                by auto
              with `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False
                by (simp add: keys_def to_trans_raw_sig_def)
            qed
            hence "\<tau>'' k1 sig = \<tau>' k1 sig"
              using `k1 < k2` `k2 = t + dly` unfolding 0 post_raw_def by auto
            have "inf_time (to_trans_raw_sig \<tau>') sig (t + (dly - 1)) = Some k1"
            proof (rule inf_time_someI)
              show "k1 \<in> dom (to_trans_raw_sig \<tau>' sig)"
                using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)`  by (simp add: dom_def keys_def zero_option_def)
            next
              show "k1 \<le> t + (dly - 1)"
                using \<open>k1 < k2\<close> \<open>k2 = t + dly\<close> by linarith
            next
              { fix ta
                assume "ta \<in> dom (to_trans_raw_sig \<tau>' sig)"
                assume "k1 < ta"
                assume "ta \<le> t + (dly - 1)"
                have "ta < k2"
                  using \<open>dly \<noteq> 0\<close> \<open>k2 = t + dly\<close> \<open>ta \<le> t + (dly - 1)\<close> by linarith
                hence "ta \<notin> keys (to_trans_raw_sig \<tau>' sig)"
                  using 3 \<open>k1 < ta\<close> by blast
                with `ta \<in> dom (to_trans_raw_sig \<tau>' sig)` have False
                  by (simp add: dom_def keys_def zero_option_def) }
              thus "\<forall>ta\<in>dom (to_trans_raw_sig \<tau>' sig). ta \<le> t + (dly - 1) \<longrightarrow> ta \<le> k1"
                using leI by blast
            qed
            hence "the (to_trans_raw_sig \<tau>' sig k1) \<noteq> Lv sign bs"
              using `(signal_of (\<sigma> sig) \<tau>' sig (t + (dly - 1)) \<noteq> Lv sign bs)`
              unfolding to_signal_def comp_def by auto
            hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
              by (metis \<open>\<tau>'' k1 sig = \<tau>' k1 sig\<close> \<open>\<tau>'' k2 sig = Some (Lv sign bs)\<close> option.sel to_trans_raw_sig_def) }
          moreover
          { assume "k2 < t + dly"
            hence "\<tau>'' k2 sig = \<tau>' k2 sig"
              using 0 unfolding post_raw_def by auto
            have "t < k2"
            proof (rule ccontr)
              assume "\<not> t < k2" hence "k2 \<le> t" by auto
              hence "\<tau>' k2 sig = \<tau> k2 sig"
                unfolding 1 combine_trans_bit_def by auto
              also have "... = 0"
                using assms  by (simp add: \<open>k2 \<le> t\<close> zero_fun_def)
              finally have "\<tau>'' k2 sig = 0"
                by (simp add: \<open>\<tau>'' k2 sig = \<tau>' k2 sig\<close>)
              with `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False
                by (simp add: keys_def to_trans_raw_sig_def)
            qed
            hence "k2 \<in> keys (to_trans_raw_sig \<tau>' sig)"
              using `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` 
              by (simp add: \<open>\<tau>'' k2 sig = \<tau>' k2 sig\<close> keys_def to_trans_raw_sig_def)
            hence "\<tau>' k2 sig \<noteq> None"
              by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
            hence k2inset: "k2 \<in> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
              using `t < k2` `k2 < t + dly` unfolding 1 combine_trans_bit_def Let_def 
              by (meson dual_order.asym leD)
            hence "\<tau>' k2 sig = Some
                (Lv sign
                  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
              unfolding 1 combine_trans_bit_def Let_def  using \<open>k2 < t + dly\<close> \<open>t < k2\<close> by auto
            hence 4: "(lval_of o the) (\<tau>' k2 sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
              by auto
            have 5: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' k2 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
            proof -
              fix b
              assume "b \<in> set [0 ..< length bs]"
              have "(lval_of o the) (\<tau>' k2 sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
                using 4 by auto
              have *: "b < length (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
                using `b \<in> set [0 ..< length bs]` by auto
              have **: "?complex = bval_of
     (signal_of
       (fst (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       (snd (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       sig k2)"
                unfolding  nth_map[OF *] by auto 
              moreover have "[0 ..< length bs] ! b = b"
                using `b \<in> set [0 ..< length bs]` by auto
              ultimately have "?complex = bval_of 
                (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
                unfolding **  using \<open>b \<in> set [0..<length bs]\<close> 
                by (simp add: val.case_eq_if)
              thus "(lval_of \<circ> the) (\<tau>' k2 sig) ! b = bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
                using 4 by auto
            qed
            have helper: "\<And>f. length (map f [0..<length bs]) \<le> length bs - 0"
              by auto
            have  "k2 \<in> fold (\<union>) (map keys
                   (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig)
                     (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                       [0..<length bs]))) {}"
              using k2inset unfolding map_map[THEN sym] map_snd_zip_take  length_map min.idem length_upt
              take_all[OF helper] by auto
            hence helper2:" k2 \<in> fold (\<union>)
               (map (\<lambda>x. keys
                      (to_trans_raw_sig
                        (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> x sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) sig))
             [0..<length bs]) {}" 
              unfolding map_map comp_def  by auto                   
            obtain b2 where "b2 \<in> set [0..< length bs]" and "k2 \<in> keys (to_trans_raw_sig
                            (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig)"
              using member_fold_union[OF helper2] by auto
            hence purge_neq: "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k2 sig \<noteq> 0"
              unfolding keys_def to_trans_raw_sig_def by auto
            have the_time: "Some k2 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig)) sig (t + dly)" and 
              sig_neq: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t \<noteq> Bv (bs ! b2)" and 
              sig_eq: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig (t + dly) = Bv (bs ! b2)"
              using `t < k2` `k2 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k2` `k2 < t + dly`] 
              by auto
            moreover hence "to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig k2 sig = Some (Bv (bs ! b2))"
              unfolding to_signal_def comp_def to_trans_raw_sig_def 
              by (smt inf_time_some_exists keys_def mem_Collect_eq not_None_eq option.sel
              option.simps(5) zero_option_def)
            ultimately have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k2 sig = Some (Bv (bs ! b2))"
              using `t < k2` `k2 < t + dly` unfolding purge_raw_def Let_def 
              by (smt "3" UnE \<open>k1 < k2\<close> \<open>k2 \<in> keys (to_trans_raw_sig \<tau>' sig)\<close> greaterThanAtMost_iff greaterThanLessThan_iff option.sel override_on_apply_notin)
            hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) 
                            (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k2 = Bv (bs ! b2)"
              using trans_some_signal_of'  by (metis o_apply option.sel )
            hence "(lval_of o the) (\<tau>' k2 sig) ! b2 = bs ! b2"
              using 5[OF `b2 \<in> set [0..< length bs]`] by auto

            have "k1 < t + dly"
              using `k1 < k2` `k2 < t + dly` by auto
            have "t < k1"
            proof (rule ccontr)
              assume "\<not> t < k1" hence "k1 \<le> t" by auto
              hence "\<tau>' k1 sig = \<tau> k1 sig"
                unfolding 1 combine_trans_bit_def by auto
              also have "... = 0"
                using assms  by (simp add: \<open>k1 \<le> t\<close> zero_fun_def)
              finally have "\<tau>' k1 sig = 0"
                by (simp)
              with `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` show False
                by (simp add: keys_def to_trans_raw_sig_def)
            qed
            have "\<tau>' k1 sig \<noteq> None"
              using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` 
              by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
            hence k1inset: "k1 \<in> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
              using `t < k1` `k1 < t + dly` unfolding 1 combine_trans_bit_def Let_def 
              by (meson dual_order.asym leD)
            have  "k1 \<in> fold (\<union>) (map keys
                   (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig)
                     (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                       [0..<length bs]))) {}"
              using k1inset unfolding map_map[THEN sym] map_snd_zip_take  length_map min.idem length_upt
              take_all[OF helper] by auto
            hence k1inset':" k1 \<in> fold (\<union>)
               (map (\<lambda>x. keys
                      (to_trans_raw_sig
                        (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> x sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) sig))
             [0..<length bs]) {}" 
              unfolding map_map comp_def  by auto     
            obtain b1 where "b1 \<in> set [0..< length bs]" and "k1 \<in> keys (to_trans_raw_sig
                            (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (Bv (bs ! b1))) sig)"
              using member_fold_union[OF k1inset'] by auto 
            hence purge_neq: "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (Bv (bs ! b1)) k1 sig \<noteq> 0"
              unfolding keys_def to_trans_raw_sig_def by auto
            have "Some k1 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig)) sig (t + dly)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig t \<noteq> Bv (bs ! b1)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig (t + dly) = Bv (bs ! b1)"
              using `t < k1` `k1 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k1` `k1 < t + dly`] 
              by auto
            have "Some k1 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig)) sig (t + dly)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig t \<noteq> Bv (bs ! b1)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig (t + dly) = Bv (bs ! b1)"
              using `t < k1` `k1 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k1` `k1 < t + dly`] 
              by auto
            hence "\<tau>' k1 sig = Some
                (Lv sign
                  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
              unfolding 1 combine_trans_bit_def Let_def  using \<open>k1 < t + dly\<close> \<open>t < k1\<close> k1inset by auto
            hence 5: "(lval_of o the) (\<tau>' k1 sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
              by auto
            have 6: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' k1 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
            proof -
              fix b
              assume "b \<in> set [0 ..< length bs]"
              have "(lval_of o the) (\<tau>' k1 sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
                using 5 by auto
              have *: "b < length (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
                using `b \<in> set [0 ..< length bs]` by auto
              have **: "?complex = bval_of
     (signal_of
       (fst (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       (snd (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       sig k1)"
                unfolding  nth_map[OF *] by auto 
              moreover have "[0 ..< length bs] ! b = b"
                using `b \<in> set [0 ..< length bs]` by auto
              ultimately have "?complex = bval_of 
                (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
                unfolding **
                using \<open>b \<in> set [0..<length bs]\<close>  by (simp add: val.case_eq_if)
              thus "(lval_of \<circ> the) (\<tau>' k1 sig) ! b = bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
                using 5 by auto
            qed
          
            have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k1 sig = None"
              using `t < k1` `k1 < k2` sig_neq sig_eq the_time unfolding purge_raw_def Let_def
              by (smt Un_iff fun_upd_eqD fun_upd_triv greaterThanLessThan_iff option.sel override_on_apply_in)
            have 7: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k1 = 
                  signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig t"
            proof (intro signal_of_less_ind')
              fix n
              assume "t < n" and "n \<le> k1"
              thus " purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) n sig = 0"
                using `k1 < k2` sig_neq sig_eq the_time unfolding purge_raw_def Let_def
                apply (auto simp add: override_on_def to_trans_raw_bit_def zero_option_def zero_fun_def split: option.splits val.splits intro!: ext)
                   apply (metis linorder_neqE_nat not_le option.sel)
                using \<open>k2 \<le> t + dly\<close> apply linarith
                 apply (metis le_less_trans option.sel)
                using \<open>k1 < t + dly\<close> by linarith
              next
              show "t \<le> k1"
                using `t < k1` by auto
            qed 
            also have "... = signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t "
            proof (rule signal_of_equal_when_trans_equal_upto)
              fix n 
              assume "n \<le> t"
              thus "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) n = to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig n"
                unfolding purge_raw_def Let_def override_on_def 
                by (smt Un_iff \<open>t \<le> k2\<close> greaterThanAtMost_iff greaterThanLessThan_iff leD less_le_trans option.sel the_time)
            qed (auto)
            also have "... \<noteq> Bv (bs ! b2)"
              using sig_neq by auto
            finally have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k1 \<noteq> Bv (bs ! b2)"
              by auto
            moreover have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t  = (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2))"
              apply (rule signal_of_def)
              using assms(4)
              unfolding to_trans_raw_bit_def by (simp add: zero_fun_def zero_option_def)
            ultimately have "(lval_of o the) (\<tau>' k1 sig) ! b2 \<noteq> bs ! b2"
              using 6[OF `b2 \<in> set [0 ..< length bs]`] 
              using "7"
              using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig t = signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t\<close> by auto
            with `(lval_of o the) (\<tau>' k2 sig) ! b2 = bs ! b2` have "\<tau>' k1 sig \<noteq> \<tau>' k2 sig"
              by auto
            moreover have "\<tau>'' k1 sig = \<tau>' k1 sig"
              using 0 `t < k1` `k1 < t + dly` unfolding post_raw_def by auto
            ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
              using `\<tau>'' k2 sig = \<tau>' k2 sig`  unfolding to_trans_raw_sig_def by auto }
          ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
            by auto }
        ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
          by auto }
      ultimately show "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
        by auto 
    next
      have "t + dly \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        unfolding 0 post_raw_def to_trans_raw_sig_def keys_def by (auto simp add: zero_fun_def zero_option_def)
      hence "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<le> t + dly"
        using Least_le  by (simp add: Least_le)
      hence "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly \<or> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) < t + dly"
        by auto
      moreover
      { assume "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly"
        hence "(to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))) = Some (Lv sign bs)"
          using 0 unfolding post_raw_def  by (simp add: to_trans_raw_sig_def)
        have "\<And>n. n < t + dly \<Longrightarrow> to_trans_raw_sig \<tau>'' sig n = 0"
          using `(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly`
            not_less_Least unfolding 0 post_raw_def   by (smt keys_def mem_Collect_eq)
        have "0 < dly \<or> dly = 0"
          by auto
        moreover 
        { assume "0 < dly"
          have "signal_of (\<sigma> sig) \<tau>' sig (t + (dly - 1)) = \<sigma> sig"
            apply (intro signal_of_def)
            using `\<And>n. n < t + dly \<Longrightarrow> to_trans_raw_sig \<tau>'' sig n = 0` 
            unfolding to_trans_raw_sig_def 0 post_raw_def 
          proof -
            fix n :: nat
            assume a1: "n \<le> t + (dly - 1)"
            assume a2: "\<And>n. n < t + dly \<Longrightarrow> (if n = t + dly then \<tau>' n(sig \<mapsto> Lv sign bs) else if t + dly < n then (\<tau>' n)(sig := None) else \<tau>' n) sig = 0"
            have "Suc 0 \<le> dly"
              by (metis (no_types) Suc_leI \<open>0 < dly\<close>)
            then show "\<tau>' n sig = 0"
              using a2 a1 by simp
          qed
          hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
            using \<open>post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig)\<close> \<open>to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Lv sign bs)\<close> by auto }
        moreover
        { assume "dly = 0"
          hence "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t"
            using `(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly` by auto
          have "to_trans_raw_sig \<tau>'' sig t = Some (Lv sign bs)"
            unfolding 0 
            using "0" \<open>(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = t + dly\<close> \<open>dly = 0\<close>
            \<open>to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Lv sign
            bs)\<close> by auto
          have "signal_of (\<sigma> sig) \<tau>' sig (t + (dly - 1)) = signal_of (\<sigma> sig) \<tau>' sig t"
            using `dly = 0` by auto
          also have "... = \<sigma> sig"
            using assms(4) 
            by (metis \<tau>'_def purge_preserve_trans_removal_nonstrict' signal_of_def zero_fun_def)
          finally have "signal_of (\<sigma> sig) \<tau>' sig (t + (dly - 1)) = \<sigma> sig"
            by auto
          hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
            using \<open>post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig)\<close> \<open>to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Lv sign bs)\<close> by auto }
        ultimately have "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
          by auto }
      moreover
      { assume lt: " (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) < t + dly"
        have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<in> keys (to_trans_raw_sig \<tau>'' sig)"
          using LeastI  by (metis \<open>t + dly \<in> keys (to_trans_raw_sig \<tau>'' sig)\<close>)      
        hence "to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<noteq> 0"
          unfolding keys_def by auto
        with lt have "\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig \<noteq> 0"
          unfolding 0 post_raw_def to_trans_raw_sig_def by auto
        have "t < (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))"
        proof (rule ccontr)
          assume "\<not> t < (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))"
          hence " (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<le> t"
            by auto
          hence "\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = 0"
            using assms(4)
            unfolding 1  combine_trans_bit_def Let_def by (auto simp add :zero_fun_def)
          with `\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig \<noteq> 0`
          show False
            unfolding to_trans_raw_sig_def by auto
        qed
        hence "\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig"
          using lt unfolding 0 post_raw_def by auto
        let ?t = "LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        have **: "?t \<in> fold (\<union>)
          (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
            (zip (map (\<lambda>n.  (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig  (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
          using `\<tau>' ?t sig \<noteq> 0` `t < ?t` `?t < t + dly` unfolding 1 combine_trans_bit_def
          using not_le zero_option_def by fastforce
        hence "?t \<in> fold (\<union>) (map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) 
                                       (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig  (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
          unfolding map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt
          using take_all by auto
        hence *: "?t  \<in> fold (\<union>) (map (keys \<circ> ((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))))) [0..<length bs]) {}"
          unfolding map_map by auto
        have "(\<exists>x\<in>set (map (keys \<circ> ((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))))) [0..<length bs]).
                      ?t \<in> x)"
          using member_fold_union[OF *] unfolding empty_iff by auto
        then obtain b where "?t \<in> keys (((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))) b)" and 
          "b \<in> set [0..< length bs]" by auto
        hence "?t \<in>  keys (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) n sig)"
          unfolding comp_def to_trans_raw_sig_def by auto
        hence "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig \<noteq> 0"
          unfolding keys_def by auto
        from purge_raw_neq_0_imp[OF this `t < ?t` `?t < t + dly`]
        have inf_time: " inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) = Some ?t"
          and sig_neq: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b) "
          and sig_eq: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)" 
          by auto
        hence "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig = 
               to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?t sig"
          using `t < ?t` `?t < t + dly` unfolding purge_raw_def Let_def by auto
        also have "... = Some (Bv (bs ! b))"
          using sig_eq inf_time unfolding to_signal_def comp_def 
          by (metis (mono_tags, lifting) \<open>purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma>
          sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) (LEAST k. k \<in> keys (to_trans_raw_sig
          \<tau>'' sig)) sig \<noteq> 0\<close> calculation option.collapse option.simps(5) to_trans_raw_sig_def
          zero_option_def)
        finally have ***: "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig = Some (Bv (bs ! b))"
          by auto
        have "\<tau>' ?t sig = Some
            (Lv sign
              (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
          using ** unfolding 1 combine_trans_bit_def Let_def  using \<open>?t < t + dly\<close> \<open>t < ?t\<close> by auto
        hence 4: "(lval_of o the) (\<tau>' ?t sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
          by auto        
        have 5: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' ?t sig) ! b = 
                  bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                    (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
        proof -
          fix b
          assume "b \<in> set [0 ..< length bs]"
          have "(lval_of o the) (\<tau>' ?t sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
            using 4 by auto
          have *: "b < length (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
            using `b \<in> set [0 ..< length bs]` by auto
          have **: "?complex = bval_of
 (signal_of
   (fst (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
   (snd (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
   sig ?t)"
            unfolding  nth_map[OF *] by auto 
          moreover have "[0 ..< length bs] ! b = b"
            using `b \<in> set [0 ..< length bs]` by auto
          ultimately have "?complex = bval_of 
            (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
            using \<open>b \<in> set [0..<length bs]\<close> unfolding ** by (simp add: val.case_eq_if)
          thus "(lval_of \<circ> the) (\<tau>' ?t sig) ! b = bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) 
                          (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
            using 4 by auto
        qed
        hence h: "(lval_of o the) (\<tau>' ?t sig) ! b = 
          bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) 
              (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
          using `b \<in> set [0..< length bs]` by auto
        have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) 
                (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t = Bv (bs ! b)"
        proof (rule signal_of_intro, rule, rule)
          show "?t \<le> ?t" by auto
        next
          have "to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig 
                                (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Bv (bs ! b))"
            using ***  unfolding to_trans_raw_sig_def by auto
          moreover have "(\<forall>j>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig).
        j \<le> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow> to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig j = None)"
            by auto
          ultimately show " to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Bv (bs ! b)) \<and>
    (\<forall>j>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig).
        j \<le> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow> to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig j = None) \<or>
    (\<forall>i\<le>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig). purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) i sig = None) \<and>
    Bv (bs ! b) = (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))"
            by auto
        qed
        hence "bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t) = bs ! b"
          by auto
        hence "(lval_of o the) (\<tau>' ?t sig) ! b = bs ! b"
          using h by auto
        have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t = (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))"
          apply (intro signal_of_def)
          using assms(4) unfolding to_trans_raw_bit_def  by (simp add: zero_fun_def zero_option_def)
        hence " (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b) \<noteq> bs ! b"
          using sig_neq by auto
        hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
          using \<open>(lval_of \<circ> the) (\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig) ! b =
          bs ! b\<close> \<open>\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys
          (to_trans_raw_sig \<tau>'' sig)) sig\<close> comp_apply to_trans_raw_sig_def 
          apply auto
          subgoal 
          proof -
            assume a1: "\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig"
            assume a2: "\<sigma> sig = the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
            assume a3: "case the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))) of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b"
            assume a4: "\<not> lval_of (the (\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig)) ! b"
            have "Some (Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))) = to_trans_raw_sig \<tau>'' sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig))"
              using a1 by (metis (no_types) \<open>\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = Some (Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))\<close> to_trans_raw_sig_def)
            then have f5: "Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) = \<sigma> sig"
              using a2  by (metis (no_types, lifting) option.sel)
            then have "map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) = lval_of (\<sigma> sig)"
              by (metis (no_types, lifting) val.sel(3))
            then have "Lv sign (lval_of (\<sigma> sig)) = \<sigma> sig"
              using f5 by presburger
            then show False
              using a4 a3 a2 a1 by (metis to_trans_raw_sig_def val.case(2))
          qed
          subgoal
          proof -
            assume a1: "\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig"
            assume a2: "\<sigma> sig = the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
            assume "\<not> (case the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))) of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)"
            assume a3: "bs ! b"
            have "Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) = \<sigma> sig"
              using a2 a1 by (metis (lifting) \<open>\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = Some (Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))\<close> option.sel to_trans_raw_sig_def)
            then have "Lv sign ((lval_of \<circ> the) (\<tau>' (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig)) = \<sigma> sig"
              by (metis (lifting) "4") 
            then show False
              using a3 
              by (metis \<open>(lval_of \<circ> the) (\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig) ! b = bs ! b\<close> \<open>\<not> (case the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))) of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)\<close> a2 val.simps(6))
          qed
          done }
      ultimately have "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
        by auto
      thus "keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {} \<longrightarrow> \<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
        by auto
    qed }
  moreover
  { assume "\<not> post_necessary_raw (dly - 1) \<tau>' t sig (Lv sign bs) (\<sigma> sig)"
    hence 0: "\<tau>'' = preempt_raw sig \<tau>' (t + dly)"
      unfolding \<tau>''_def trans_post_raw_def by auto
    have ?thesis
      unfolding non_stuttering_def
    proof (rule, rule, rule, rule)
      fix k1 k2
      assume "k1 < k2 \<and> k1 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> k2 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))"
      hence "k1 < k2" and "k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)" and 
        2: "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))" by auto
      have "k2 \<le> t + dly"
      proof (rule ccontr)
        assume "\<not> k2 \<le> t + dly" hence "t + dly < k2" by auto
        hence "\<tau>'' k2 sig = None"
          using `\<tau>'' = preempt_raw sig  \<tau>' (t + dly)` unfolding preempt_raw_def by auto
        with `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False 
          unfolding to_trans_raw_sig_def keys_def zero_option_def by auto
      qed
      have "k1 \<in> keys (to_trans_raw_sig \<tau>' sig)"
        using `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` unfolding 0 preempt_raw_def to_trans_raw_sig_def keys_def zero_option_def
        using \<open>k1 < k2\<close> \<open>k2 \<le> t + dly\<close> by auto
      have 3: "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig))"
        using `k2 \<le> t + dly` 0 2 `k1 < k2` unfolding preempt_raw_def 
        by (metis domIff dom_def dual_order.asym keys_def less_le_trans to_trans_raw_sig_def zero_option_def)
      have "k2 < t \<or> k2 \<ge> t"
        by auto
      moreover
      { assume "k2 < t"
        hence "\<tau>'' k2 sig = \<tau>' k2 sig"
          using 0 unfolding preempt_raw_def by auto
        also have "... = \<tau> k2 sig"
          using 1 `k2 < t` unfolding combine_trans_bit_def Let_def by auto
        finally have "\<tau>'' k2 sig = \<tau> k2 sig"
          by auto
        hence "False"
          by (metis (full_types) \<open>k1 < k2 \<and> k1 \<in> keys (to_trans_raw_sig \<tau>'' sig) \<and> k2 \<in> keys
          (to_trans_raw_sig \<tau>'' sig) \<and> (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>'' sig))\<close>
          \<open>k2 < t\<close> assms(4) domIff dom_def keys_def less_imp_le_nat to_trans_raw_sig_def
          zero_fun_def zero_option_def)
        hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
          by auto }
      moreover
      { assume "k2 \<ge> t"
        have "dly = 0 \<or> dly \<noteq> 0"
          by auto
        moreover
        { assume "dly = 0"
          hence "k2 = t" 
            using \<open>k2 \<le> t + dly\<close> \<open>t \<le> k2\<close> by linarith
          have "k1 < t"
            using `k1 < k2` `k2 = t` by auto
          hence "\<tau>''  k1 sig = \<tau>' k1 sig"
            using 0 unfolding preempt_raw_def by auto
          also have "... = \<tau> k1 sig"
            using `k1 < t` unfolding 1 combine_trans_bit_def Let_def by auto
          also have "... = 0"
            using `k1 < t` assms(4) by (auto simp add: zero_fun_def zero_option_def)
          finally have "\<tau>'' k1 sig = 0"
            by auto
          hence "k1 \<notin> keys (to_trans_raw_sig \<tau>'' sig)"
            unfolding to_trans_raw_sig_def keys_def by auto
          with `k1 \<in> keys (to_trans_raw_sig \<tau>'' sig)` have False
            by auto
          hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
            by auto }
        moreover
        { assume "dly \<noteq> 0"
          have "k2 = t + dly \<or> k2 < t + dly"
            using `k2 \<le> t + dly` by auto
          moreover
          { assume "k2 = t + dly"
            hence "\<tau>'' k2 sig = None"
              unfolding 0 preempt_raw_def by auto
            hence False 
              using `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` unfolding keys_def to_trans_raw_sig_def
              by (simp add: zero_option_def)
            hence "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
              by auto }
          moreover
          { assume "k2 < t + dly"
            hence "\<tau>'' k2 sig = \<tau>' k2 sig"
              using 0 unfolding preempt_raw_def by auto
            have "t < k2"
            proof (rule ccontr)
              assume "\<not> t < k2" hence "k2 \<le> t" by auto
              hence "\<tau>' k2 sig = \<tau> k2 sig"
                unfolding 1 combine_trans_bit_def by auto
              also have "... = 0"
                using assms  by (simp add: \<open>k2 \<le> t\<close> zero_fun_def)
              finally have "\<tau>'' k2 sig = 0"
                by (simp add: \<open>\<tau>'' k2 sig = \<tau>' k2 sig\<close>)
              with `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` show False
                by (simp add: keys_def to_trans_raw_sig_def)
            qed
            hence "k2 \<in> keys (to_trans_raw_sig \<tau>' sig)"
              using `k2 \<in> keys (to_trans_raw_sig \<tau>'' sig)` 
              by (simp add: \<open>\<tau>'' k2 sig = \<tau>' k2 sig\<close> keys_def to_trans_raw_sig_def)
            hence "\<tau>' k2 sig \<noteq> None"
              by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
            hence k2inset: "k2 \<in> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
              using `t < k2` `k2 < t + dly` unfolding 1 combine_trans_bit_def Let_def 
              by (meson dual_order.asym leD)
            hence "\<tau>' k2 sig = Some
                (Lv sign
                  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
              unfolding 1 combine_trans_bit_def Let_def  using \<open>k2 < t + dly\<close> \<open>t < k2\<close> by auto
            hence 4: "(lval_of o the) (\<tau>' k2 sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
              by auto
            have 5: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' k2 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                              (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
            proof -
              fix b
              assume "b \<in> set [0 ..< length bs]"
              have "(lval_of o the) (\<tau>' k2 sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k2))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
                using 4 by auto
              have *: "b < length (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
                using `b \<in> set [0 ..< length bs]` by auto
              have **: "?complex = bval_of
     (signal_of
       (fst (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       (snd (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       sig k2)"
                unfolding  nth_map[OF *] by auto 
              moreover have "[0 ..< length bs] ! b = b"
                using `b \<in> set [0 ..< length bs]` by auto
              ultimately have "?complex = bval_of 
                (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
                using \<open>b \<in> set [0..<length bs]\<close> unfolding ** 
                by (simp add: nth_map val.case_eq_if)
              thus "(lval_of o the) (\<tau>' k2 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                              (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k2)"
                using 4 by auto
            qed
            have helper: "\<And>f. length (map f [0..<length bs]) \<le> length bs - 0"
              by auto
            have  "k2 \<in> fold (\<union>) (map keys
                   (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig)
                     (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                       [0..<length bs]))) {}"
              using k2inset unfolding map_map[THEN sym] map_snd_zip_take  length_map min.idem length_upt
              take_all[OF helper] by auto
            hence helper2:" k2 \<in> fold (\<union>)
               (map (\<lambda>x. keys
                      (to_trans_raw_sig
                        (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> x sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) sig))
             [0..<length bs]) {}" 
              unfolding map_map comp_def  by auto                   
            obtain b2 where "b2 \<in> set [0..< length bs]" and "k2 \<in> keys (to_trans_raw_sig
                            (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig)"
              using member_fold_union[OF helper2] by auto
            hence purge_neq: "purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k2 sig \<noteq> 0"
              unfolding keys_def to_trans_raw_sig_def by auto
            have the_time: "Some k2 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig)) sig (t + dly)" and 
              sig_neq: "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t \<noteq> Bv (bs ! b2)" and 
              sig_eq: "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig (t + dly) = Bv (bs ! b2)"
              using `t < k2` `k2 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k2` `k2 < t + dly`] 
              by auto
            moreover hence "to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig k2 sig = Some (Bv (bs ! b2))"
              unfolding to_signal_def comp_def to_trans_raw_sig_def 
              by (smt inf_time_some_exists keys_def mem_Collect_eq not_None_eq option.sel
              option.simps(5) zero_option_def)
            ultimately have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k2 sig = Some (Bv (bs ! b2))"
              using `t < k2` `k2 < t + dly` unfolding purge_raw_def Let_def 
              by (smt "3" UnE \<open>k1 < k2\<close> \<open>k2 \<in> keys (to_trans_raw_sig \<tau>' sig)\<close> greaterThanAtMost_iff greaterThanLessThan_iff option.sel override_on_apply_notin)
            hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k2 = Bv (bs ! b2)"
              using trans_some_signal_of'  by (metis o_apply option.sel )
            hence "(lval_of o the) (\<tau>' k2 sig) ! b2 = bs ! b2"
              using 5[OF `b2 \<in> set [0..< length bs]`] by auto

            have "k1 < t + dly"
              using `k1 < k2` `k2 < t + dly` by auto
            have "t < k1"
            proof (rule ccontr)
              assume "\<not> t < k1" hence "k1 \<le> t" by auto
              hence "\<tau>' k1 sig = \<tau> k1 sig"
                unfolding 1 combine_trans_bit_def by auto
              also have "... = 0"
                using assms  by (simp add: \<open>k1 \<le> t\<close> zero_fun_def)
              finally have "\<tau>' k1 sig = 0"
                by (simp)
              with `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` show False
                by (simp add: keys_def to_trans_raw_sig_def)
            qed
            have "\<tau>' k1 sig \<noteq> None"
              using `k1 \<in> keys (to_trans_raw_sig \<tau>' sig)` 
              by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
            hence k1inset: "k1 \<in> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
              using `t < k1` `k1 < t + dly` unfolding 1 combine_trans_bit_def Let_def 
              by (meson dual_order.asym leD)
            have  "k1 \<in> fold (\<union>) (map keys
                   (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig)
                     (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                       [0..<length bs]))) {}"
              using k1inset unfolding map_map[THEN sym] map_snd_zip_take  length_map min.idem length_upt
              take_all[OF helper] by auto
            hence k1inset':" k1 \<in> fold (\<union>)
               (map (\<lambda>x. keys
                      (to_trans_raw_sig
                        (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> x sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) sig))
             [0..<length bs]) {}" 
              unfolding map_map comp_def  by auto     
            obtain b1 where "b1 \<in> set [0..< length bs]" and "k1 \<in> keys (to_trans_raw_sig
                            (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (Bv (bs ! b1))) sig)"
              using member_fold_union[OF k1inset'] by auto 
            hence purge_neq: "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (Bv (bs ! b1)) k1 sig \<noteq> 0"
              unfolding keys_def to_trans_raw_sig_def by auto
            have "Some k1 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig)) sig (t + dly)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig t \<noteq> Bv (bs ! b1)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig (t + dly) = Bv (bs ! b1)"
              using `t < k1` `k1 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k1` `k1 < t + dly`] 
              by auto
            have "Some k1 = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig)) sig (t + dly)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig t \<noteq> Bv (bs ! b1)" and 
              "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b1)) (to_trans_raw_bit (\<sigma> sig) \<tau> b1 sig) sig (t + dly) = Bv (bs ! b1)"
              using `t < k1` `k1 < t + dly` purge_raw_neq_0_imp[OF purge_neq `t < k1` `k1 < t + dly`] 
              by auto
            hence "\<tau>' k1 sig = Some
                (Lv sign
                  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
              unfolding 1 combine_trans_bit_def Let_def  using \<open>k1 < t + dly\<close> \<open>t < k1\<close> k1inset by auto
            hence 5: "(lval_of o the) (\<tau>' k1 sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
              by auto
            have 6: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' k1 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
            proof -
              fix b
              assume "b \<in> set [0 ..< length bs]"
              have "(lval_of o the) (\<tau>' k1 sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig k1))
                    (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
                using 5 by auto
              have *: "b < length (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
                using `b \<in> set [0 ..< length bs]` by auto
              have **: "?complex = bval_of
     (signal_of
       (fst (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       (snd (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
       sig k1)"
                unfolding  nth_map[OF *] by auto 
              moreover have "[0 ..< length bs] ! b = b"
                using `b \<in> set [0 ..< length bs]` by auto
              ultimately have "?complex = bval_of 
                (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
                using \<open>b \<in> set [0..<length bs]\<close> unfolding **  by (simp add: val.case_eq_if)
              thus "(lval_of o the) (\<tau>' k1 sig) ! b = 
                      bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig k1)"
                using 5 by auto
            qed
          
            have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) k1 sig = None"
              using `t < k1` `k1 < k2` sig_neq sig_eq the_time unfolding purge_raw_def Let_def
              by (smt Un_iff fun_upd_eqD fun_upd_triv greaterThanLessThan_iff option.sel override_on_apply_in)
            have 7: "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k1 = 
                  signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig t"
            proof (intro signal_of_less_ind')
              fix n
              assume "t < n" and "n \<le> k1"
              thus " purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) n sig = 0"
                using `k1 < k2` sig_neq sig_eq the_time unfolding purge_raw_def Let_def
                apply (auto simp add: override_on_def to_trans_raw_bit_def zero_option_def zero_fun_def split: option.splits val.splits intro!: ext)
                apply (metis linorder_neqE_nat not_le option.sel)
                using \<open>k1 < t + dly\<close> apply linarith
                apply (metis le_less_trans option.sel)
                using \<open>k1 < t + dly\<close> by linarith
            next
              show "t \<le> k1"
                using `t < k1` by auto
            qed 
            also have "... = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t "
            proof (rule signal_of_equal_when_trans_equal_upto)
              fix n 
              assume "n \<le> t"
              thus "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2)) n = to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig n"
                unfolding purge_raw_def Let_def override_on_def 
                by (smt Un_iff \<open>t \<le> k2\<close> greaterThanAtMost_iff greaterThanLessThan_iff leD less_le_trans option.sel the_time)
            qed (auto)
            also have "... \<noteq> Bv (bs ! b2)"
              using sig_neq by auto
            finally have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (Bv (bs ! b2))) sig k1 \<noteq> Bv (bs ! b2)"
              by auto
            moreover have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t  = (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2))"
              apply (rule signal_of_def)
              using assms(4)
              unfolding to_trans_raw_bit_def by (simp add: zero_fun_def zero_option_def)
            ultimately have "(lval_of o the) (\<tau>' k1 sig) ! b2 \<noteq> bs ! b2"
              using 6[OF `b2 \<in> set [0 ..< length bs]`] 
              using "7" 
              using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b2)) (purge_raw
              (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs
              ! b2)) (Bv (bs ! b2))) sig t = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow>
              bs ! b2)) (to_trans_raw_bit (\<sigma> sig) \<tau> b2 sig) sig t\<close> by auto
            with `(lval_of o the) (\<tau>' k2 sig) ! b2 = bs ! b2` have "\<tau>' k1 sig \<noteq> \<tau>' k2 sig"
              by auto
            moreover have "\<tau>'' k1 sig = \<tau>' k1 sig"
              using 0 `t < k1` `k1 < t + dly` unfolding preempt_raw_def by auto
            ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
              using `\<tau>'' k2 sig = \<tau>' k2 sig`  unfolding to_trans_raw_sig_def by auto }
          ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
            by auto }
        ultimately have "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
          by auto }
      ultimately show "to_trans_raw_sig \<tau>'' sig k1 \<noteq> to_trans_raw_sig \<tau>'' sig k2"
        by auto 
    next  
      { assume "keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}"
        have lt: "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) < t + dly"
        proof (rule ccontr)
          assume "\<not> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) < t + dly"
          hence atmost: "t + dly \<le> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))"
            by auto
          have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<in> keys (to_trans_raw_sig \<tau>'' sig)"
            using `keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}`  by (meson LeastI all_not_in_conv)
          hence "to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<noteq> 0"
            unfolding keys_def by auto
          moreover have "to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = 0"
            using atmost unfolding 0 to_trans_raw_sig_def preempt_raw_def by (auto simp add: zero_option_def)
          ultimately show False
            by auto
        qed
        have "(LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<in> keys (to_trans_raw_sig \<tau>'' sig)"
          using `keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {}`  by (meson LeastI all_not_in_conv)      
        hence "to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<noteq> 0"
          unfolding keys_def by auto
        with lt have "\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig \<noteq> 0"
          unfolding 0 preempt_raw_def to_trans_raw_sig_def by auto
        have "t < (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))"
        proof (rule ccontr)
          assume "\<not> t < (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig))"
          hence " (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<le> t"
            by auto
          hence "\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = 0"
            using assms(4)
            unfolding 1  combine_trans_bit_def Let_def by (auto simp add :zero_fun_def)
          with `\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig \<noteq> 0`
          show False
            unfolding to_trans_raw_sig_def by auto
        qed
        hence "\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig"
          using lt unfolding 0 preempt_raw_def by auto
        let ?t = "LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)"
        have **: "?t \<in> fold (\<union>)
          (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
            (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
          using `\<tau>' ?t sig \<noteq> 0` `t < ?t` `?t < t + dly` unfolding 1 combine_trans_bit_def
          using not_le zero_option_def by force
        hence "?t \<in> fold (\<union>) (map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
          unfolding map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt
          using take_all by auto
        hence *: "?t  \<in> fold (\<union>) (map (keys \<circ> ((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))))) [0..<length bs]) {}"
          unfolding map_map by auto
        have "(\<exists>x\<in>set (map (keys \<circ> ((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))))) [0..<length bs]).
                      ?t \<in> x)"
          using member_fold_union[OF *] unfolding empty_iff by auto
        then obtain b where "?t \<in> keys (((\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))) b)" and 
          "b \<in> set [0..< length bs]" by auto
        hence "?t \<in>  keys (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) n sig)"
          unfolding comp_def to_trans_raw_sig_def by auto
        hence "purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig \<noteq> 0"
          unfolding keys_def by auto
        from purge_raw_neq_0_imp[OF this `t < ?t` `?t < t + dly`]
        have inf_time: " inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly) = Some ?t"
          and sig_neq: "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig t \<noteq> Bv (bs ! b) "
          and sig_eq: "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (t + dly) = Bv (bs ! b)" 
          by auto
        hence "purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig = 
               to_trans_raw_bit (\<sigma> sig)  \<tau> b sig ?t sig"
          using `t < ?t` `?t < t + dly` unfolding purge_raw_def Let_def by auto
        also have "... = Some (Bv (bs ! b))"
          using sig_eq inf_time unfolding to_signal_def comp_def 
          by (metis (mono_tags, lifting) \<open>purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma>
          sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) (LEAST k. k \<in> keys
          (to_trans_raw_sig \<tau>'' sig)) sig \<noteq> 0\<close> calculation option.collapse option.simps(5)
          to_trans_raw_sig_def zero_option_def)
        finally have ***: "purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?t sig = Some (Bv (bs ! b))"
          by auto
        have "\<tau>' ?t sig = Some
            (Lv sign
              (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
          using ** unfolding 1 combine_trans_bit_def Let_def  using \<open>?t < t + dly\<close> \<open>t < ?t\<close> by auto
        hence 4: "(lval_of o the) (\<tau>' ?t sig) =  (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))"
          by auto        
        have 5: "\<And>b. b \<in> set [0..< length bs] \<Longrightarrow> (lval_of o the) (\<tau>' ?t sig) ! b = 
                  bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
        proof -
          fix b
          assume "b \<in> set [0 ..< length bs]"
          have "(lval_of o the) (\<tau>' ?t sig) ! b = (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig ?t))
                (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) ! b" (is "_ = ?complex")
            using 4 by auto
          have *: "b < length (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
            using `b \<in> set [0 ..< length bs]` by auto
          have **: "?complex = bval_of
  (signal_of
   (fst (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
   (snd (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) 
             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) ! b))
   sig ?t)"
            unfolding  nth_map[OF *] by auto 
          moreover have "[0 ..< length bs] ! b = b"
            using `b \<in> set [0 ..< length bs]` by auto
          ultimately have "?complex = bval_of 
            (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
            using \<open>b \<in> set [0..<length bs]\<close> unfolding **  by (simp add: val.case_eq_if)
          thus " (lval_of o the) (\<tau>' ?t sig) ! b = bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
            using 4 by auto
        qed
        hence h: "(lval_of o the) (\<tau>' ?t sig) ! b = 
          bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t)"
          using `b \<in> set [0..< length bs]` by auto
        have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?t = Bv (bs ! b)"
        proof (rule signal_of_intro, rule, rule)
          show "?t \<le> ?t" by auto
        next
          have "to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) = Some (Bv (bs ! b))"
            using ***  unfolding to_trans_raw_sig_def by auto
          moreover have "(\<forall>j>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig).
        j \<le> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow> to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (lval_of (\<sigma> sig) ! b)) (Bv (bs ! b))) sig j = None)"
            by auto
          ultimately show " to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig
     (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) =
    Some (Bv (bs ! b)) \<and>
    (\<forall>j>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig).
        j \<le> (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) \<longrightarrow>
        to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig j = None) \<or>
    (\<forall>i\<le>LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig). purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) i sig = None) \<and>
    Bv (bs ! b) = Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)"
            by auto
        qed
        hence "bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))(Bv (bs ! b))) sig ?t) = bs ! b"
          by auto
        hence "(lval_of o the) (\<tau>' ?t sig) ! b = bs ! b"
          using h by auto
        have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t = (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))"
          apply (intro signal_of_def)
          using assms(4) unfolding to_trans_raw_bit_def  by (simp add: zero_fun_def zero_option_def)
        hence "(case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b) \<noteq> bs ! b"
          using sig_neq by auto
        hence "\<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
        proof -
          { assume "Lv sign ((lval_of \<circ> the) (\<tau>'' (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig)) \<noteq> the (\<tau>'' (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig)"
            moreover
            { assume "map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case the (to_trans_raw_sig \<tau>'' sig (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig))) of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) \<noteq> (lval_of \<circ> the) (\<tau>'' (LEAST n. n \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig)"
              then have ?thesis
                by (metis "4" \<open>\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig\<close>) (* > 1.0 s, timed out *) }
            ultimately have ?thesis
              by (simp add: \<open>\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = Some (Lv sign (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig)  \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))\<close> \<open>\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig\<close>) }
          then show ?thesis
            by (metis \<open>(case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b) \<noteq> bs ! b\<close> \<open>(lval_of \<circ> the) (\<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig) ! b = bs ! b\<close> \<open>\<tau>'' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig = \<tau>' (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)) sig\<close> to_trans_raw_sig_def val.simps(6))
        qed }
      thus "keys (to_trans_raw_sig \<tau>'' sig) \<noteq> {} \<longrightarrow> \<sigma> sig \<noteq> the (to_trans_raw_sig \<tau>'' sig (LEAST k. k \<in> keys (to_trans_raw_sig \<tau>'' sig)))"
        by auto
    qed }
  ultimately show ?thesis
    by auto
qed

lemma purge'_trans_post_preserve_non_stuttering:
  fixes \<tau> sig t dly cur_val
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>'  \<equiv> purge_raw' \<tau> t dly sig (\<sigma> sig) cur_val"
  defines "\<tau>'' \<equiv> trans_post_raw sig cur_val (\<sigma> sig) \<tau>' t dly"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  shows "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> sig"
  using purge'_trans_post_preserve_non_stuttering_bv purge'_trans_post_preserve_non_stuttering_lv
  by (metis \<tau>''_def \<tau>'_def assms(1) assms(4) val.exhaust)
    
lemma post_raw_preserves_non_stuttering:
  fixes dly t val
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  defines "\<tau>' \<equiv> post_raw sig val \<tau> (t + dly)"
  assumes "post_necessary_raw (dly-1) \<tau> t sig val (\<sigma> sig)"
  assumes "\<forall>n \<le> t. \<tau> n = 0"
  assumes "0 < dly"
  shows   "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> sig"
proof -
  have cases: "(\<exists>i val'. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None)) \<or>
               (\<forall>i\<le>t + (dly - 1). \<tau> i sig = None) \<and> val \<noteq> \<sigma> sig"
    using assms(3) unfolding post_necessary_raw_correctness2 by auto
  { fix k1 k2
    assume "k1 \<in> keys (to_trans_raw_sig \<tau>' sig)" and "k2 \<in> keys (to_trans_raw_sig \<tau>' sig)"
    assume "k1 < k2"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau>' sig)"
    have "k2 \<le> t + dly"
      using `k2 \<in> keys (to_trans_raw_sig \<tau>' sig)` unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def
    proof -
      assume "k2 \<in> keys (\<lambda>n. (if n = t + dly then \<tau> n(sig \<mapsto> val) else if t + dly < n then (\<tau> n)(sig := None) else \<tau> n) sig)"
      then have "k2 \<in> {n. (if n = t + dly then \<tau> n(sig \<mapsto> val) else if t + dly < n then (\<tau> n)(sig := None) else \<tau> n) sig \<noteq> 0}"
        by (simp add: keys_def)
      then show ?thesis
        using leI zero_option_def by fastforce
    qed
    hence "k2 = t + dly \<or> k2 < t + dly"
      by auto
    moreover
    { assume "k2 = t + dly"
      hence "to_trans_raw_sig \<tau>' sig k2 = Some val"
        unfolding \<tau>'_def post_raw_def to_trans_raw_sig_def by auto
      consider (case1) "(\<exists>i val'. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None))"
             | (case2) "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> \<tau> i sig = None) \<and> val \<noteq> \<sigma> sig"
        using cases by auto
      hence "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
      proof (cases)
        case case1
        then obtain i val' where "i\<ge>t" and "i \<le> t + (dly-1)" and "\<tau> i sig = Some val'" and "val' \<noteq> val"
          "\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None"
          by (metis assms(4) nat_le_linear option.distinct(1) zero_fun_def zero_option_def)
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
              using `i \<le> t + (dly-1)` `\<tau> i sig = Some val'`
              by (intro exI[where x="i"])(metis (no_types, hide_lams) One_nat_def Suc_diff_1
              add.right_neutral add_Suc_right assms(4) diff_is_0_eq' less_Suc_eq_le nat_le_linear
              not_le option.distinct(1) zero_fun_def zero_option_def)
            with * have False by auto }
          ultimately show False by auto
        qed
        thus "to_trans_raw_sig \<tau>' sig k1 \<noteq> to_trans_raw_sig \<tau>' sig k2"
          using `i = k1` `\<tau> i sig = Some val'` `to_trans_raw_sig \<tau>' sig k2 = Some val`
          by (metis \<open>k1 < k2\<close> \<open>k2 = t + dly\<close> \<open>val' \<noteq> val\<close> \<tau>'_def add_less_same_cancel1
          less_imp_add_positive not_less_zero option.sel post_raw_def to_trans_raw_sig_def)
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
    { assume "(\<exists>i val'. i \<le> t + (dly - 1) \<and> \<tau> i sig = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + (dly - 1) \<longrightarrow> \<tau> j sig = None))"
      then obtain i val' where "i \<ge> t" and "i \<le> t + (dly - 1)" and "\<tau> i sig = Some val'" and
        "\<forall>j>i. j < t + (dly - 1) \<longrightarrow> \<tau> j sig = None"
        by (metis assms(4) nat_le_linear nat_less_le option.distinct(1) zero_fun_def zero_option_def)
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
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "cs = Bassign_trans sig e dly"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bcase x1 x2)
  then show ?case  by force
next
  case (Bassign_trans sig e dly)
  obtain x where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b x"
    by (meson Bassign_trans.prems(2) seq_cases_trans)
  hence \<tau>'_def: "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
    using Bassign_trans.prems(2) beval_raw_deterministic by (metis seq_cases_trans)
  have prev_zero: "\<And>n. n < t \<Longrightarrow> to_trans_raw_sig \<tau> s n = 0"
    using Bassign_trans(3) unfolding to_trans_raw_sig_def
    by (auto simp add: zero_fun_def zero_option_def)
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
    have "post_necessary_raw (dly-1) \<tau> t sig x (\<sigma> sig) \<or>
          \<not> post_necessary_raw (dly-1) \<tau> t sig x (\<sigma> sig)" by auto
    moreover
    { assume notnec: "\<not> post_necessary_raw (dly-1) \<tau> t sig x (\<sigma> sig)"
      have look: " \<tau>' = preempt_raw sig ( \<tau>) (t + dly)"
        using notnec unfolding \<tau>'_def trans_post_raw_def by auto
      hence ?case
        using preempt_raw_preserves_non_stuttering[OF Bassign_trans(1)]  by (simp add: \<open>sig = s\<close>) }
    moreover
    { assume nec: "post_necessary_raw (dly-1) \<tau> t sig x (\<sigma> sig)"
      hence lookup: "\<tau>' = post_raw sig x \<tau> (t + dly)"
        unfolding \<tau>'_def by (auto simp add: trans_post_raw_def)
      have "0 < dly \<or> dly = 0"
        by auto
      moreover
      { assume "0 < dly "
        hence ?case
          using post_raw_preserves_non_stuttering[OF Bassign_trans(1)]
          using Bassign_trans.prems(3) \<open>0 < dly\<close> \<open>sig = s\<close>  using lookup nec by blast }
      moreover
      { assume "dly = 0"
        hence nec': "post_necessary_raw 0 \<tau> t sig x (\<sigma> sig)" and lookup': "\<tau>' = post_raw sig x \<tau> t"
          using nec lookup by auto
        have keys': "keys (to_trans_raw_sig \<tau>' s) = {t}"
        proof 
          { fix k
            assume "k \<in> keys (to_trans_raw_sig \<tau>' s)"
            hence "to_trans_raw_sig \<tau>' s k \<noteq> 0"
              unfolding keys_def by auto
            have "\<not> k < t"
            proof (rule ccontr)
              assume "\<not> \<not> k < t" hence "k < t" by auto
              hence "to_trans_raw_sig \<tau>' s k = 0"
                using prev_zero unfolding lookup' post_raw_def by (simp add: to_trans_raw_sig_def)
              with `to_trans_raw_sig \<tau>' s k \<noteq> 0` show False by auto
            qed
            moreover have "\<not> k > t"
            proof (rule ccontr)
              assume "\<not> \<not> k > t" hence "k > t" by auto
              hence "to_trans_raw_sig \<tau>' s k = 0"
                unfolding lookup' post_raw_def
              proof -
                have "k \<noteq> t"
                  using \<open>t < k\<close> by blast
              then show "to_trans_raw_sig (\<lambda>n. if n = t then \<tau> n(sig \<mapsto> x) else if t < n then (\<tau> n)(sig := None) else \<tau> n) s k = 0"
                by (simp add: \<open>sig = s\<close> \<open>t < k\<close> to_trans_raw_sig_def zero_option_def)
              qed
              with `to_trans_raw_sig \<tau>' s k \<noteq> 0` show False 
                by auto
            qed
            ultimately have "k = t"
              by auto }
          thus "keys (to_trans_raw_sig \<tau>' s) \<subseteq> {t}"
            by auto
          have "t \<in> keys (to_trans_raw_sig \<tau>' s)"
            unfolding lookup' post_raw_def 
            by (simp add: \<open>sig = s\<close> keys_def to_trans_raw_sig_def zero_option_def)
          thus "{t} \<subseteq> keys (to_trans_raw_sig \<tau>' s)"
            by auto
        qed
        have least: "(LEAST k. k \<in> {t}) = t"
          by (meson LeastI_ex singleton_iff)
        have "(\<exists>i val'. i \<le> t \<and> \<tau> i sig = Some val' \<and> val' \<noteq> x \<and> (\<forall>j>i. j \<le> t \<longrightarrow> \<tau> j sig = None)) \<or> (\<forall>i\<le>t. \<tau> i sig = None) \<and> x \<noteq> \<sigma> sig"
          using nec' unfolding post_necessary_raw_correctness2 by auto
        hence "(\<forall>i\<le>t. \<tau> i sig = None) \<and> x \<noteq> \<sigma> sig"
          by (metis Bassign_trans.prems(3) add.right_neutral option.distinct(1) zero_fun_def
          zero_option_def)
        hence " \<sigma> s \<noteq> the (to_trans_raw_sig \<tau>' s (LEAST k. k \<in> {t}))"
          unfolding lookup' post_raw_def least to_trans_raw_sig_def \<open>sig = s\<close> by auto
        hence ?case
          unfolding non_stuttering_def keys' by blast }
      ultimately have ?case by auto }
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
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay cs"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction rule: b_seq_exec.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  hence *: "non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using nonneg_delay.simps(2) by blast
  have "b_seq_exec t \<sigma> \<gamma> \<theta> def ss2 \<tau>'' \<tau>'"
    by (simp add: "2.hyps"(2))
  moreover have "\<And>n. n < t \<Longrightarrow> \<tau>'' n = 0"
    using "2.hyps"(1) "2.prems"(2) b_seq_exec_preserve_trans_removal less_imp_le_nat by blast
  ultimately show ?case
    by (metis "*" "2.IH"(2) "2.hyps"(1) "2.prems"(2) "2.prems"(3) \<open>\<And>n. n < t \<Longrightarrow> \<tau>'' n = 0\<close>
    nonneg_delay.simps(2) nonneg_delay_same order.not_eq_order_implies_strict)
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case
    using nonneg_delay.simps(3) by blast
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case
    using nonneg_delay.simps(3) by blast
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case
    by (meson b_seq_exec.intros(5) trans_post_preserves_non_stuttering)
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence \<tau>'_def': "\<tau>' = trans_post_raw sig x (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) x) t dly"
    using 6  by (simp add: inr_post_raw'_def)
  let ?\<tau> = "purge_raw' \<tau> t dly sig (\<sigma> sig) x"
  have "s = sig \<or> s \<noteq> sig"
    by auto
  moreover
  { assume "s \<noteq> sig"
    hence "\<And>n. to_trans_raw_sig \<tau>' s n = to_trans_raw_sig \<tau> s n"
      using \<tau>'_def'
      by (metis "6.hyps"(2) inr_post_raw_does_not_affect_other_sig' to_trans_raw_sig_def)
    hence "to_trans_raw_sig \<tau>' s = to_trans_raw_sig \<tau> s"
      by blast
    hence ?case
      using 6 unfolding non_stuttering_def Let_def by auto }
  moreover
  { assume "s = sig"
    moreover have 3: "\<And>n. n \<le> t \<Longrightarrow> ?\<tau> n = 0"
      by (simp add: "6.prems"(2) purge_preserve_trans_removal_nonstrict')
    obtain cs2 where cs2_def: "cs2 = Bassign_trans sig e dly"
      by auto
    hence 2: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, ?\<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using \<tau>'_def' by (meson "6.hyps"(1) b_seq_exec.intros(5))
    hence ?case
      using "6.prems"(1) "6.prems"(2)  \<tau>'_def' calculation
      purge'_trans_post_preserve_non_stuttering by metis }
  ultimately show ?case
    by auto
qed auto

text \<open>end of non stuttering\<close>

text \<open>The type @{typ "'signal assn"} represents a predicate over a worldline, i.e., a property
about a worldline. The pre- and post-condition of a VHDL sequential statement will be of this type.\<close>

definition state_of_world :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal state" where
  "state_of_world w t = (\<lambda>s. snd w s t)"

definition event_of_world :: "'signal worldline_init  \<Rightarrow> nat \<Rightarrow> 'signal event" where
  "event_of_world w t = (if t = 0 then {s :: 'signal. snd w s t \<noteq> fst w s} else
                                       {s :: 'signal. snd w s t \<noteq> snd w s (t - 1)})"

definition beh_of_world_raw :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "beh_of_world_raw w t = (\<lambda>t'. if t' < t then (\<lambda>s. Some (snd w s t')) else Map.empty)"

inductive beval_world_raw :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
  where
  " state_of_world w t = \<sigma> \<Longrightarrow> event_of_world w t = \<gamma> \<Longrightarrow> derivative_hist_raw w t = \<theta> \<Longrightarrow>
    t, \<sigma>, \<gamma>, \<theta>, (fst w) \<turnstile> exp \<longrightarrow>\<^sub>b x \<Longrightarrow> beval_world_raw w t exp x"

inductive_cases beval_world_raw_cases [elim!]: "beval_world_raw w t exp x"

lemma beval_world_raw_deterministic:
  assumes "beval_world_raw w t exp x1"
  assumes "beval_world_raw w t exp x2"
  shows "x2 = x1"
  using assms(1) assms(2) beval_raw_deterministic beval_world_raw_cases by blast

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
values, i.e., @{term "Bv False :: val"}. The expression for else-statement in @{term "event_of_world"}
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
Null: "\<turnstile>\<^sub>t {P} Bnull {P}"

| Assign: "\<turnstile>\<^sub>t {\<lambda>w . (\<exists>x. beval_world_raw w t exp x \<and> P (w[sig, t + dly := x]))} Bassign_trans sig exp dly {P}"

| AssignI: "\<turnstile>\<^sub>t {\<lambda>w . (\<exists>x. beval_world_raw w  t exp x \<and> P (worldline_inert_upd2 w sig t dly x))} Bassign_inert sig exp dly {P}"

| Comp: "\<lbrakk> \<turnstile>\<^sub>t {P} s1 {Q}; \<turnstile>\<^sub>t {Q} s2 {R}\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P} Bcomp s1 s2 {R}"

| If: " \<turnstile>\<^sub>t {\<lambda>w . P w  \<and> (\<exists>x. beval_world_raw w  t g x \<and>   bval_of x)} s1 {Q} \<Longrightarrow>
        \<turnstile>\<^sub>t {\<lambda>w . P w  \<and> (\<exists>x. beval_world_raw w  t g x \<and> \<not> bval_of x)} s2 {Q} \<Longrightarrow>
        \<turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}"

| Conseq: "\<lbrakk>\<forall>w . P' w  \<longrightarrow> P w ; \<turnstile>\<^sub>t {P} s {Q}; \<forall>w . Q w  \<longrightarrow> Q' w \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} s {Q'}"

| Bcase_empty_choices: "\<turnstile>\<^sub>t {P} Bcase exp [] {P}"

| Bcase_others: "\<turnstile>\<^sub>t {P} ss {Q} \<Longrightarrow> \<turnstile>\<^sub>t {P} Bcase exp ((Others, ss) # choices) {Q}"

| Bcase_if: "\<turnstile>\<^sub>t {\<lambda>w. P w \<and> (\<exists>x. beval_world_raw w t exp x \<and> beval_world_raw w t exp' x)} ss {Q}
  \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>w. P w \<and> (\<exists>x x'. beval_world_raw w t exp x \<and> beval_world_raw w t exp' x' \<and> x \<noteq> x')} Bcase exp choices {Q}
  \<Longrightarrow> \<turnstile>\<^sub>t {P} Bcase exp ( (Explicit exp', ss) # choices) {Q}"

text \<open>The inductive definition @{term "seq_hoare"} is similar to the inductive definition @{term
"hoare"} in @{theory_text "Hoare"}. Rules other than @{thm "Assign"} and @{thm "AssignI"} are
standard; we explain those two only here. As can be seen, the construct @{term "worldline_upd"} and
@{term "worldline_inert_upd"} are designed for the purpose of defining the axiomatic semantics
of VHDL. We show how it makes sense later in the soundness property.\<close>

inductive_cases seq_hoare_ic: "\<turnstile>\<^sub>t {P} s {Q}"

inductive_cases seq_hoare_cases_null [elim!]: "\<turnstile>\<^sub>t {P} Bnull {Q}" and
                seq_hoare_cases_assign : "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}" and
                seq_hoare_cases_assign_inert : "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}" and
                seq_hoare_cases_comp : "\<turnstile>\<^sub>t {P} Bcomp s1 s2 {Q}" and
                seq_hoare_cases_if : "\<turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}" and
                seq_hoare_cases_bcase : "\<turnstile>\<^sub>t {P} Bcase exp choices {Q}"

lemma BnullE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bnull"
  shows "\<forall>w . P w  \<longrightarrow> Q w "
  using assms
  by (induction rule:seq_hoare.induct, auto)

lemma BnullE':
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<forall>w . P w  \<longrightarrow> Q w "
  by (simp add: BnullE)

lemma BassignE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>w . P w  \<longrightarrow> (\<exists>x. beval_world_raw w t exp x \<and> Q (w[sig, t + dly := x]))"
  using assms
proof (induction rule:seq_hoare.induct)
  case (Conseq P' P t s Q Q')
  then show ?case by metis
qed (auto)

lemma BassignE2:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>w  x. P w  \<and> beval_world_raw w t exp x \<longrightarrow> Q (w[sig, t + dly := x])"
  using BassignE[OF assms] beval_world_raw_deterministic by metis

lemma Bassign_inertE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> (\<exists>x. beval_world_raw w t exp x \<and> Q (worldline_inert_upd2 w sig t dly x))"
  using assms
proof (induction rule: seq_hoare.induct)
  case (Conseq P' P t s Q Q')
  then show ?case by  metis
qed auto

lemma Bassign_inertE2:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>w x. P w \<and> beval_world_raw w t exp x \<longrightarrow> Q (worldline_inert_upd2 w sig t dly x)"
  using Bassign_inertE[OF assms] beval_world_raw_deterministic by metis

lemma BcompE:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile>\<^sub>t {P} s1 {Q} \<and> \<turnstile>\<^sub>t {Q} s2 {R}"
  using assms
proof (induction rule:seq_hoare.induct)
  case (Comp t P s1 Q s2 R)
  then show ?case by blast
next
  case (Conseq P' P t s Q Q')
  then show ?case
    by (metis seq_hoare.Conseq)
qed auto

lemmas [simp] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If
                seq_hoare.Bcase_empty_choices seq_hoare.Bcase_if seq_hoare.Bcase_others
lemmas [intro!] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If
                  seq_hoare.Bcase_empty_choices seq_hoare.Bcase_if seq_hoare.Bcase_others

lemma strengthen_pre:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P'} s {Q}"
  using assms by (blast intro: Conseq)

lemma weaken_post:
  assumes "\<forall>w. Q w \<longrightarrow> Q' w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P} s {Q'}"
  using assms by (blast intro: Conseq)

lemma Assign':
  assumes "\<forall>w. P w \<longrightarrow> (\<exists>x. beval_world_raw w t exp x \<and> Q (worldline_upd w sig (t + dly) x))"
  shows "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  using assms by (simp add: strengthen_pre)

definition
seq_hoare_valid :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ {(1_)}/ (_)/ {(1_)}" 50)
where "\<Turnstile>\<^sub>t {P} s {Q} \<longleftrightarrow>  (\<forall>\<sigma> \<tau> \<gamma> \<theta> \<tau>' w w' def .  context_invariant t \<sigma> \<gamma> \<theta> def \<tau>
                                            \<and> (\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s)
                                            \<and> (\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s)
                                            \<and>  w = worldline_raw t \<sigma> \<theta> def \<tau>
                                            \<and>  P w
                                            \<and> (t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s, \<tau>> \<longrightarrow>\<^sub>s \<tau>')
                                            \<and>  w' = worldline_raw t \<sigma> \<theta> def \<tau>' \<longrightarrow> Q w')"

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
  shows   "\<Turnstile>\<^sub>t {P} Bcomp s1 s2 {R}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a trans_raw"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline_init"
  fix def
  assume "context_invariant t \<sigma> \<gamma> \<theta> def \<tau> \<and> All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>) \<and> All (non_stuttering (to_trans_raw_sig \<theta>) def) \<and>
          w = worldline_raw t \<sigma> \<theta> def \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and "w = worldline_raw t \<sigma> \<theta> def \<tau>" and "P w" and "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    and "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    and "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' " and 2: "w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
    by auto
  then obtain \<tau>'' where 0: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and 1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    using seq_cases_bcomp by blast
  define w'' where "w'' = worldline_raw t \<sigma> \<theta> def \<tau>''"
  hence "Q w''"
    using `\<Turnstile>\<^sub>t {P} s1 {Q}` unfolding seq_hoare_valid_def
    using \<open>P w\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> \<open>w = worldline_raw t \<sigma> \<theta> def \<tau>\<close>
    \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close>
    by blast
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` 0] assms(3)
    by auto
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  proof -
    have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
      using b_seq_exec_preserves_non_stuttering[OF 0] `All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)`
      `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` assms(3)  by (simp add: context_invariant_def)
    thus ?thesis
      using b_seq_exec_preserves_non_stuttering[OF 1]
      `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` assms(3)
      by (meson calculation context_invariant_def nonneg_delay.simps(2))
  qed
  ultimately show "R w'"
    using `\<Turnstile>\<^sub>t {Q} s2 {R}` `w'' = worldline_raw t \<sigma> \<theta> def \<tau>''` `Q w''` 1 2 unfolding seq_hoare_valid_def
    by (metis (full_types, hide_lams) "0" \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau> \<and> All (non_stuttering
    (to_trans_raw_sig \<tau>) \<sigma>) \<and> All (non_stuttering (to_trans_raw_sig \<theta>) def) \<and> w = worldline_raw t \<sigma> \<theta> def \<tau> \<and> P w \<and> t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bcomp s1 s2 , \<tau>>
    \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> def \<tau>'\<close> assms(3) b_seq_exec_preserves_non_stuttering
    context_invariant_def nonneg_delay.simps(2))
qed

lemma Bnull_sound:
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bnull {Q}"
  by (auto dest!: BnullE' simp add: seq_hoare_valid_def)

lemma state_of_world:
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
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
  assumes "beval_raw t \<sigma> \<gamma> \<theta> def exp x"
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "beval_raw t \<sigma> \<gamma> (beh_of_world_raw w t) def exp x"
  using assms
proof (induction rule: beval_raw.inducts)
  case (4 t \<sigma> \<gamma> \<theta> def sig n)
  have "t , \<sigma> , \<gamma> , (beh_of_world_raw w t), def \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b (signal_of (def sig) (beh_of_world_raw w t) sig (t - n))"
    by (meson beval_raw.intros(4))
  have *: "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) \<theta> sig (t - n))"
    by (meson beval_raw.intros(4))
  have "0 < n \<and> 0 < t \<or> (t \<noteq> 0 \<and> n = 0) \<or> t = 0"
    by auto
  moreover
  { assume "0 < n \<and> 0 < t"
    hence " (beh_of_world_raw w t) (t - n) = Some \<circ> (\<lambda>s. snd w s (t - n))"
      unfolding beh_of_world_raw_def comp_def by auto
    hence "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = snd w sig (t - n)"
      by (auto dest!:trans_some_signal_of)
    also have "... = signal_of (def sig) \<theta> sig (t - n)"
      using `0 < n \<and> 0 < t` unfolding 4 worldline_raw_def by auto
    hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) \<theta> sig (t - n))"
      using * by auto
    hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) (beh_of_world_raw w t) sig (t - n))"
      using \<open>snd w sig (t - n) = signal_of (def sig) \<theta> sig (t - n)\<close> calculation by auto
    hence ?case
      using \<open>t , \<sigma> , \<gamma> , beh_of_world_raw w t, def \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b signal_of (def sig)
      (beh_of_world_raw w t) sig (t - n)\<close> \<open>snd w sig (t - n) = signal_of (def sig) \<theta> sig (t - n)\<close>
      calculation by auto }
  moreover
  { assume "t \<noteq> 0 \<and> n = 0 \<or> t = 0"
    moreover
    { assume "t = 0"
      hence "t - n = 0" by auto
      have "beh_of_world_raw w t = 0" unfolding `t = 0`
        by (auto simp add: beh_of_world_raw_def zero_fun_def zero_option_def)
      hence "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) 0 sig 0"
        unfolding `t - n = 0` by auto
      also have "... = def sig"
        using signal_of_empty[of "def sig" "sig" "0"] by auto
      finally have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = def sig"
        by auto
      have "\<theta> = 0"
        using 4 unfolding `t = 0` by (auto simp add: zero_fun_def)
      hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) \<theta> sig 0)"
        using `t - n = 0` "*" by auto
      also have "... = def sig"
        unfolding `\<theta> = 0` using signal_of_empty[of "def sig"] by metis
      finally have "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (def sig)"
        by auto
      hence ?case
        using `signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = def sig`
        by (simp add: \<open>\<theta> = 0\<close> \<open>beh_of_world_raw w t = 0\<close>) }
    moreover
    { assume "t \<noteq> 0 \<and> n = 0"
      have " \<theta> t = 0"
        using 4 by auto
      have " (beh_of_world_raw w t) t = 0"
        unfolding beh_of_world_raw_def
        by (metis (full_types) less_not_refl map_add_subsumed1 map_add_subsumed2 map_le_def
        zero_fun_def zero_option_def)
      have *: " (beh_of_world_raw w t) (t - 1) = Some o (\<lambda>s. snd w s (t - 1))"
        using `t \<noteq> 0 \<and> n = 0` unfolding beh_of_world_raw_def by auto
      have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) (beh_of_world_raw w t) sig t"
        using `t \<noteq> 0 \<and> n = 0` by auto
      also have "... = signal_of (def sig) (beh_of_world_raw w t) sig (t - 1)"
        using signal_of_less[where \<tau>="beh_of_world_raw w t", OF `(beh_of_world_raw w t) t = 0`]
        by metis
      also have "... = snd w sig (t - 1)"
        using * by(auto dest!: trans_some_signal_of)
      also have "... = signal_of (def sig) \<theta> sig (t - 1)"
        using `t \<noteq> 0 \<and> n = 0` unfolding 4(1) worldline_raw_def by auto
      also have "... = signal_of (def sig) \<theta> sig t"
        using signal_of_less[where \<tau>="\<theta>", OF ` \<theta> t = 0`] by metis
      also have "... = signal_of (def sig) \<theta> sig (t - n)"
        using `t \<noteq> 0 \<and> n = 0` by auto
      finally have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) \<theta> sig (t - n)"
        by auto
      hence ?case
        using \<open>t , \<sigma> , \<gamma> , beh_of_world_raw w t, def \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b signal_of (def sig)
        (beh_of_world_raw w t) sig (t - n)\<close> by auto }
    ultimately have ?case by auto }
  ultimately show ?case by auto
qed (metis beval_raw.intros)+

lemma beval_beh_of_world':
  assumes "beval_raw t \<sigma> \<gamma> \<theta>' def exp x"
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  assumes "\<theta>' = beh_of_world_raw w t"
  shows "beval_raw t \<sigma> \<gamma> \<theta> def exp x"
  using assms
proof (induction rule: beval_raw.inducts)
  case (4 t \<sigma> \<gamma> \<theta>' def sig n)
  have *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b signal_of (def sig) \<theta> sig (t - n)"
    by (meson beval_raw.intros(4))

  have "0 < n \<and> 0 < t \<or> (t \<noteq> 0 \<and> n = 0) \<or> t = 0"
    by auto
  moreover
  { assume "0 < n \<and> 0 < t"
    hence " (beh_of_world_raw w t) (t - n) = Some \<circ> (\<lambda>s. snd w s (t - n))"
      unfolding beh_of_world_raw_def comp_def by auto
    hence "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = snd w sig (t - n)"
      by (auto dest!:trans_some_signal_of)
    also have "... = signal_of (def sig) \<theta> sig (t - n)"
      using `0 < n \<and> 0 < t` unfolding 4 worldline_raw_def by auto
    hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) \<theta> sig (t - n))"
      using * by auto
    hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) (beh_of_world_raw w t) sig (t - n))"
      using \<open>snd w sig (t - n) = signal_of (def sig) \<theta> sig (t - n)\<close> calculation by auto
    hence ?case
      using "4.prems"(3) by metis }
  moreover
  { assume "t \<noteq> 0 \<and> n = 0 \<or> t = 0"
    moreover
    { assume "t = 0"
      hence "t - n = 0" by auto
      have "beh_of_world_raw w t = 0" unfolding `t = 0`
        by (auto simp add: beh_of_world_raw_def zero_fun_def zero_option_def)
      hence "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) 0 sig 0"
        unfolding `t - n = 0` by auto
      also have "... = def sig"
        using signal_of_empty[of "def sig" "sig" "0"] by auto
      finally have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = def sig"
        by auto
      have "\<theta> = 0"
        using 4 unfolding `t = 0` by (auto simp add: zero_fun_def)
      hence "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (signal_of (def sig) \<theta> sig 0)"
        using `t - n = 0` "*" by auto
      also have "... = def sig"
        unfolding `\<theta> = 0` using signal_of_empty[of "def sig"] by metis
      finally have "beval_raw t \<sigma> \<gamma> \<theta> def (Bsig_delayed sig n) (def sig)"
        by auto
      hence ?case
        using `signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = def sig`
        by (simp add: "4.prems"(3)) }
    moreover
    { assume "t \<noteq> 0 \<and> n = 0"
      have " \<theta> t = 0"
        using 4 by auto
      have " (beh_of_world_raw w t) t = 0"
        unfolding beh_of_world_raw_def
        by (metis (full_types) less_not_refl map_add_subsumed1 map_add_subsumed2 map_le_def
        zero_fun_def zero_option_def)
      have *: " (beh_of_world_raw w t) (t - 1) = Some o (\<lambda>s. snd w s (t - 1))"
        using `t \<noteq> 0 \<and> n = 0` unfolding beh_of_world_raw_def by auto
      have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) (beh_of_world_raw w t) sig t"
        using `t \<noteq> 0 \<and> n = 0` by auto
      also have "... = signal_of (def sig) (beh_of_world_raw w t) sig (t - 1)"
        using signal_of_less[where \<tau>="beh_of_world_raw w t", OF `(beh_of_world_raw w t) t = 0`]
        by metis
      also have "... = snd w sig (t - 1)"
        using * by(auto dest!: trans_some_signal_of)
      also have "... = signal_of (def sig) \<theta> sig (t - 1)"
        using `t \<noteq> 0 \<and> n = 0` unfolding 4(1) worldline_raw_def by auto
      also have "... = signal_of (def sig) \<theta> sig t"
        using signal_of_less[where \<tau>="\<theta>", OF ` \<theta> t = 0`] by metis
      also have "... = signal_of (def sig) \<theta> sig (t - n)"
        using `t \<noteq> 0 \<and> n = 0` by auto
      finally have "signal_of (def sig) (beh_of_world_raw w t) sig (t - n) = signal_of (def sig) \<theta> sig (t - n)"
        by auto
      hence ?case
        using "4.prems"(3) beval_raw.intros(4) by fastforce }
    ultimately have ?case by auto }
  ultimately show ?case by auto
qed (metis beval_raw.intros)+

lemma beval_beh_of_world_iff:
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_raw t \<sigma> \<gamma> (beh_of_world_raw w t) def exp"
proof (rule, rule)
  fix x
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
  show "t , \<sigma> , \<gamma> , beh_of_world_raw w t, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using beval_beh_of_world[OF `t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x` assms] by auto
next
  fix x
  assume "t , \<sigma> , \<gamma> , beh_of_world_raw w t, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
  thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x "
    using beval_beh_of_world'[OF _ assms] by blast
qed

text \<open>Note that the definition of @{term "\<gamma>"} below will only be preserved by VHDL code which does
not contain a zero time signal assignment. That is, in every assignment statement, be it of transport
or inertial type, must have nonzero delay. Check @{thm "context_invariant"} and note the assumption
@{term "t < next_time t \<tau>'"}.\<close>

lemma beval_beval_world_raw:
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes gam: "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
  assumes beh: "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
  shows "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw w t exp"
proof (rule, rule)
  fix x
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x "
  have "state_of_world w t = \<sigma>"
    using state_of_world[OF assms(1) assms(2)] by auto
  moreover have "event_of_world w t = \<gamma>"
  proof (cases "0 < t")
    case True
    fix s
    have "snd w s t = \<sigma> s"
      using `state_of_world w t = \<sigma>` unfolding state_of_world_def by auto
    moreover have "snd w s (t - 1) = signal_of (def s) \<theta> s (t - 1)"
      unfolding assms(1) worldline_raw_def using True by auto
    ultimately show ?thesis
      unfolding event_of_world_def assms(3)
      using True
      by (smt Collect_cong \<open>state_of_world w t = \<sigma>\<close> assms(1) diff_less less_numeral_extra(3)
      snd_conv state_of_world_def worldline_raw_def zero_less_one)
  next
    case False
    hence "t = 0" by auto
    hence ev: "event_of_world w t = {s. snd w s 0 \<noteq> def s}"
      unfolding event_of_world_def  by (simp add: assms(1) worldline_raw_def)
    have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
      using `t = 0` gam by auto
    have "\<theta> = 0"
      using beh unfolding `t = 0` by (auto simp add: zero_fun_def)
    hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
      using signal_of_empty by metis
    hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
      using \<gamma>_def' by auto
    moreover have "\<And>s.  snd w s 0 = \<sigma> s"
      using `state_of_world w t = \<sigma>` `t = 0` unfolding state_of_world_def by auto
    ultimately  have "\<gamma> = {s. snd w s 0 \<noteq> def s}"
      by auto
    thus ?thesis  using ev by auto
  qed
  moreover have "derivative_hist_raw w t = \<theta>"
    by (simp add: assms(1) assms(5) beh derivative_is_history)
  ultimately have " beval_raw t (state_of_world w t) (event_of_world w t) (derivative_hist_raw w t) def exp =
                    beval_raw t \<sigma> \<gamma> \<theta> def exp"
    by auto
  thus "beval_world_raw w t exp x"
    by (simp add: \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> assms(1) beval_world_raw.intros worldline_raw_def)
next
  fix x
  assume "beval_world_raw w t exp x"
  hence "beval_raw t (state_of_world w t) (event_of_world w t) (derivative_hist_raw w t) def exp x"
    by (simp add: assms(1) beval_world_raw.simps worldline_raw_def)
  have "state_of_world w t = \<sigma>"
    using state_of_world[OF assms(1) assms(2)] by auto
  moreover have "event_of_world w t = \<gamma>"
  proof (cases "0 < t")
    case True
    fix s
    have "snd w s t = \<sigma> s"
      using `state_of_world w t = \<sigma>` unfolding state_of_world_def by auto
    moreover have "snd w s (t - 1) = signal_of (def s) \<theta> s (t - 1)"
      unfolding assms(1) worldline_raw_def using True by auto
    ultimately show ?thesis
      unfolding event_of_world_def assms(3)
      using True
      by (smt Collect_cong \<open>state_of_world w t = \<sigma>\<close> assms(1) diff_less less_numeral_extra(3)
      snd_conv state_of_world_def worldline_raw_def zero_less_one)
  next
    case False
    hence "t = 0" by auto
    hence ev: "event_of_world w t = {s. snd w s 0 \<noteq> def s}"
      unfolding event_of_world_def  by (simp add: assms(1) worldline_raw_def)
    have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
      using `t = 0` gam by auto
    have "\<theta> = 0"
      using beh unfolding `t = 0` by (auto simp add: zero_fun_def)
    hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
      using signal_of_empty by metis
    hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
      using \<gamma>_def' by auto
    moreover have "\<And>s.  snd w s 0 = \<sigma> s"
      using `state_of_world w t = \<sigma>` `t = 0` unfolding state_of_world_def by auto
    ultimately  have "\<gamma> = {s. snd w s 0 \<noteq> def s}"
      by auto
    thus ?thesis  using ev by auto
  qed
  moreover have "derivative_hist_raw w t = \<theta>"
    by (simp add: assms(1) assms(5) beh derivative_is_history)
  ultimately have "beval_raw t \<sigma> \<gamma> \<theta> def exp x"
    using \<open>t , state_of_world w t , event_of_world w t , derivative_hist_raw w t, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> by blast
  thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using beval_beh_of_world' assms(1) beh by blast
qed

lemma beval_beval_world_raw_ci:
  assumes "w = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau> "
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
  shows "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw w t exp"
proof -
  have 0: "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0" and
       1: "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}" and
       3: "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  show ?thesis
    using beval_beval_world_raw[OF assms(1) 0 1 3 assms(3)] by auto
qed

lemma Bguarded_hoare_valid:
  assumes "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x. beval_world_raw a t g x \<and> bval_of x)} s1 {Q}" and "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x. beval_world_raw a t g x \<and> \<not> bval_of x)} s2 {Q}"
  shows "\<Turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a trans_raw"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline_init"
  fix def
  assume "context_invariant t \<sigma> \<gamma> \<theta> def \<tau> \<and> All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>) \<and> All (non_stuttering (to_trans_raw_sig \<theta>) def) \<and>
          w = worldline_raw t \<sigma> \<theta> def \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
  hence s: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and w: "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    and c: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and p: "P w" and w': "w' = worldline_raw t \<sigma> \<theta> def \<tau>'" and
      "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)" and "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    by auto
  obtain x where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x"
    using s by (metis seq_cases_bguarded)
  hence "is_Bv x"
    using beval_raw_deterministic s  by (metis seq_cases_bguarded val.discI(1))
  have "bval_of x \<or> \<not> bval_of x"
    by auto
  moreover
  { assume "bval_of x "
    hence \<tau>'_def: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s \<open>is_Bv x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> beval_raw_deterministic val.collapse(1)
      by (metis seq_cases_bguarded val.inject(1))
    have "beval_world_raw w t g x"
      using `bval_of x` beval_beval_world_raw[OF w] c unfolding context_invariant_def
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close>
      by (simp add: \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close>)
    with `P w` have " Q w'"
      using assms(1) c w \<tau>'_def w' \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
      \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close>
      unfolding seq_hoare_valid_def  using \<open>bval_of x\<close>  by metis }
  moreover
  { assume "\<not> bval_of x"
    hence \<tau>'_def: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s \<open>is_Bv x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> beval_raw_deterministic val.collapse(1)
      by (metis dual_order.irrefl less_irrefl neq_iff seq_cases_bguarded val.sel(1))
    have "beval_world_raw w t g x"
      using `\<not> bval_of x` beval_beval_world_raw[OF w] c unfolding context_invariant_def
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close>
      by auto
    with `P w` have "Q w'"
      using assms(2) c w \<tau>'_def w' \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
      unfolding seq_hoare_valid_def  using \<open>\<not> bval_of x\<close> \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close>
      by metis }
  ultimately show "Q w'" by auto
qed

lemma lift_trans_post_worldline_upd:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "beval_world_raw \<omega> t exp x"
  assumes \<tau>'_def: "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
  assumes "\<forall>i < t. \<tau> i = 0"
  assumes "0 < dly"
  shows "worldline_raw t \<sigma> \<theta> def \<tau>' = \<omega>[sig, t + dly := x]"
proof (rule, rule_tac[2] ext, rule_tac[2] ext)
  fix s' t'
  have "t' < t \<or> t' \<ge> t" by auto
  moreover
  { assume "t' < t"
    hence 0: " snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =  signal_of (def s') \<theta> s' t'"
      unfolding worldline_raw_def by auto
    have "t' < t + dly"
      using `t' < t` by auto
    hence "snd (\<omega>[sig, t + dly := x]) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
      unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_upd_def by auto
    also have "... = signal_of (def s') \<theta> s' t'"
      using `t' < t` unfolding worldline_raw_def by auto
    finally have "snd (\<omega>[sig, t + dly := x]) s' t' = signal_of (def s') \<theta> s' t'"
      by auto
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t'"
      using 0 by auto }
  moreover
  { assume "t' \<ge> t"
    hence 0: "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
      unfolding worldline_raw_def by auto
    have "t' < t + dly \<or> t' \<ge> t + dly"
      by auto
    moreover
    { assume "t' < t + dly"
      have "snd (\<omega>[sig, t + dly := x]) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        using `t' < t + dly` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_upd_def by auto
      also have "... = signal_of (\<sigma> s') \<tau> s' t'"
        using `t' \<ge> t` unfolding worldline_raw_def by auto
      finally have 1: "snd (\<omega>[sig, t + dly := x]) s' t' = signal_of (\<sigma> s') \<tau> s' t'"
        by auto
      have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        using `t' \<ge> t` unfolding worldline_raw_def by auto
      also have "... = signal_of (\<sigma> s') \<tau> s' t'"
        using signal_of_trans_post2[OF `t' < t + dly`] unfolding \<tau>'_def by metis
      also have "... = snd (\<omega>[sig, t + dly := x]) s' t'"
        using 1 by auto
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t'"
        by auto }
    moreover
    { assume "t' \<ge> t + dly"
      have "s' = sig \<or> s' \<noteq> sig" by auto
      moreover
      { assume "s' = sig"
        hence 2: "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (snd (\<omega>[sig, t + dly := x]) s' t')"
          using `t' \<ge> t + dly` `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_upd_def
          by (smt assms(2) le_eq_less_or_eq not_less_iff_gr_or_eq snd_conv)
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        moreover have "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (signal_of (\<sigma> s') \<tau>' s' t')"
          using signal_of_trans_post3[OF `t + dly \<le> t'`, of _ "\<sigma> s'" "sig"] \<tau>'_def
          `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` \<open>s' = sig\<close> assms(2-5)  by auto
        ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t' "
          using 2 beval_world_raw_deterministic by metis }
      moreover
      { assume "s' \<noteq> sig"
        hence "sig \<noteq> s'" by auto
        hence "snd (\<omega>[sig, t + dly := x]) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
          unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_upd_def  by auto
        also have "... = signal_of (\<sigma> s') \<tau> s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        finally have 3: "snd (\<omega>[sig, t + dly := x]) s' t' = signal_of (\<sigma> s') \<tau> s' t'"
          by auto
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        also have "... = signal_of (\<sigma> s') \<tau> s' t'"
          unfolding \<tau>'_def using signal_of_trans_post[OF `sig \<noteq> s'`] by metis
        also have "... = snd (\<omega>[sig, t + dly := x]) s' t'"
          using 3 by auto
        finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t' "
          by auto }
      ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t' "
        by auto }
    ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t' "
      by auto }
  ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t + dly := x]) s' t'"
    by auto
qed (simp add: assms(1) worldline_raw_def worldline_upd_def)

lemma Bassign_trans_sound:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> (\<exists>x. beval_world_raw w t exp x \<and> Q (w[sig, t + dly := x]))"
    by (auto dest!: BassignE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a trans_raw"
    fix w w' :: "'a worldline_init"
    fix \<gamma> def
    assume "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    hence "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
      unfolding context_invariant_def by auto
    assume "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    assume "P w"
    assume "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    then obtain x where "beval_raw t \<sigma> \<gamma> \<theta> def exp x" and "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
      by (metis seq_cases_trans)
    moreover have "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw w t exp"
      using `w = worldline_raw t \<sigma> \<theta> def \<tau>` \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> beval_beval_world_raw_ci
      \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close> by blast
    ultimately have \<tau>'_def: "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
      by auto
    have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') = snd (w[sig, t + dly := x])"
      using \<open>w = worldline_raw t \<sigma> \<theta> def \<tau>\<close> \<tau>'_def lift_trans_post_worldline_upd `\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0` `0 < dly`
      by (metis \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw w t exp\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> less_imp_le_nat)
    with imp and `P w` have "Q(w[sig, t + dly := x])"
      by (metis (full_types) \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw w t exp\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> beval_world_raw_deterministic)
    assume "w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
    hence "Q w'"
      using `Q(w[sig, t + dly := x])` `snd (worldline_raw t \<sigma> \<theta> def \<tau>') = snd (w[sig, t + dly := x])`
      by (simp add: \<open>w = worldline_raw t \<sigma> \<theta> def \<tau>\<close> worldline_raw_def worldline_upd_def) }
  thus " \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
    unfolding seq_hoare_valid_def  by meson
qed

lemma lift_inr_post_worldline_upd:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "0 < dly"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  assumes "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
  assumes "beval_world_raw \<omega> t exp (Bv v)"
  shows "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_inert_upd2 \<omega> sig t dly (Bv v)"
proof (rule, rule_tac[2] ext, rule_tac[2] ext)
  fix s' t'
  have "beval_raw t \<sigma> \<gamma> \<theta> def exp (Bv v)"
    using assms beval_beval_world_raw_ci by metis
  have "\<tau>' = inr_post_raw' sig (Bv v) (\<sigma> sig) \<tau> t dly"
    using assms(3) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b(Bv v)\<close> beval_raw_deterministic  by (metis seq_cases_inert)
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw \<omega> t exp"
    using `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    by (simp add: assms(6) beval_beval_world_raw_ci)
  hence \<tau>'_def: "\<tau>' = inr_post_raw' sig(Bv v) (\<sigma> sig) \<tau> t dly"
    by (simp add: calculation)
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using b_seq_exec_preserves_context_invariant[OF assms(2-3)] `0 < dly` by auto

  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  have "s' \<noteq> sig \<or> t' < t \<or> s' = sig \<and> t \<le> t'"
    by auto
  moreover
  { assume "s' \<noteq> sig \<or> t' < t"
    moreover
    { assume "t' < t"
      hence 0: " snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =  signal_of (def s') \<theta> s' t'"
        unfolding worldline_raw_def by auto
      have "t' < t + dly"
        using `t' < t` by auto
      hence "snd (\<omega>[sig, t,  dly :=(Bv v)]) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_inert_upd_def  by (simp add: \<open>t' < t\<close>)
      also have "... = signal_of (def s') \<theta> s' t'"
        using `t' < t` unfolding worldline_raw_def by auto
      finally have "snd (\<omega>[sig, t, dly :=(Bv v)]) s' t' = signal_of (def s') \<theta> s' t'"
        by auto
      hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly :=(Bv v)]) s' t'"
        using 0 by auto }
    moreover
    { assume "s' \<noteq> sig"
      hence "snd (\<omega>[sig, t, dly :=(Bv v)]) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        unfolding worldline_inert_upd_def `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` by auto
      also have "... = snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t'"
      proof -
        have "\<And>n. (to_trans_raw_sig \<tau> s') n = (to_trans_raw_sig \<tau>' s') n"
          using `s' \<noteq> sig` unfolding \<tau>'_def inr_post_raw'_def
          by (metis purge_raw_does_not_affect_other_sig' to_trans_raw_sig_def trans_post_raw_diff_sig)
        hence "signal_of (\<sigma> s') \<tau> s' t' = signal_of (\<sigma> s') \<tau>'  s' t'"
          by (meson signal_of_equal_when_trans_sig_equal_upto)
        thus ?thesis
          unfolding worldline_raw_def by auto
      qed
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly :=(Bv v)]) s' t'"
        by auto }
    ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := Bv v]) s' t'"
      by auto }
  moreover
  { assume "s' = sig \<and> t \<le> t'"
    have "(snd \<omega> sig t = (Bv v) \<or> snd \<omega> sig (t + dly) \<noteq> (Bv v)) \<or> (snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v))"
      by auto
    moreover
    { assume "snd \<omega> sig t = (Bv v) \<or> snd \<omega> sig (t + dly) \<noteq> (Bv v)"
      have "t + dly \<le> t' \<or> t' < t + dly" and "s' = sig" and "t \<le> t'"
        using leI \<open>s' = sig \<and> t \<le> t'\<close> by auto
      moreover
      { assume "t + dly \<le> t'"
        hence 2: "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (snd (\<omega>[sig, t, dly := (Bv v)]) s' t')"
            using `s' = sig`  `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_inert_upd_def
            using \<open>snd \<omega> sig t = (Bv v) \<or> snd \<omega> sig (t + dly) \<noteq> (Bv v)\<close> assms(1)
            by (smt \<open>s' = sig \<and> t \<le> t'\<close> assms(7) not_le snd_conv)
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        hence "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (signal_of (\<sigma> s') \<tau>' s' t')"
          using signal_of_inr_post'[OF `t + dly \<le> t'`, of _ "\<sigma> s'" "sig"]  \<tau>'_def
          `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>`  using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>s' = sig \<and> t \<le> t'\<close> `0 < dly`
          assms(7) by auto
        hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t' "
          using 2 \<open>snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'\<close>
          beval_world_raw_deterministic by metis }
      moreover
      { assume "t' < t + dly"
        hence "snd (\<omega>[sig, t, dly := (Bv v)]) s' t' = snd \<omega> sig t"
          unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close>
          using \<open>snd \<omega> sig t = (Bv v) \<or> snd \<omega> sig (t + dly) \<noteq> (Bv v)\<close> by auto
        also have "... = signal_of (\<sigma> sig) \<tau> sig t"
          unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_raw_def by auto
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
        finally have l: "snd (\<omega>[sig, t, dly := (Bv v)]) s' t' = \<sigma> sig"
          by auto
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          unfolding worldline_raw_def using `s' = sig \<and> t \<le> t'` by auto
        also have "... = \<sigma> s'"
        proof -
          have 0: "signal_of (\<sigma> s') \<tau> s' t = (Bv v) \<or> signal_of (\<sigma> s') \<tau> s' (t + dly) \<noteq> (Bv v)"
            using `snd \<omega> sig t = (Bv v) \<or> snd \<omega> sig (t + dly) \<noteq> (Bv v)` \<open>s' = sig\<close>
            unfolding assms(1) worldline_raw_def by auto
          thus ?thesis
            using signal_of_inr_post3[OF `t \<le> t'` `t' < t + dly` `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`] \<open>s' = sig\<close>
            unfolding \<tau>'_def inr_post_raw'_eq_inr_post_raw
            by (meson \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>s' = sig \<and> t \<le> t'\<close> \<open>t' < t + dly\<close> signal_of_inr_post3)
        qed
        finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = \<sigma> s'"
          by auto
        with l have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t' "
          using `s' = sig` by auto }
      ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t' "
        by auto }
    moreover
    { assume "snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)"
      hence sig_not_eq: "signal_of (\<sigma> sig) \<tau> sig t \<noteq> (Bv v)" and  sig_eq: "signal_of (\<sigma> sig) \<tau> sig (t + dly) = (Bv v)"
        unfolding assms(1) worldline_raw_def by auto
      hence exist_mapping: "\<exists>k > t. k\<le>t + dly \<and> \<tau> k sig = Some (Bv v)"
        using switch_signal_ex_mapping[of "\<sigma>", OF sig_not_eq] `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`
        by (simp add: zero_fun_def)
      let ?time = "GREATEST n. n \<le> t + dly \<and> (snd \<omega> sig (n - 1) \<noteq> (Bv v)) \<and> snd \<omega> sig n = (Bv v)"
      have "?time \<le> t' \<or> t' < ?time" and "s' = sig" and "t \<le> t'"
        using \<open>s' = sig \<and> t \<le> t'\<close> by auto
      moreover
      { assume "?time \<le> t'"
        hence 2: "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (snd (\<omega>[sig, t, dly := (Bv v)]) s' t')"
            using `s' = sig` unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_inert_upd_def
            using \<open>snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)\<close>
            \<open>s' = sig \<and> t \<le> t'\<close> assms(1)  using assms(7) by auto
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          using `t' \<ge> t` unfolding worldline_raw_def by auto
        also have "... = (Bv v)"
          unfolding \<tau>'_def \<open>s' = sig\<close> inr_post_raw'_eq_inr_post_raw
        proof (rule signal_of_inr_post4)
          show "signal_of (\<sigma> sig) \<tau> sig t \<noteq> (Bv v)"
            using \<open>snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)\<close>
            by (simp add: assms(1) worldline_raw_def)
        next
          show "signal_of (\<sigma> sig) \<tau> sig (t + dly) = (Bv v)"
            using \<open>snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)\<close>
            by (simp add: assms(1) worldline_raw_def)
        next
          have "?time = (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v))" (is "_ = ?time2")
          proof (rule Greatest_equality)
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (Bv v)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)" and b="t + dly"]
              exist_mapping by auto
            have "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close>
                 \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) sig = Some (Bv v)\<close> leI
              option.distinct(1) zero_fun_def zero_option_def)
            have "signal_of (\<sigma> sig) \<tau> sig ?time2 = (Bv v)"
              using trans_some_signal_of'[of "\<tau>", OF `\<tau> ?time2 sig = Some (Bv v)`]
              by auto
            hence "snd \<omega> sig ?time2 = (Bv v)"
              using `t < ?time2` unfolding assms(1) worldline_raw_def by auto
            have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<noteq> (Bv v)"
            proof (cases "\<exists>n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None")
              case False
              hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time2 - 1 \<Longrightarrow> \<tau> n sig = 0"
                by (auto simp add: zero_option_def)
              have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) = signal_of (\<sigma> sig) \<tau> sig t"
                using signal_of_less_ind'[of "t" "?time2 - 1" "\<tau>" "sig", OF none] `t < ?time2`
                by auto
              also have "... \<noteq> (Bv v)"
                using sig_not_eq by auto
              finally show "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<noteq> (Bv v)"
                by auto
            next
              case True
              let ?key1 = "(GREATEST n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None)"
              from True have "t < ?key1" and "?key1 < ?time2" and "\<tau> ?key1 sig \<noteq> None"
                using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
              have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time2 \<Longrightarrow> \<tau> n sig = None"
                using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time2 \<and> \<tau> x sig \<noteq> None" and b="?time2"]
                by (smt \<open>t < (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<and>
                \<tau> n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
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
                  using `\<tau> ?time2 sig = Some (Bv v)`
                  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "\<forall>k. ?key1 < k \<and> k < ?time2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
                  using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                  zero_option_def)
                ultimately show ?thesis
                  using `?key1 < ?time2` assms(5) unfolding non_stuttering_def
                  by (simp add: to_trans_raw_sig_def)
              qed
              hence "\<tau> ?key1 sig \<noteq> Some (Bv v)"
                using \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) sig = Some (Bv v)\<close>
                      \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> by auto
              thus ?thesis
                unfolding to_signal_def comp_def using inf_some
                by (metis (no_types, lifting) \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and>
                \<tau> n sig = Some (Bv v)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> not_None_eq option.sel
                option.simps(5) to_trans_raw_sig_def)
            qed
            hence "snd \<omega> sig (?time2 - 1) \<noteq>  (Bv v)"
              using `t < ?time2` unfolding assms(1) worldline_raw_def  by (simp add: leD)
            thus "?time2 \<le> t + dly \<and> snd \<omega> sig (?time2 - 1) \<noteq> (Bv v) \<and> snd \<omega> sig ?time2 = (Bv v)"
              using \<open>(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<le> t + dly\<close>
              \<open>snd \<omega> sig (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) = (Bv v)\<close> by blast
          next
            fix y
            assume "y \<le> t + dly \<and> snd \<omega> sig (y - 1) \<noteq> (Bv v) \<and> snd \<omega> sig y = (Bv v)"
            hence "y \<le> t + dly" and "snd \<omega> sig (y - 1) \<noteq> (Bv v)" and "snd \<omega> sig y = (Bv v)"
              by auto
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (Bv v)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)" and b="t + dly"]
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
              hence "snd \<omega> sig (y - 1) = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                unfolding assms(1) worldline_raw_def by auto
              hence 0: "... \<noteq> (Bv v)"
                using `snd \<omega> sig (y - 1) \<noteq> (Bv v)` by auto
              have "snd \<omega> sig y = signal_of (\<sigma> sig) \<tau> sig y"
                unfolding assms(1) worldline_raw_def using `t < y` by auto
              hence 1: "... = (Bv v)"
                using `snd \<omega> sig y = (Bv v)` `t < y` by auto
              have "\<tau> y sig = Some (Bv v)"
              proof (rule ccontr)
                assume "\<not> \<tau> y sig = Some (Bv v)"
                then obtain x' where "\<tau> y sig = None \<or> \<tau> y sig = Some x' \<and> x' \<noteq> (Bv v)"
                  using domIff by fastforce
                moreover
                { assume "\<tau> y sig = None"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                    by (intro signal_of_less_sig)(simp add: zero_option_def)
                  with 0 1 have False by auto }
                moreover
                { assume "\<tau> y sig = Some x' \<and> x' \<noteq> (Bv v)"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = x'" and "x' \<noteq> (Bv v)"
                    using trans_some_signal_of' by fastforce+
                  with 1 have False by auto }
                ultimately show False by auto
              qed
              with `y \<le> t + dly` have "y \<le> ?time2"
                by (metis (mono_tags, lifting) Greatest_le_nat) }
            ultimately show "y \<le> ?time2"
              by auto
          qed
          thus "(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<le> t'"
            using \<open>(GREATEST n. n \<le> t + dly \<and> snd \<omega> sig (n - 1) \<noteq> Bv v \<and> snd \<omega> sig n = Bv v) \<le> t'\<close> by linarith
        next
          show "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
            using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> by auto
        qed
        hence "beval_world_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t exp (Bv v)"
          using assms(1) assms(7) by metis
        hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t' "
          using 2  by (metis \<open>signal_of (\<sigma> s') \<tau>' s' t' = (Bv v)\<close> beval_world_raw_deterministic calculation) }
      moreover
      { assume " t' < ?time"
        hence "snd (\<omega>[sig, t, dly := (Bv v)]) s' t' = snd \<omega> sig t"
          unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close>
          using \<open>snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)\<close> by auto
        also have "... = signal_of (\<sigma> sig) \<tau> sig t"
          unfolding `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>` worldline_raw_def by auto
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
        finally have l: "snd (\<omega>[sig, t, dly := (Bv v)]) s' t' = \<sigma> sig"
          by auto
        have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
          unfolding worldline_raw_def using `s' = sig \<and> t \<le> t'` by auto
        also have "... = \<sigma> s'"
          unfolding \<tau>'_def \<open>s' = sig\<close> inr_post_raw'_eq_inr_post_raw
        proof(rule signal_of_inr_post2)
          show "t \<le> t'"
            by (simp add: \<open>s' = sig \<and> t \<le> t'\<close>)
        next
          show "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
            using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> by blast
        next
          show "\<sigma> sig \<noteq> (Bv v)"
            using \<open>snd \<omega> sig t = signal_of (\<sigma> sig) \<tau> sig t\<close> \<open>snd \<omega> sig t \<noteq> (Bv v) \<and> snd \<omega> sig (t + dly) = (Bv v)\<close>
            \<open>signal_of (\<sigma> sig) \<tau> sig t = \<sigma> sig\<close> by simp
        next
          show "signal_of (\<sigma> sig) \<tau> sig (t + dly) = (Bv v)"
            using sig_eq by blast
        next
          have "?time = (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v))" (is "_ = ?time2")
          proof (rule Greatest_equality)
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (Bv v)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)" and b="t + dly"]
              exist_mapping by auto
            have "t < ?time2"
              by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n
              sig = Some (Bv v)) sig = Some (Bv v)\<close> leI option.distinct(1) zero_fun_def zero_option_def)
            have "signal_of (\<sigma> sig) \<tau> sig ?time2 = (Bv v)"
              using trans_some_signal_of'[of "\<tau>", OF `\<tau> ?time2 sig = Some (Bv v)`]
              by auto
            hence "snd \<omega> sig ?time2 = (Bv v)"
              using `t < ?time2` unfolding assms(1) worldline_raw_def by auto
            have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<noteq>  (Bv v)"
            proof (cases "\<exists>n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None")
              case False
              hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time2 - 1 \<Longrightarrow> \<tau> n sig = 0"
                by (auto simp add: zero_option_def)
              have "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) = signal_of (\<sigma> sig) \<tau> sig t"
                using signal_of_less_ind'[of "t" "?time2 - 1" "\<tau>" "sig", OF none] `t < ?time2`
                by auto
              also have "... \<noteq> (Bv v)"
                using sig_not_eq by auto
              finally show "signal_of (\<sigma> sig) \<tau> sig (?time2 - 1) \<noteq> (Bv v)"
                by auto
            next
              case True
              let ?key1 = "(GREATEST n. t < n \<and> n < ?time2 \<and> \<tau> n sig \<noteq> None)"
              from True have "t < ?key1" and "?key1 < ?time2" and "\<tau> ?key1 sig \<noteq> None"
                using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
              have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time2 \<Longrightarrow> \<tau> n sig = None"
                using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time2 \<and> \<tau> x sig \<noteq> None" and b="?time2"]
                by (smt \<open>t < (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<and>
                \<tau> n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
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
                  using `\<tau> ?time2 sig = Some (Bv v)`
                  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                moreover have "\<forall>k. ?key1 < k \<and> k < ?time2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig \<tau> sig)"
                  using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                  zero_option_def)
                ultimately show ?thesis
                  using `?key1 < ?time2` assms(5) unfolding non_stuttering_def
                  by (simp add: to_trans_raw_sig_def)
              qed
              hence "\<tau> ?key1 sig \<noteq> Some (Bv v)"
                using \<open>\<tau> (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) sig =
                Some (Bv v)\<close> \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly
                \<and> \<tau> n sig = Some (Bv v)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> by auto
              thus ?thesis
                unfolding to_signal_def comp_def using inf_some
                by (metis (no_types, lifting) \<open>\<tau> (GREATEST n. t < n \<and> n < (GREATEST n. n \<le> t + dly \<and>
                \<tau> n sig = Some (Bv v)) \<and> \<tau> n sig \<noteq> None) sig \<noteq> None\<close> not_None_eq option.sel
                option.simps(5) to_trans_raw_sig_def)
            qed
            hence "snd \<omega> sig (?time2 - 1) \<noteq>  (Bv v)"
              using `t < ?time2` unfolding assms(1) worldline_raw_def  by (simp add: leD)
            thus "?time2 \<le> t + dly \<and> snd \<omega> sig (?time2 - 1) \<noteq> (Bv v) \<and> snd \<omega> sig ?time2 = (Bv v)"
              using \<open>(GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) \<le> t + dly\<close>
              \<open>snd \<omega> sig (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)) = (Bv v)\<close> by blast
          next
            fix y
            assume "y \<le> t + dly \<and> snd \<omega> sig (y - 1) \<noteq> (Bv v) \<and> snd \<omega> sig y = (Bv v)"
            hence "y \<le> t + dly" and "snd \<omega> sig (y - 1) \<noteq> (Bv v)" and "snd \<omega> sig y = (Bv v)"
              by auto
            have "?time2 \<le> t + dly" and "\<tau> ?time2 sig = Some (Bv v)"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v)" and b="t + dly"]
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
              hence "snd \<omega> sig (y - 1) = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                unfolding assms(1) worldline_raw_def by auto
              hence 0: "... \<noteq> (Bv v)"
                using `snd \<omega> sig (y - 1) \<noteq> (Bv v)` by auto
              have "snd \<omega> sig y = signal_of (\<sigma> sig) \<tau> sig y"
                unfolding assms(1) worldline_raw_def using `t < y` by auto
              hence 1: "... = (Bv v)"
                using `snd \<omega> sig y = (Bv v)` `t < y` by auto
              have "\<tau> y sig = Some (Bv v)"
              proof (rule ccontr)
                assume "\<not> \<tau> y sig = Some (Bv v)"
                then obtain x' where "\<tau> y sig = None \<or> \<tau> y sig = Some x' \<and> x' \<noteq> (Bv v)"
                  using domIff by fastforce
                moreover
                { assume "\<tau> y sig = None"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = signal_of (\<sigma> sig) \<tau> sig (y - 1)"
                    by (intro signal_of_less_sig)(simp add: zero_option_def)
                  with 0 1 have False by auto }
                moreover
                { assume "\<tau> y sig = Some x' \<and> x' \<noteq> (Bv v)"
                  hence "signal_of (\<sigma> sig) \<tau> sig y = x'" and "x' \<noteq> (Bv v)"
                    using trans_some_signal_of' by fastforce+
                  with 1 have False by auto }
                ultimately show False by auto
              qed
              with `y \<le> t + dly` have "y \<le> ?time2"
                by (metis (mono_tags, lifting) Greatest_le_nat) }
            ultimately show "y \<le> ?time2"
              by auto
          qed
          thus "t' < (GREATEST n. n \<le> t + dly \<and> \<tau> n sig = Some (Bv v))"
            using \<open>t' < (GREATEST n. n \<le> t + dly \<and> snd \<omega> sig (n - 1) \<noteq> (Bv v) \<and> snd \<omega> sig n = (Bv v))\<close>
            by linarith
        qed
        finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = \<sigma> s'"
          by auto
        with l have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t' "
          using `s' = sig` by auto }
      ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t'"
        by auto }
    ultimately  have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (\<omega>[sig, t, dly := (Bv v)]) s' t'"
      by auto }
  ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Bv v)) s' t' "
    by (simp add: assms(1) worldline_inert_upd_def worldline_raw_def)
qed (simp add: assms(1) worldline_inert_upd_def worldline_raw_def)

lemma to_bit_signal_of_eq:
  "signal_of (Bv (bs ! b)) (to_trans_raw_bit (Lv sign bs) \<tau> b sig) sig t = v \<longleftrightarrow> to_bit b (signal_of (Lv sign bs) \<tau> sig t) = v"
  by (metis (no_types, lifting) to_bit_signal_of' val.case_eq_if val.collapse(1) val.distinct(1) val.sel(3))

lemma non_stuttering_to_trans_raw_bit:
  assumes " non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  shows   " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) (to_bit b o \<sigma>) sig"
  unfolding non_stuttering_def
proof (rule)+
  fix k1 k2 :: nat
  assume "k1 < k2 \<and>
       k1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<and>
       k2 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<and>
       (\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig))"
  hence "k1 < k2" and "k1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)" 
    and "k2 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)" 
    and *: "(\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig))"
    by auto
  hence "to_trans_raw_bit (\<sigma> sig) \<tau> b sig k1 sig \<noteq> None" and  "to_trans_raw_bit (\<sigma> sig) \<tau> b sig k2 sig \<noteq> None" and "0 < k2"
    unfolding keys_def to_trans_raw_sig_def by (auto simp add: zero_option_def)
  hence "\<tau> k2 sig \<noteq> None" and "to_bit b (signal_of (\<sigma> sig) \<tau> sig (k2 - 1)) \<noteq> to_bit b (the (\<tau> k2 sig))"
    unfolding to_trans_raw_bit_def by (auto split: option.splits)
  have " inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (k2 - 1) = Some k1"
  proof (rule inf_time_someI)
    show " k1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
      using \<open> k1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> 
      unfolding dom_def keys_def zero_option_def by auto
  next
    show "k1 \<le> k2 - 1" using \<open>k1 < k2\<close> by auto
  next
    show "\<forall>t\<in>dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). t \<le> k2 - 1 \<longrightarrow> t \<le> k1"
      using * unfolding dom_def keys_def zero_option_def  using leI by force
  qed
  hence " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (k2 - 1) = 
         the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k1)"
    unfolding to_bit_signal_of'_eq[THEN sym] to_signal_def comp_def by auto
  moreover have " the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k2)  = to_bit b (the (\<tau> k2 sig))"
    using \<open>0 < k2\<close> \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (k2 - 1)) \<noteq> to_bit b (the (\<tau> k2 sig))\<close>
    unfolding to_trans_raw_sig_def to_trans_raw_bit_def  using \<open>\<tau> k2 sig \<noteq> None\<close> by auto
  ultimately have "to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k1 \<noteq> to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k2"
    using to_bit_signal_of'_eq 
    using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (k2 - 1)) \<noteq> to_bit b (the (\<tau> k2 sig))\<close> by fastforce
  moreover assume "to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k1 = to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig k2"
  ultimately show False
    by auto
next
  { assume ex: " keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<noteq> {}"
    let ?time = "(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig))"
    have "?time \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
      using ex  by (meson LeastI all_not_in_conv)
    have "\<tau> ?time sig \<noteq> None"
    proof -
      have "\<exists>n v. to_trans_raw_bit v \<tau> n sig (LEAST n. n \<in> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> None}) sig \<noteq> None"
        by (metis \<open>(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> domD dom_def keys_def option.simps(3) to_trans_raw_sig_def zero_option_def)
      then have "\<tau> (LEAST n. n \<in> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> None}) sig \<noteq> None"
        by (smt option.simps(4) to_trans_raw_bit_def)
      then show ?thesis
        by (simp add: keys_def zero_option_def)
    qed
    have "?time = 0 \<or> ?time \<noteq> 0"
      by auto
    moreover
    { assume "?time = 0"
      hence "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig) \<noteq> to_bit b (\<sigma> sig)"
        unfolding to_trans_raw_bit_def 
      proof -
        assume a1: "(LEAST k. k \<in> keys (to_trans_raw_sig (\<lambda>n siga. if siga \<noteq> sig then \<tau> n siga else case \<tau> n siga of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> siga (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) = 0"
        have "0 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
          using \<open>(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) = 0\<close> \<open>(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> by presburger
        then have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig 0 sig \<noteq> None"
          by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
        then have f2: "(case \<tau> 0 sig of None \<Rightarrow> None | Some v \<Rightarrow> if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b v then None else if to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) \<noteq> None"
          by (smt option.case_eq_if to_trans_raw_bit_def)  
        then have f3: "\<tau> 0 sig \<noteq> None"
          by (metis option.case_eq_if)
        obtain vv :: "val option \<Rightarrow> val" where
          "\<And>z za v. (z = None \<or> Some (vv z) = z) \<and> (za \<noteq> None \<or> za \<noteq> Some (v::val))"
          by (metis (full_types) not_None_eq)
        then have f4: "\<And>z za f. z = None \<or> (case z of None \<Rightarrow> za::val option | Some x \<Rightarrow> f x) = f (vv z)"
          by (metis (full_types) option.case_eq_if option.sel)
        then have f5: "(if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b (vv (\<tau> 0 sig)) then None else if to_bit b (\<sigma> sig) = to_bit b (vv (\<tau> 0 sig)) then None else Some (to_bit b (vv (\<tau> 0 sig)))) \<noteq> None \<or> \<tau> 0 sig = None"
          using f2  by smt
        { assume "(if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b (vv (\<tau> 0 sig)) then None else if True \<and> to_bit b (\<sigma> sig) = to_bit b (vv (\<tau> 0 sig)) then None else Some (to_bit b (vv (\<tau> 0 sig)))) \<noteq> Some (to_bit b (\<sigma> sig))"
          have "\<tau> 0 sig \<noteq> None \<and> the (if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b (vv (\<tau> 0 sig)) then None else if True \<and> to_bit b (\<sigma> sig) = to_bit b (vv (\<tau> 0 sig)) then None else Some (to_bit b (vv (\<tau> 0 sig)))) \<noteq> to_bit b (\<sigma> sig)"
            using f5 f3 by force }
        then have "\<tau> 0 sig \<noteq> None \<and> the (if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b (vv (\<tau> 0 sig)) then None else if True \<and> to_bit b (\<sigma> sig) = to_bit b (vv (\<tau> 0 sig)) then None else Some (to_bit b (vv (\<tau> 0 sig)))) \<noteq> to_bit b (\<sigma> sig)"
          by simp
        then have "the (if False then \<tau> 0 sig else case \<tau> 0 sig of None \<Rightarrow> None | Some v \<Rightarrow> if (0::nat) < 0 \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig (0 - 1)) = to_bit b v then None else if to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) \<noteq> to_bit b (\<sigma> sig)"
          using f4  by (metis (no_types, lifting))
        then show "the (if sig \<noteq> sig then \<tau> (LEAST n. n \<in> keys (to_trans_raw_sig (\<lambda>n a. if a \<noteq> sig then \<tau> n a else case \<tau> n a of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> a (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) sig else case \<tau> (LEAST n. n \<in> keys (to_trans_raw_sig (\<lambda>n a. if a \<noteq> sig then \<tau> n a else case \<tau> n a of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> a (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) sig of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < (LEAST n. n \<in> keys (to_trans_raw_sig (\<lambda>n a. if a \<noteq> sig then \<tau> n a else case \<tau> n a of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> a (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) \<and> to_bit b (signal_of (\<sigma> sig) \<tau> sig ((LEAST n. n \<in> keys (to_trans_raw_sig (\<lambda>n a. if a \<noteq> sig then \<tau> n a else case \<tau> n a of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> a (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) - 1)) = to_bit b v then None else if (LEAST n. n \<in> keys (to_trans_raw_sig (\<lambda>n a. if a \<noteq> sig then \<tau> n a else case \<tau> n a of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit b (signal_of (\<sigma> sig) \<tau> a (n - 1)) = to_bit b v then None else if n = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) sig)) = 0 \<and> to_bit b (\<sigma> sig) = to_bit b v then None else Some (to_bit b v)) \<noteq> to_bit b (\<sigma> sig)"
          using a1 by presburger
      qed
      hence " (to_bit b o \<sigma>) sig \<noteq> the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time)"
      proof -
        have f1: "\<And>n. n \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<or> to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> 0"
          by (simp add: keys_def)
        have "\<forall>v n. \<exists>b. to_bit n v = Bv b"
          by (metis to_bit.elims)
        then obtain bb :: "val \<Rightarrow> nat \<Rightarrow> bool" where
          f2: "\<And>n v. to_bit n v = Bv (bb v n)"
          by moura
        moreover
        { assume "\<exists>n. Bv (bb (\<sigma> sig) n) \<noteq> \<sigma> sig"
          then have "\<exists>f v. Some (\<sigma> sig) = Some (f sig) \<and> signal_of v (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (LEAST n. n \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) \<noteq> f sig"
            using f2 by (metis to_bit.simps(1) to_bit_signal_of')
          then have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (LEAST n. n \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) sig) \<noteq> \<sigma> sig"
            using f1 by (metis \<open>(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> option.collapse to_trans_raw_sig_def trans_some_signal_of' zero_option_def) }
        ultimately show ?thesis
          by (metis \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) sig) \<noteq> to_bit b (\<sigma> sig)\<close> comp_apply to_trans_raw_sig_def)
      qed }
    moreover
    { assume "?time \<noteq> 0"
      hence "  to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> to_bit b (the (\<tau> ?time sig))"
        using \<open>?time \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close>
        unfolding to_trans_raw_sig_def keys_def to_trans_raw_bit_def  by (smt mem_Collect_eq neq0_conv option.case_eq_if zero_option_def)
      moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) = (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))"
        unfolding to_bit_signal_of'_eq[THEN sym]
      proof (rule signal_of_def)
        fix n 
        assume "n \<le> ?time - 1"
        thus "         to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = 0"
        proof -
          have "n \<le> (LEAST n. n \<in> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> 0}) - 1"
            by (metis \<open>n \<le> (LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) - 1\<close> keys_def)
          then have f1: "\<forall>na. na \<le> (LEAST n. n \<in> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> 0}) - 1 \<or> \<not> na \<le> n"
            by (meson le_trans)
          have "(LEAST n. n \<in> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> 0}) \<noteq> 0"
            by (metis \<open>(LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)) \<noteq> 0\<close> keys_def)
          then have "n \<notin> {n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig n \<noteq> 0}"
            using f1 by (metis Least_le diff_le_self le_antisym minus_eq zero_neq_one)
          then show ?thesis
            by (simp add: to_trans_raw_sig_def)
        qed
      qed
      ultimately have "(to_bit b \<circ> \<sigma>) sig \<noteq> to_bit b (the (\<tau> ?time sig))"
        unfolding comp_def
        by (metis to_bit.simps(1) to_bit.simps(2) val.case_eq_if val.collapse(1) val.collapse(2))
      moreover have " to_bit b (the (\<tau> ?time sig)) = the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time)"
        using \<open>\<tau> ?time sig \<noteq> None\<close> \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> to_bit b (the (\<tau> ?time sig))\<close>
        unfolding to_trans_raw_sig_def to_trans_raw_bit_def apply auto
        by (smt inf_time_at_most le_zero_eq option.exhaust option.sel option.simps(4) option.simps(5) to_signal_def) 
      ultimately have " (to_bit b \<circ> \<sigma>) sig \<noteq> the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time)"
        by auto }
    ultimately have "(to_bit b \<circ> \<sigma>) sig \<noteq>
    the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig
          (LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)))"
      by auto }
  thus "keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<noteq> {} \<longrightarrow>
    (to_bit b \<circ> \<sigma>) sig \<noteq>
    the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig
          (LEAST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)))"
    by auto
qed
  
lemma lift_inr_post_worldline_upd2:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "0 < dly"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  assumes "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
  assumes "beval_world_raw \<omega> t exp (Lv sign bs)"
  shows   "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)"
proof (rule, rule_tac[2] ext, rule_tac[2] ext)
  fix s' t'
  have "beval_raw t \<sigma> \<gamma> \<theta> def exp (Lv sign bs)"
    using assms beval_beval_world_raw_ci by metis
  have "\<tau>' = inr_post_raw' sig (Lv sign bs) (\<sigma> sig) \<tau> t dly"
    using assms(3) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b(Lv sign bs)\<close> beval_raw_deterministic  by (metis seq_cases_inert)
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw \<omega> t exp"
    using `\<omega> = worldline_raw t \<sigma> \<theta> def \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    by (simp add: assms(6) beval_beval_world_raw_ci)
  hence \<tau>'_def: "\<tau>' = inr_post_raw' sig(Lv sign bs) (\<sigma> sig) \<tau> t dly"
    by (simp add: calculation)
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using b_seq_exec_preserves_context_invariant[OF assms(2-3)] `0 < dly` by auto

  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  have "s' \<noteq> sig \<or> t' < t \<or> s' = sig \<and> t \<le> t'"
    by auto
  moreover
  { assume "s' = sig \<and> t \<le> t'"
    hence "t + dly \<le> t' \<or> t' < t + dly" and "s' = sig" and "t \<le> t'"
      by auto
    moreover
    { assume "t + dly \<le> t'"
      hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        unfolding worldline_raw_def snd_conv by auto
      also have "... = signal_of (\<sigma> s') (inr_post_raw' sig (Lv sign bs) (\<sigma> sig) \<tau> t dly) s' t'"
        unfolding \<tau>'_def by auto
      also have "... = signal_of (\<sigma> s') (trans_post_raw sig (Lv sign bs) (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) t dly) s' t'"
        unfolding inr_post_raw'_def by auto
      also have "... = Lv sign bs"
        unfolding `s' = sig`
      proof (intro signal_of_trans_post3)
        show "t + dly \<le> t'"
          using `t + dly \<le> t'` by auto
      next
        show "\<forall>i<t. purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) i = 0"
          using assms(2) unfolding purge_raw'_def combine_trans_bit_def context_invariant_def by auto
      next
        show "0 < dly"
          by (simp add: assms(4))
      qed
      also have "... = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t'"
        unfolding worldline_inert_upd2.simps snd_conv `s' = sig`
      proof -
        have "bs = map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs]"
        proof (rule nth_equalityI)
          fix i 
          assume "i < length bs"
          hence "map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs] ! i = 
                 bval_of (snd to_worldline_init_bit \<omega> sig i[sig, t, dly := Bv (bs ! i)] sig t')"
            by auto
          also have "... = bs ! i"
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv
          proof (cases "((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t = Bv (bs ! i) \<or> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! i)")
            case False
            hence "((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! i)" and 
                  "((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! i)"
              by auto
            have *: "\<exists>k\<le>t + dly. ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (k - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig k = Bv (bs ! i) "
            proof (rule ccontr)
              assume "\<not> (\<exists>k\<le>t + dly. ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (k - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig k = Bv (bs ! i))"
              hence ind: "\<forall>k. k \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (k - 1) \<noteq> Bv (bs ! i) \<longrightarrow> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig k \<noteq> Bv (bs ! i)"
                by auto
              { fix k
                assume "t \<le> k"
                assume "k \<le> t + dly"
                hence "((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig k \<noteq> Bv (bs ! i)"
                  using ind `t \<le> k` `((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! i)`
                proof (induction "k - t" arbitrary: t dly)
                  case 0
                  then show ?case  by auto
                next
                  case (Suc x)
                  hence 0: "x = k - Suc t" and 1: "k \<le> Suc t + (dly - 1)"
                    by linarith+
                  have "k = Suc x + t"
                    using Suc by linarith
                  have 3: "\<forall>k. k \<le> Suc t + (dly - 1) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (k - 1) \<noteq> Bv (bs ! i) \<longrightarrow> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig k \<noteq> Bv (bs ! i)"
                    using Suc(4) 
                    by (metis (no_types, lifting) One_nat_def Suc.hyps(2) Suc.prems(1) Suc_pred add_Suc_shift less_add_same_cancel1 less_le_trans zero_less_Suc zero_less_diff)
                  have 4: "Suc t \<le> k"
                    using \<open>k = Suc x + t\<close> by linarith
                  have 5: "((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! i)"
                    using Suc  by (metis "3" diff_Suc_1 le_add1)
                  show ?case 
                    using Suc(1)[OF 0 1 3 4 5] by auto
                qed }
              with `((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! i)`
              show False
                by auto
            qed
            have "(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig n = Bv (bs ! i)) \<le> t + dly"
              using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig n = Bv (bs ! i)" and b="t + dly", OF *]
              by auto
            thus "bval_of (let time = if ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t = Bv (bs ! i) \<or> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! i) then t + dly
                                      else GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig n = Bv (bs ! i)
                           in if sig \<noteq> sig \<or> t' < t then ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t' else if t' < time then ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t else Bv (bs ! i)) = bs ! i"
              using False  using \<open>t + dly \<le> t'\<close> by auto
          next
            case True
            thus "bval_of (let time = if ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t = Bv (bs ! i) \<or> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! i) then t + dly
                                      else GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! i) \<and> ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig n = Bv (bs ! i)
                           in if sig \<noteq> sig \<or> t' < t then ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t' else if t' < time then ((snd \<omega>)(sig := to_bit i \<circ> snd \<omega> sig)) sig t else Bv (bs ! i)) = bs ! i"
              using \<open>t + dly \<le> t'\<close> by auto
          qed
          finally show " bs ! i = map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs] ! i"
            by auto
        qed (auto)
        thus " Lv sign bs =
    ((snd \<omega>)
     (sig :=
        \<lambda>n. let w' = \<lambda>b. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)];
                time =
                  if \<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. w' b sig (n - 1) \<noteq> w' b sig n)
                  then LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. w' b sig (n - 1) \<noteq> w' b sig n) else t + dly
            in if n < t then snd \<omega> sig n
               else if n < time then snd \<omega> sig t else Lv sign (map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) [0..<length bs])))
     sig t'"
          using \<open>t \<le> t'\<close> 
        proof ( cases "\<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd (to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)]) sig (n - 1) \<noteq> snd (to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)]) sig n)")
          case True
          let ?w' = "\<lambda>b. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)]"
          have "(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n)) \<le> t + dly"
            using True 
            by (metis (mono_tags, lifting) LeastI_ex)
          then show ?thesis 
            using True \<open>t + dly \<le> t'\<close> \<open>bs = map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs]\<close>
            by auto
        next
          case False
          then show ?thesis 
            using \<open>t + dly \<le> t'\<close> \<open>bs = map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs]\<close>
            by auto
        qed
      qed
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t'"
        by auto }
    moreover
    { assume "t' < t + dly"
      hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> s') \<tau>' s' t'"
        using `t \<le> t'` unfolding worldline_raw_def snd_conv by auto 
      also have "... = signal_of (\<sigma> s') (inr_post_raw' sig (Lv sign bs) (\<sigma> sig) \<tau> t dly) s' t'"
        unfolding \<tau>'_def by auto    
      also have "... = signal_of (\<sigma> s') (trans_post_raw sig (Lv sign bs) (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) t dly) s' t'"
        unfolding inr_post_raw'_def by auto
      also have "... = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
        unfolding `s' = sig`  signal_of_trans_post2[OF `t' < t + dly`] by auto
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
        by auto
      let ?w' = "\<lambda>b. snd (to_worldline_init_bit \<omega> sig b)[sig, t, dly := Bv (bs ! b)]"
      have "\<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n) \<or> 
            \<not> (\<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n))"
        by auto
      moreover
      { assume thereis: "\<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n)"
        let ?zeit = "LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n)"
        define zeit where "zeit = ?zeit"
        have "t < ?zeit" and "?zeit \<le> t + dly" and "\<exists>b\<in>set [0..<length bs]. ?w' b sig (?zeit - 1) \<noteq> ?w' b sig ?zeit"
          using LeastI_ex[OF thereis] by auto
        then obtain index where "index \<in> set [0..< length bs]" and "?w' index sig (?zeit - 1) \<noteq> ?w' index sig ?zeit"
          by auto
        have "?w' index sig (zeit - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t"
        proof (cases "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index)")
          case True
          then show ?thesis 
            using \<open>?zeit \<le> t + dly\<close>
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
            by (smt One_nat_def Suc_leI Suc_pred \<open>(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) \<le> t + dly\<close> \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> diff_less le_eq_less_or_eq le_zero_eq less_numeral_extra(1) less_trans not_le zeit_def)
        next
          case False
          hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
            by auto
          have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          proof (rule ccontr)
            assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
            hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            { fix n 
              assume "t \<le> n" and "n \<le> t + dly"
              hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> imp
              proof (induction "n - t" arbitrary: t dly)
                case 0 hence "n = t" by auto
                then show ?case 
                  using 0 by auto
              next
                case (Suc x)
                hence 0: "x = n - Suc t"
                  by auto
                have 2: "n \<le> Suc t + (dly - 1) "
                  using Suc by auto
                hence 1: "Suc t \<le> n "
                  using Suc by linarith
                hence "Suc t \<le> t + dly"
                  using Suc by linarith
                hence 3: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! index)"
                  using Suc(5-6) by auto
                have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using Suc(6) by auto
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using  Suc(1)[OF 0 1 2 3 4] by auto
                thus ?case
                  by auto
              qed }
            hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            thus False
              using False le_add1 by blast
          qed
          let ?time_again ="GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"

          have "t < ?time_again"
            using * 
          proof -
            have f1: "\<forall>p n na. (n::nat) \<le> Greatest p \<or> (\<exists>n. \<not> n \<le> na \<and> p n) \<or> \<not> p n"
              by (metis (lifting) Greatest_le_nat)
            obtain nn :: nat where
              f2: "Bv (bs ! index) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig nn \<and> Bv (bs ! index) \<noteq> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn - 1) \<and> nn \<le> t + dly \<and> t < nn"
              by (metis (no_types) "*")
            then have "nn \<le> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
              using f1 by force
            then show ?thesis
              using f2 by (meson less_le_trans)
          qed
          hence "?time_again - 1 < ?time_again"
            by auto
          have "?time_again \<le> t + dly" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time_again - 1) \<noteq> Bv (bs ! index)" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig ?time_again = Bv (bs ! index)"
            using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
            using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
            using GreatestI_ex_nat *  by smt
          have "?w' index sig (?time_again - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t"
            using \<open>t < ?time_again\<close> \<open>?time_again - 1 < ?time_again\<close> False
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
          moreover have "?w' index sig (?time_again) = Bv (bs ! index)"
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
            using False \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by auto
          ultimately have "?w' index sig (?time_again - 1) \<noteq> ?w' index sig ?time_again"
            using False by auto
          hence "?zeit \<le> ?time_again"
          proof -
            have "t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<and> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly \<and> (\<exists>n. n \<in> set [0..<length bs] \<and> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)))"
              using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly\<close> \<open>index \<in> set [0..<length bs]\<close> \<open>snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by blast
            then show ?thesis
              by (simp add: Bex_def_raw Least_le)
          qed
              
          show ?thesis 
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv
            by (smt False One_nat_def Suc_leI Suc_pred \<open>?zeit \<le> ?time_again\<close> \<open>t <
            (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig
            b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t,
            dly := Bv (bs ! b)] sig n))\<close> le_eq_less_or_eq le_zero_eq lessI less_trans not_le
            zeit_def)
        qed
        also have "... =  (to_bit index \<circ> snd (worldline_raw t \<sigma> \<theta> def \<tau>) sig) t"
          unfolding assms(1) fun_upd_def by auto
        also have "... = to_bit index (signal_of (\<sigma> sig) \<tau> sig t)"
          unfolding worldline_raw_def snd_conv by auto
        finally have "?w' index sig (zeit - 1) = to_bit index (signal_of (\<sigma> sig) \<tau> sig t)"
          by auto
        have "\<not> zeit < t"
          using \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd
          to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd
          to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> not_le zeit_def 
          by linarith
        have "\<not> zeit - 1 < t"
          using \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> zeit_def by linarith
        have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t  \<noteq> Bv (bs ! index)"
        proof (rule ccontr)
          assume "\<not> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)"
          hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t = Bv (bs ! index)"
            by auto
          have "zeit < t + dly \<or> zeit = t + dly"
            using \<open>(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) \<le> t + dly\<close> le_eq_less_or_eq zeit_def by blast 
          moreover
          { assume "zeit < t + dly"
            hence "?w' index sig zeit = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t"
              unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
              using \<open>\<not> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> \<open>\<not> zeit < t\<close> by auto
            hence False
              using \<open>?w' index sig (zeit - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close>
              \<open>?w' index sig (?zeit - 1) \<noteq> ?w' index sig (?zeit)\<close> zeit_def by auto }
          moreover
          { assume "zeit = t + dly"
            hence "?w' index sig zeit = Bv (bs ! index)"
              unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
              using \<open>\<not> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> by auto
            with \<open>?w' index sig (zeit - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close> have False
              unfolding \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t = Bv (bs ! index)\<close>
              using \<open>?w' index sig (zeit - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close>
              \<open>?w' index sig (?zeit - 1) \<noteq> ?w' index sig (?zeit)\<close> zeit_def by auto }
          ultimately show False
            by auto
        qed
        hence "?w' index sig (zeit - 1) \<noteq> Bv (bs ! index)"
          using \<open>snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig (zeit -
          1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close> by auto
        have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index) \<Longrightarrow> zeit = t + dly"
        proof (rule ccontr)
          assume as: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index)"
          assume "\<not> zeit = t + dly" hence "zeit < t + dly"
            using \<open>?zeit \<le> t + dly\<close> unfolding zeit_def by auto
          hence "?w' index sig zeit = ?w' index sig (zeit - 1)"
            using \<open>\<not> zeit < t\<close> \<open>\<not> zeit - 1 < t\<close>  as
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
          thus False
            using \<open>?w' index sig (?zeit - 1) \<noteq> ?w' index sig ?zeit\<close> unfolding zeit_def
            by auto
        qed
        have "?w' index sig (zeit) =  Bv (bs ! index) "
        proof (cases "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index)")
          case True
          then show ?thesis 
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index) \<Longrightarrow> zeit = t + dly\<close>
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
        next
          case False
          let ?time_again ="GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          have cond1: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)" and cond2: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
            using False  using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> by blast+
          have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          proof (rule ccontr)
            assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
            hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            { fix n 
              assume "t \<le> n" and "n \<le> t + dly"
              hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> imp
              proof (induction "n - t" arbitrary: t dly)
                case 0 hence "n = t" by auto
                then show ?case 
                  using 0 by auto
              next
                case (Suc x)
                hence 0: "x = n - Suc t"
                  by auto
                have 2: "n \<le> Suc t + (dly - 1) "
                  using Suc by auto
                hence 1: "Suc t \<le> n "
                  using Suc by linarith
                hence "Suc t \<le> t + dly"
                  using Suc by linarith
                hence 3: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! index)"
                  using Suc(5-6) by auto
                have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using Suc(6) by auto
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using  Suc(1)[OF 0 1 2 3 4] by auto
                thus ?case
                  by auto
              qed }
            hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            thus False
              using False le_add1 by blast
          qed
          { assume "\<not> ?w' index sig zeit = Bv (bs ! index)"
            hence "zeit < ?time_again"
              using cond1 cond2
              unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
              using \<open>\<not> zeit < t\<close> by presburger
            hence "?w' index sig zeit = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t"
              using cond1 cond2
              unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
              by (simp add: \<open>\<not> zeit < t\<close>)
            hence "?w' index sig zeit = ?w' index sig (zeit - 1)"
              using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t = (to_bit index \<circ> snd (worldline_raw t \<sigma> \<theta> def \<tau>) sig) t\<close> \<open>(to_bit index \<circ> snd (worldline_raw t \<sigma> \<theta> def \<tau>) sig) t = to_bit index (signal_of (\<sigma> sig) \<tau> sig t)\<close> \<open>snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig (zeit - 1) = to_bit index (signal_of (\<sigma> sig) \<tau> sig t)\<close> by auto
            hence False
              using \<open>?w' index sig (?zeit - 1) \<noteq> ?w' index sig (?zeit)\<close> zeit_def 
              by auto }
          thus ?thesis 
            by auto
        qed
        hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> 
                zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
          unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv
        proof -
          assume "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
          let ?time_again ="GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          have cond1: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)" and cond2: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> apply blast
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> by blast
          have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          proof (rule ccontr)
            assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
            hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            { fix n 
              assume "t \<le> n" and "n \<le> t + dly"
              hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> imp
              proof (induction "n - t" arbitrary: t dly)
                case 0 hence "n = t" by auto
                then show ?case 
                  using 0 by auto
              next
                case (Suc x)
                hence 0: "x = n - Suc t"
                  by auto
                have 2: "n \<le> Suc t + (dly - 1) "
                  using Suc by auto
                hence 1: "Suc t \<le> n "
                  using Suc by linarith
                hence "Suc t \<le> t + dly"
                  using Suc by linarith
                hence 3: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! index)"
                  using Suc(5-6) by auto
                have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using Suc(6) by auto
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using  Suc(1)[OF 0 1 2 3 4] by auto
                thus ?case
                  by auto
              qed }
            hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            thus False
              using cond2 le_add1 by blast
          qed          
          have "t < ?time_again"
            using * 
          proof -
            have f1: "\<forall>p n na. (n::nat) \<le> Greatest p \<or> (\<exists>n. \<not> n \<le> na \<and> p n) \<or> \<not> p n"
              by (metis (lifting) Greatest_le_nat)
            obtain nn :: nat where
              f2: "Bv (bs ! index) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig nn \<and> Bv (bs ! index) \<noteq> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn - 1) \<and> nn \<le> t + dly \<and> t < nn"
              by (metis (no_types) "*")
            then have "nn \<le> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
              using f1 by force
            then show ?thesis
              using f2 by (meson less_le_trans)
          qed
          hence "?time_again - 1 < ?time_again"
            by auto
          have "?time_again \<le> t + dly" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time_again - 1) \<noteq> Bv (bs ! index)" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig ?time_again = Bv (bs ! index)"
            using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
            using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
            using GreatestI_ex_nat *  by smt
          have "?w' index sig (?time_again - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t"
            using \<open>t < ?time_again\<close> \<open>?time_again - 1 < ?time_again\<close> cond1 cond2
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
          moreover have "?w' index sig (?time_again) = Bv (bs ! index)"
            unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
            using cond1 cond2 \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by auto
          ultimately have "?w' index sig (?time_again - 1) \<noteq> ?w' index sig ?time_again"
            using cond1 cond2 by auto
          hence "?zeit \<le> ?time_again"
          proof -
            have "t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<and> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly \<and> (\<exists>n. n \<in> set [0..<length bs] \<and> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)))"
              using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly\<close> \<open>index \<in> set [0..<length bs]\<close> \<open>snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig index[sig, t, dly := Bv (bs ! index)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by blast
            then show ?thesis
              by (simp add: Bex_def_raw Least_le)
          qed
          hence "zeit \<le> ?time_again"
            unfolding zeit_def by auto
          moreover have "\<not> zeit < ?time_again"
            by (smt One_nat_def Suc_leI Suc_pred \<open>?w' index sig (?time_again - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close> 
            \<open>?w' index sig (?time_again) = Bv (bs ! index)\<close> \<open>?w' index sig (zeit) =  Bv (bs ! index)\<close> 
            \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig
            (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs !
            index))\<close> \<open>t < ?zeit\<close> cond1 gr_implies_not0
            leD not_less_iff_gr_or_eq prod.sel(2) worldline_inert_upd_def zeit_def)
          thus ?thesis
            using calculation le_eq_less_or_eq by blast
        qed
        hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> 
               ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit) = Bv (bs ! index)"
        proof -
          assume "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
          hence "zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by blast
          have cond1: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)" and cond2: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> apply blast
            using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> by blast
          have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
          proof (rule ccontr)
            assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
            hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            { fix n 
              assume "t \<le> n" and "n \<le> t + dly"
              hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! index)\<close> imp
              proof (induction "n - t" arbitrary: t dly)
                case 0 hence "n = t" by auto
                then show ?case 
                  using 0 by auto
              next
                case (Suc x)
                hence 0: "x = n - Suc t"
                  by auto
                have 2: "n \<le> Suc t + (dly - 1) "
                  using Suc by auto
                hence 1: "Suc t \<le> n "
                  using Suc by linarith
                hence "Suc t \<le> t + dly"
                  using Suc by linarith
                hence 3: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! index)"
                  using Suc(5-6) by auto
                have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using Suc(6) by auto
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
                  using  Suc(1)[OF 0 1 2 3 4] by auto
                thus ?case
                  by auto
              qed }
            hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)"
              by auto
            thus False
              using cond2 le_add1 by blast
          qed         
          thus ?thesis
          proof -
            obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
              f1: "\<And>p n na nb. (\<not> p n \<or> p (Greatest p) \<or> p (nn p na)) \<and> (\<not> p nb \<or> \<not> nn p na \<le> na \<or> p (Greatest p))"
              by (metis (lifting) GreatestI_ex_nat)
            then have "\<And>n na. (\<not> n \<le> t + dly \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! index)) \<or> zeit \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index) \<or> nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) na \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) na - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) na) = Bv (bs ! index)"
              by (smt \<open>zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close>) 
            moreover
            { assume "\<exists>n\<le>t + dly. ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)"
              { assume "\<exists>n. (n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<and> (\<not> zeit \<le> t + dly \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit \<noteq> Bv (bs ! index))"
                then have "\<exists>n. (n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<and> (\<not> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) - 1) = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<noteq> Bv (bs ! index))"
                  using \<open>zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by force
                then have "\<exists>n. \<not> nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n \<le> t + dly \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n - 1) = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n) \<noteq> Bv (bs ! index)"
                  using f1 by smt }
              then have "(\<exists>n. \<not> nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>) (sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n \<le> t + dly \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n - 1) = Bv (bs ! index) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (nn (\<lambda>n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) n) \<noteq> Bv (bs ! index)) \<or> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index)"
                by blast }
            ultimately show ?thesis
              using "*" by blast
          qed
        qed
        have "\<And>b2. b2 < length bs \<Longrightarrow> bval_of (snd to_worldline_init_bit \<omega> sig b2[sig, t, dly := Bv (bs ! b2)] sig t') = bval_of (to_bit b2 (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
        proof-
          fix b
          assume "b < length bs"
          have *: "bval_of (snd (to_worldline_init_bit \<omega> sig b)[sig, t, dly := Bv (bs ! b)] sig t') =  bval_of
       (let time =
              if ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t = Bv (bs ! b) \<or> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! b) then t + dly
              else GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)
        in if t' < time then ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t else Bv (bs ! b))"
            using `t \<le> t'` unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
          have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t = Bv (bs ! b) \<or> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! b) \<or> 
                ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)"
            by auto
          moreover
          { assume "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t = Bv (bs ! b) \<or> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! b)"
            hence "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                   bval_of (((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t)"
              using `t' < t + dly` unfolding * by auto
            also have "... =  bval_of (to_bit b (signal_of (\<sigma> sig) \<tau> sig t))"
              unfolding assms(1) worldline_raw_def snd_conv by auto
            also have "... = bval_of (to_bit b (\<sigma> sig))"
            proof -
              have "inf_time (to_trans_raw_sig \<tau>) sig t = None"
                using assms(2) unfolding context_invariant_def 
              proof -
                assume a1: "(\<forall>n\<le>t. \<tau> n = 0) \<and> \<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)} \<and> (\<forall>n\<ge>t. \<theta> n = 0)"
                have "\<forall>f a n. \<exists>na. (na \<le> n \<or> inf_time f (a::'a) n = None) \<and> (na \<in> keys (f a) \<or> inf_time f a n = None)"
                  by (metis (lifting) inf_time_def)
                then obtain nn :: "('a \<Rightarrow> nat \<Rightarrow> val option) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
                  f2: "\<And>f a n. (nn f a n \<le> n \<or> inf_time f a n = None) \<and> (nn f a n \<in> keys (f a) \<or> inf_time f a n = None)"
                  by moura
                moreover
                { assume "nn (to_trans_raw_sig \<tau>) sig t \<le> t"
                  then have "\<tau> (nn (to_trans_raw_sig \<tau>) sig t) sig = None"
                    using a1 by (simp add: zero_fun_def zero_option_def)
                  then have ?thesis
                    using f2 by (metis domIff dom_def keys_def to_trans_raw_sig_def zero_option_def) }
                ultimately show ?thesis
                  by blast
              qed
              thus ?thesis
                unfolding to_signal_def comp_def by auto
            qed 
            also have "... = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
            proof (cases "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t'")
              case None
              then show ?thesis 
                unfolding to_signal_def comp_def by auto
            next
              case (Some a)
              have "t < a"
              proof (rule ccontr)
                assume "\<not> t < a" hence "a \<le> t" by auto
                have "a \<in> keys (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)" and "a \<le> t'"
                  using Some unfolding inf_time_def  by (meson Some inf_time_some_exists)+
                hence " purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> 0"
                  unfolding keys_def to_trans_raw_sig_def by auto
                hence "\<tau> a sig \<noteq> 0"
                  unfolding purge_raw'_def combine_trans_bit_def using `a \<le> t` by auto
                with assms(2) show False
                  unfolding context_invariant_def using `a \<le> t`  by (simp add: zero_fun_def)
              qed
              have "a < t + dly"
                using `t' < t + dly`  by (meson Some inf_time_some_exists le_less_trans)
              have "a \<in> fold (\<union>)
                  (map (keys \<circ> (\<lambda>\<tau> n. \<tau> n sig) \<circ> snd)
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
                  {}"
              proof (rule ccontr)
                assume anotin: "a \<notin> fold (\<union>)
                  (map (keys \<circ> (\<lambda>\<tau> n. \<tau> n sig) \<circ> snd)
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                      (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
                  {}"
                have "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> 0"
                  using inf_time_some_exists[OF Some] 
                  unfolding keys_def to_trans_raw_sig_def by auto
                moreover have "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = 0"
                  using anotin `a < t + dly` `t < a` unfolding purge_raw'_def combine_trans_bit_def zero_option_def
                  Let_def to_trans_raw_sig_def by auto
                ultimately show False 
                  by auto
              qed
              hence " (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig a) = Some
                             (Lv sign         
                               (map (\<lambda>p. bval_of ((to_signal (get_time p) \<circ> (\<lambda>\<tau> sig n. \<tau> n sig)) (snd p) sig a))
                                 (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                                   (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))"
                (is "_ = Some ?comp") 
                using `t < a` `a < t + dly` unfolding to_trans_raw_sig_def purge_raw'_def combine_trans_bit_def by auto
              have len: "b < length (zip (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
                using `b < length bs` by auto
              have len2: "b < length (map (\<lambda>n. (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..<length bs])"
                using `b < length bs` by auto
              have len3: "b < length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])"
                using `b < length bs` by auto
              have len4: "b < length ([0..< length bs])"
                using `b < length bs` by auto
              have len5: "[0 ..< length bs] ! b = b"
                using `b < length bs` by auto
              have "to_bit b ?comp = Bv (bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))
                                                             (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) n) sig a))"
                unfolding to_bit.simps comp_def nth_map[OF len] to_trans_raw_sig_def nth_zip[OF len2 len3] nth_map[OF len4] len5 fst_conv 
                snd_conv by auto
              also have "... =  Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)"
              proof -
                have " to_bit b (signal_of (\<sigma> sig) \<tau> sig t) = Bv (bs ! b) \<or> to_bit b (signal_of (\<sigma> sig) \<tau> sig (t + dly)) \<noteq> Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t = Bv (bs ! b) \<or> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! b)`
                  unfolding assms(1) worldline_raw_def snd_conv by auto
                hence "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t = Bv (bs ! b) \<or> 
                       signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) \<noteq> Bv (bs ! b)"
                  unfolding to_bit_signal_of'_eq[THEN sym] by auto
                hence "inf_time (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)))) sig a = None"
                  unfolding to_trans_raw_sig_def purge_raw_def comp_def
                  using assms(2) unfolding context_invariant_def Let_def inf_time_none_iff[THEN sym]
                  by (smt \<open>a < t + dly\<close> domIff fun_upd_eqD fun_upd_triv greaterThanAtMost_iff leI
                  le_trans less_imp_le_nat option.simps(4) override_on_apply_in
                  override_on_apply_notin to_trans_raw_bit_def zero_fun_def zero_option_def)
                thus ?thesis
                  unfolding to_signal_def comp_def by auto
              qed
              then show ?thesis 
                unfolding to_signal_def comp_def
                by (smt Some \<open>Bv (bval_of (signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs !
                b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow>
                b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a)) = Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv
                sign bs \<Rightarrow> bs ! b)\<close> \<open>to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig
                a = Some (Lv sign (map (\<lambda>p. bval_of ((to_signal (get_time p) \<circ> (\<lambda>\<tau> sig n. \<tau> n sig))
                (snd p) sig a)) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))
                [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv
                (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))\<close>
                calculation option.sel option.simps(5) to_bit.simps(1) to_bit.simps(2) val.case_eq_if
                val.collapse(1) val.collapse(2))
            qed 
            finally have "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                          bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              by auto }
          moreover
          { assume 1: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)"
            let ?time = "(GREATEST n. n \<le> t + dly  \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
            have exist: "\<exists>n. t < n \<and> n \<le> t + dly  \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b) "
            proof (rule ccontr)
              assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly  \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
              hence ind: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                by auto
              { fix n
                assume "n \<le> t + dly"
                assume "t < n"
                hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                  using ind 1
                proof (induction "n - t" arbitrary: t dly)
                  case 0
                  then show ?case using 1  using le_eq_less_or_eq by auto
                next
                  case (Suc m)
                  hence h0: "m = n - Suc t"
                    by linarith
                  have h1: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                    using Suc(4) by simp
                  have h2: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (Suc t + (dly - 1)) = Bv (bs ! b)"
                    by (metis (no_types, lifting) Suc.prems(2) Suc.prems(3) Suc_pred add_Suc_shift diff_Suc_1 le_add1 le_eq_less_or_eq lessI less_add_same_cancel1)
                  then show ?case 
                    using Suc.hyps(2)  Suc.hyps(1) Suc.prems(1) Suc_lessI h0 h1 by blast
                qed }
              thus False
                using 1 \<open>t \<le> t'\<close> \<open>t' < t + dly\<close> by auto
            qed
            hence exist': "\<exists>n. n \<le> t + dly  \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b) "
              by auto
            have "?time \<le> t + dly" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time - 1) \<noteq> Bv (bs ! b)" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time = Bv (bs ! b)"
              using GreatestI_ex_nat[OF exist'] by auto
            have "t < ?time"
            proof (rule ccontr)
              assume "\<not> t < ?time" hence "?time \<le> t" by auto
              obtain n where "t < n" and "n \<le> t + dly" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b)"
                and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)" using exist by auto
              hence "n \<le> ?time"
                using Greatest_le_nat[where k="n" and b="t + dly"] by auto
              with `t < n` and `?time \<le> t` show False
                by auto
            qed
            have "t' < ?time \<or> ?time \<le> t'" by auto
            moreover            
            { assume "?time \<le> t'"
              hence "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = (bs ! b)"
                unfolding * using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig :=
                to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)\<close> by auto
              also have "... = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              proof (cases "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t'")
                case None
                hence "Ball (dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)) ((<) t')"
                  unfolding inf_time_none_iff[THEN sym] by auto
                have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time - 1) \<noteq> Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time = Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                ultimately have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig) ?time sig \<noteq> None"
                  by (metis (no_types, lifting) signal_of_less_sig to_bit_signal_of' zero_option_def)
                have h0: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                have h1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                have exist_mapping: "\<exists>n>t. n \<le> t + dly \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = Some (Bv (bs ! b))"
                  using switch_signal_ex_mapping_gen[OF h0 h1]
                  by (simp add: \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> to_trans_raw_bit_def zero_fun_def zero_option_def)
                have *: "length (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) = 
                             length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig
                               (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                      [0..<length bs])"
                  by auto  
                have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig
                           (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?time sig \<noteq> None 
                  \<or> purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig
                           (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?time sig = None"
                  by auto
                moreover
                { assume purge_neq_none: "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig
                           (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?time sig \<noteq> None"
                  hence time_in: "?time \<in> fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                     (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig
                             (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                    [0..<length bs]))) {}"
                    using `b < length bs` 
                    unfolding map_map[THEN sym] map_snd_zip[OF *] member_fold_union2
                    keys_def zero_option_def  by (auto intro!: bexI[where x="b"] simp add: to_trans_raw_sig_def) 
                  have "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) ?time sig = 
                        combine_trans_bit \<tau>
                        (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                          (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig
                                     (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n)))
                            [0..<length bs]))
                        sign sig t dly ?time sig"
                    unfolding purge_raw'_def by auto
                  also have "... \<noteq> None"
                    unfolding combine_trans_bit_def 
                    using time_in \<open>?time \<le> t + dly\<close> \<open>t < ?time\<close> by auto
                  finally have False
                  proof -
                    assume a1: "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None"
                    have "\<not> t' < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
                      using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) \<le> t'\<close> leD by blast
                    then show ?thesis
                      using a1 by (simp add: \<open>Ball (dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)) ((<) t')\<close> domIff to_trans_raw_sig_def)
                  qed
                  hence " bs ! b = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                    by auto }
                moreover
                { assume "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) ?time sig = None"
                  hence "?time < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) 
                       \<or> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) < ?time"
                    using `t < ?time` `?time \<le> t'` `t' < t + dly` h0 h1
                    unfolding purge_raw_def Let_def 
                    by (smt Un_iff \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig \<noteq> None\<close> greaterThanAtMost_iff
                    greaterThanLessThan_iff override_on_apply_notin)
                  moreover have "the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) < ?time \<Longrightarrow> False"
                  proof -
                    assume "the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) < ?time"
                    have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) \<noteq> None"
                    proof -
                      have "None \<noteq> to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
                        by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None\<close> to_trans_raw_sig_def)
                      then show ?thesis
                        using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) \<le> t + dly\<close> inf_time_noneE2 zero_option_def by fastforce
                    qed
                    then obtain time' where "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) = Some time'"
                      by auto
                    hence "to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time = None"
                      using \<open>?time \<le> t + dly\<close> \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t +
                      dly)) < ?time\<close> inf_time_someE by fastforce
                    with `(to_trans_raw_bit (\<sigma> sig) \<tau> b sig) ?time sig \<noteq> None` show False
                      by (simp add: to_trans_raw_sig_def)
                  qed
                  ultimately have "?time < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))" (is "_ < ?time'")
                    by auto
                  obtain val where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val" 
                    using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig \<noteq> None\<close> by auto
                  hence "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time = val"
                    using trans_some_signal_of'[where \<tau>="to_trans_raw_bit (\<sigma> sig) \<tau> b sig" and n="?time" and \<sigma>="(\<lambda>x. _)(sig:= val)"]
                    by auto
                  hence "val = Bv (bs ! b)"
                    using to_bit_signal_of'[OF \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)\<close>]
                    by auto
                  have "\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly"
                    by (metis (mono_tags, lifting) \<open>?time \<le> t + dly\<close> \<open>\<And>thesis. (\<And>val.
                    to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> keys_def
                    mem_Collect_eq option.simps(3) to_trans_raw_sig_def zero_option_def)
                  hence time'_eq: "?time' = (GREATEST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<and> k \<le> t + dly)"
                    unfolding inf_time_def by auto
                  hence "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)" and "?time' \<le> t + dly"
                    using GreatestI_ex_nat 
                    by (metis (mono_tags, lifting) \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly\<close> inf_time_def inf_time_ex1 inf_time_some_exists)+
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig"
                  proof (rule ccontr)
                    assume "\<not> to_trans_raw_bit (\<sigma> sig)  \<tau> b sig ?time' sig = to_trans_raw_bit (\<sigma> sig)  \<tau> b sig ?time sig"
                    hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time =  val"
                      using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> b sig" "?time" "sig" "(\<lambda>x. _)(sig := val)"]
                      using \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig :=
                      to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ>
                      snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val\<close> by auto
                    then obtain val' where "to_trans_raw_bit (\<sigma> sig)  \<tau> b sig ?time' sig = Some val'"
                    proof -
                      assume "\<And>val'. to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) sig = Some val' \<Longrightarrow> thesis"
                      then show ?thesis
                        by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig)\<close> domIff dom_def keys_def not_None_eq to_trans_raw_sig_def zero_option_def)
                    qed
                    hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time' =  val'"
                      using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> b sig" "?time" "sig" "(\<lambda>x. _)(sig := val')"] time'_eq
                      by (meson trans_some_signal_of')
                    also have "... \<noteq> val"
                      using \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val\<close> \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) sig = Some val'\<close> \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) sig \<noteq> to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig\<close> by auto
                    finally have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time' \<noteq> 
                                  signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time "
                      using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) = val\<close> by blast
                    have "t < ?time'"
                      using \<open>?time < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close> by linarith
                    have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time') = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time'"
                      using `t < ?time'` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                    moreover have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time"
                      using `t < ?time` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                    ultimately have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time') \<noteq> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time)"
                      using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) \<noteq> signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close> by auto
                      
                    have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time' = val'"
                      using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> b sig" "?time'" "sig" "(\<lambda>x. _)(sig := val')"] \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig ?time' sig = Some val'\<close>
                      by auto
                    have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) = 
                          inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly)"
                      using time'_eq 
                    proof -
                      obtain nn :: nat where
                        f1: "nn \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig) \<and> nn \<le> t + dly"
                          using \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig). k \<le> t + dly\<close> by blast
                        have f2: "to_signal (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! b)) (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly) = Bv (bs ! b)"
                      using h1 by auto
                      have f3: "\<forall>v n a f. to_signal v f (a::'a) n = the (f a (the (inf_time f a n))) \<or> inf_time f a n = None"
                        by (simp add: option.case_eq_if to_signal_def)
                        have f4: "\<forall>f. f (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly)))) = f (Some val')"
                      by (metis (no_types) \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) sig = Some val'\<close> to_trans_raw_sig_def)
                        have "Bv (bs ! b) \<noteq> val'"
                          by (metis (no_types) \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) = Bv (bs ! b)\<close> \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly)))\<close> \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) \<noteq> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close> \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) = val'\<close>)
                      then have f5: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly) = None"
                      using f4 f3 f2 option.sel 
                        by (metis \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) sig = Some val'\<close> to_trans_raw_sig_def)
                      have "\<forall>n. Some (GREATEST na. na \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig) \<and> na \<le> n) = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig n \<or> \<not> nn \<le> n"
                      using f1 by (simp add: inf_time_def)
                        then show ?thesis
                      using f5 f1 by force
                    qed
                    hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (t + dly) = 
                          signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time'"
                      unfolding to_signal_def comp_def by auto
                    hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time' = Bv (bs ! b)"
                      using h1 by auto
                    have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time) = Bv (bs ! b)"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time) = Bv (bs ! b)\<close> by blast
                    have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time') = Bv (bs ! b)"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time') = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig ?time'\<close>
                      using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) = Bv (bs ! b)\<close> by auto
                    show False
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) = Bv (bs ! b)\<close> \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) = Bv (bs ! b)\<close> \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> b sig)) sig (t + dly))) \<noteq> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close> by auto
                  qed
                  have "?time = ?time'"
                  proof (rule Greatest_equality)
                    have "t \<le> ?time' - 1" using \<open>?time < ?time'\<close> \<open>t < ?time\<close> by linarith
                    moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)"
                      unfolding to_bit_signal_of'_eq[THEN sym]
                    proof (cases "\<exists>n. t < n \<and> n < ?time' \<and> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig \<noteq> None")
                      case False
                      hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time' - 1 \<Longrightarrow> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig = 0"
                        by (auto simp add: zero_option_def)
                      have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                              signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t"
                        using signal_of_less_ind'[of "t" "?time' - 1" "to_trans_raw_bit (\<sigma> sig) \<tau> b sig" "sig", OF none] `t \<le> ?time' - 1`
                        by auto                    
                      also have "... \<noteq> (Bv (bs ! b))"
                        using h0 to_bit_signal_of'_eq by force
                      finally show " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                        by auto
                    next
                      case True
                      let ?key1 = "(GREATEST n. t < n \<and> n < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)"
                      from True have "t < ?key1" and "?key1 < ?time'" and " to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None"
                        using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
                      have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time' \<Longrightarrow> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = None"
                        using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig x sig \<noteq> None" and b="?time'"]
                        by (smt \<open>t < (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
                      have inf_some: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (?time' - 1) = Some ?key1"
                      proof (rule inf_time_someI)
                        show "?key1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
                      next
                        show "?key1 \<le> ?time' - 1"
                          using `?key1 < ?time'`  by linarith
                      next
                        { fix ta
                          assume "ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          assume "ta \<le> ?time' - 1"
                          assume "?key1 < ta"
                          hence "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ta sig = None"
                            using *[OF `?key1 < ta`] `ta \<le> ?time' - 1` by simp
                          hence "ta \<notin> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                            by (simp add: domIff to_trans_raw_sig_def)
                          with `ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)` have False by auto }
                        thus "\<forall>ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). ta \<le> ?time' - 1 \<longrightarrow> ta \<le> ?key1"
                          using not_le_imp_less by blast
                      qed
                      have non_stut: " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) (to_bit b o \<sigma>) sig"
                        using assms(5) non_stuttering_to_trans_raw_bit by force
                      hence "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig  ?key1 sig) \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig"
                      proof -
                        have "?key1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                        moreover have "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          using \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> by blast
                        moreover have "\<forall>k. ?key1 < k \<and> k < ?time' \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                          zero_option_def)
                        ultimately show ?thesis    
                          using `?key1 < ?time'` non_stut unfolding non_stuttering_def
                          by (simp add: to_trans_raw_sig_def)
                      qed
                      moreover have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Some (Bv (bs ! b))"
                      proof -
                        have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig)"
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig\<close> by auto
                        also have "... = Bv (bs ! b)"
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val\<close> \<open>val = Bv (bs ! b)\<close> by auto
                        finally show ?thesis
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (?time) sig = Some val\<close>
                          \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig
                          (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig = to_trans_raw_bit
                          (\<sigma> sig) \<tau> b sig (?time) sig\<close> by auto
                      qed
                      ultimately have neq: "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) \<noteq> Some (Bv (bs ! b))"
                        by auto
                      then obtain valu where "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) = Some valu" and "valu \<noteq> Bv (bs ! b)"
                        using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> by blast
                      have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                            the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?key1)"
                        using inf_some unfolding to_signal_def comp_def
                        by auto
                      also have "... \<noteq> Bv (bs ! b)"
                        using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> neq 
                        by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. t < n \<and> n < the
                        (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))
                        \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None) sig = Some valu\<close> option.sel
                        to_trans_raw_sig_def)
                      finally show "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                        by blast
                    qed
                    ultimately have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) = to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1))"
                      unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def by auto
                    hence *: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b)"
                      using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)\<close> by auto
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                      using \<open>t \<le> ?time' - 1\<close> exist_mapping
                      using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = Some (Bv (bs ! b))" and b="t + dly"]
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val\<close> 
                            \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig\<close> \<open>val = Bv (bs ! b)\<close> by auto
                    have "to_bit b (signal_of (\<sigma> sig) \<tau> sig ?time') = (Bv (bs ! b))"
                      using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig) \<tau> b sig", OF `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))`]
                      using to_bit_signal_of'_eq by fastforce
                    hence " ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) = Bv (bs ! b)"
                      unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def 
                      using \<open>t \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) - 1\<close> by auto
                    thus "?time' \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b) \<and>
                                             ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time' = Bv (bs ! b)"    
                      using * `?time' \<le> t + dly` by auto  
                  next
                    have "t \<le> ?time' - 1" using \<open>?time < ?time'\<close> \<open>t < ?time\<close> by linarith
                    fix y
                    assume "y \<le> t + dly \<and>  ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)"
                    hence "y \<le> t + dly" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y) = Bv (bs ! b)"
                      by auto
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                      using \<open>t \<le> ?time' - 1\<close> exist_mapping
                      using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = Some (Bv (bs ! b))" and b="t + dly"]
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val\<close> 
                            \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig\<close> \<open>val = Bv (bs ! b)\<close> by auto
                    hence "t < ?time'"
                      by (meson \<open>t < ?time\<close> \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) \<Longrightarrow> False\<close> le_less_trans not_le)
                    have "y \<le> t \<or> t < y"
                      by auto
                    moreover
                    { assume "y \<le> t"
                      hence "y < ?time'" using `t < ?time'` by linarith }
                    moreover
                    { assume "t < y"
                      hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) =  to_bit b (signal_of (\<sigma> sig) \<tau> sig (y - 1))"
                        unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                      hence 0: "... \<noteq> (Bv (bs ! b))"
                        using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)\<close> by auto
                      have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y =  to_bit b (signal_of (\<sigma> sig) \<tau> sig y)"
                        using `t < y`  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                      hence 1: "... = Bv (bs ! b)"
                        using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)\<close> by auto
                      have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                      proof (rule ccontr)
                        assume "\<not> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                        then obtain x' where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None \<or> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                          using domIff by fastforce
                        moreover
                        { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None"
                          hence "signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = 
                                 signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (y - 1)"
                            by (intro signal_of_less_sig)(simp add: zero_option_def)
                          with 0 1 have False 
                            by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None\<close> signal_of_less_sig to_bit_signal_of' zero_option_def) }
                        moreover
                        { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                          hence "signal_of ((Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = x'" and "x' \<noteq> (Bv (bs ! b))"
                            using trans_some_signal_of' by fastforce+
                          with 1 have False 
                            unfolding to_bit_signal_of'_eq by auto }
                        ultimately show False
                          by auto
                      qed
                      with `y \<le> t + dly` have "y \<le> ?time'"
                        unfolding time'_eq 
                        apply (intro Greatest_le_nat)
                        unfolding keys_def to_trans_raw_sig_def zero_option_def by auto }
                    ultimately show "y \<le> ?time'"
                      by auto
                  qed
                  hence False
                    using `?time < ?time'` by auto
                  hence " bs ! b = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                    by auto }
                ultimately show " bs ! b = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                  by auto
              next
                case (Some a)
                hence "signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = the (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig)"
                  by (simp add: to_signal_def to_trans_raw_sig_def)
                have "\<forall>t\<in>dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig). t \<le> t' \<longrightarrow> t \<le> a"
                  using inf_time_someE[OF Some] by auto
                have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time - 1) \<noteq> Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time = Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                ultimately have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig) ?time sig \<noteq> None"
                  by (metis (no_types, lifting) signal_of_less_sig to_bit_signal_of' zero_option_def)
                have h0: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                have h1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                let ?time' = "the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))"
                obtain val where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val" 
                    using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig \<noteq> None\<close> by auto
                have "\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly"
                 by (metis (mono_tags, lifting) \<open>?time \<le> t + dly\<close> \<open>\<And>thesis. (\<And>val.
                    to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> keys_def
                    mem_Collect_eq option.simps(3) to_trans_raw_sig_def zero_option_def)
                hence time'_eq: "?time' = (GREATEST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<and> k \<le> t + dly)"
                  unfolding inf_time_def by auto
                hence "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)" and "?time' \<le> t + dly"
                  using GreatestI_ex_nat 
                  by (metis (mono_tags, lifting) \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly\<close> inf_time_def inf_time_ex1 inf_time_some_exists)+
                have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)"
                proof -
                  have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) = Some ?time'"
                    by (simp add: \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly\<close> inf_time_def)
                  thus "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)"
                    using h1 unfolding to_signal_def comp_def 
                    by (metis option.simps(5) to_trans_raw_sig_def)
                qed
                have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig) = Bv (bs ! b)"
                proof- 
                  have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time = Bv (bs ! b)"
                    using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)\<close>
                    unfolding to_bit_signal_of'_eq[THEN sym] by auto
                  moreover have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig ?time = Some ?time"
                  proof (intro inf_time_someI)
                    show "?time \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                    proof -
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None"
                      by (metis (full_types) \<open>\<And>thesis. (\<And>val. to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> option.simps(3))
                    then show ?thesis
                        by (simp add: domIff to_trans_raw_sig_def)
                    qed
                  qed (auto)
                  ultimately show ?thesis
                    unfolding to_signal_def comp_def 
                    by (simp add: to_trans_raw_sig_def)
                qed
                have "?time = ?time'"
                proof (rule Greatest_equality)
                  have "t \<le> ?time' - 1" 
                  proof (rule ccontr)
                    assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                      by auto
                    hence "?time' \<le> t" by auto
                    hence "\<tau> ?time' sig = None"
                      using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig \<noteq> None"
                      using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> 
                      by (metis domIff dom_is_keys to_trans_raw_sig_def)
                    thus "False"
                      using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                  qed
                  moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)"
                    unfolding to_bit_signal_of'_eq[THEN sym]
                  proof (cases "\<exists>n. t < n \<and> n < ?time' \<and> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig \<noteq> None")
                    case False
                    hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time' - 1 \<Longrightarrow> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig = 0"
                      by (auto simp add: zero_option_def)
                    have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                            signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t"
                      using signal_of_less_ind'[of "t" "?time' - 1" "to_trans_raw_bit (\<sigma> sig) \<tau> b sig" "sig", OF none] `t \<le> ?time' - 1`
                      by auto                    
                    also have "... \<noteq> (Bv (bs ! b))"
                      using h0 to_bit_signal_of'_eq by force
                    finally show " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                      by auto
                  next
                    case True
                    let ?key1 = "(GREATEST n. t < n \<and> n < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)"
                    from True have "t < ?key1" and "?key1 < ?time'" and " to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None"
                      using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
                    have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time' \<Longrightarrow> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = None"
                      using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig x sig \<noteq> None" and b="?time'"]
                      by (smt \<open>t < (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
                    have inf_some: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (?time' - 1) = Some ?key1"
                    proof (rule inf_time_someI)
                      show "?key1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
                    next
                      show "?key1 \<le> ?time' - 1"
                        using `?key1 < ?time'`  by linarith
                    next
                      { fix ta
                        assume "ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        assume "ta \<le> ?time' - 1"
                        assume "?key1 < ta"
                        hence "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ta sig = None"
                          using *[OF `?key1 < ta`] `ta \<le> ?time' - 1` by simp
                        hence "ta \<notin> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          by (simp add: domIff to_trans_raw_sig_def)
                        with `ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)` have False by auto }
                      thus "\<forall>ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). ta \<le> ?time' - 1 \<longrightarrow> ta \<le> ?key1"
                        using not_le_imp_less by blast
                    qed
                    have non_stut: " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) (to_bit b o \<sigma>) sig"
                      using assms(5) non_stuttering_to_trans_raw_bit by force
                    hence "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig  ?key1 sig) \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig"
                    proof -
                      have "?key1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                      moreover have "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> by blast
                      moreover have "\<forall>k. ?key1 < k \<and> k < ?time' \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                        zero_option_def)
                      ultimately show ?thesis    
                        using `?key1 < ?time'` non_stut unfolding non_stuttering_def
                        by (simp add: to_trans_raw_sig_def)
                    qed
                    moreover have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Some (Bv (bs ! b))"
                      by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                    ultimately have neq: "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) \<noteq> Some (Bv (bs ! b))"
                      by auto
                    then obtain valu where "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) = Some valu" and "valu \<noteq> Bv (bs ! b)"
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> by blast
                    have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                          the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?key1)"
                      using inf_some unfolding to_signal_def comp_def
                      by auto
                    also have "... \<noteq> Bv (bs ! b)"
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> neq 
                      by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. t < n \<and> n < the
                      (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))
                      \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None) sig = Some valu\<close> option.sel
                      to_trans_raw_sig_def)
                    finally show "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                      by blast
                  qed
                  ultimately have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) = to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1))"
                    unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def by auto
                  hence *: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b)"
                    using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)\<close> by auto
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                  have "to_bit b (signal_of (\<sigma> sig) \<tau> sig ?time') = (Bv (bs ! b))"
                    using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig) \<tau> b sig", OF `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))`]
                    using to_bit_signal_of'_eq by fastforce
                  hence " ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) = Bv (bs ! b)"
                    unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def 
                    using \<open>t \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) - 1\<close> by auto
                  thus "?time' \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b) \<and>
                                           ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time' = Bv (bs ! b)"    
                    using * `?time' \<le> t + dly` by auto  
                next
                  have "t \<le> ?time' - 1" 
                  proof (rule ccontr)
                    assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                      by auto
                    hence "?time' \<le> t" by auto
                    hence "\<tau> ?time' sig = None"
                      using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig \<noteq> None"
                      using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> 
                      by (metis domIff dom_is_keys to_trans_raw_sig_def)
                    thus "False"
                      using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                  qed
                  fix y
                  assume "y \<le> t + dly \<and>  ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)"
                  hence "y \<le> t + dly" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y) = Bv (bs ! b)"
                    by auto
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                  hence "t < ?time'"
                    by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig) = Bv (bs ! b)\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None\<close> leI option.sel option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                  have "y \<le> t \<or> t < y"
                    by auto
                  moreover
                  { assume "y \<le> t"
                    hence "y < ?time'" using `t < ?time'` by linarith }
                  moreover
                  { assume "t < y"
                    hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) =  to_bit b (signal_of (\<sigma> sig) \<tau> sig (y - 1))"
                      unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                    hence 0: "... \<noteq> (Bv (bs ! b))"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)\<close> by auto
                    have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y =  to_bit b (signal_of (\<sigma> sig) \<tau> sig y)"
                      using `t < y`  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                    hence 1: "... = Bv (bs ! b)"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)\<close> by auto
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                    proof (rule ccontr)
                      assume "\<not> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                      then obtain x' where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None \<or> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                        using domIff by fastforce
                      moreover
                      { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None"
                        hence "signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = 
                               signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (y - 1)"
                          by (intro signal_of_less_sig)(simp add: zero_option_def)
                        with 0 1 have False 
                          by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None\<close> signal_of_less_sig to_bit_signal_of' zero_option_def) }
                      moreover
                      { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                        hence "signal_of ((Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = x'" and "x' \<noteq> (Bv (bs ! b))"
                          using trans_some_signal_of' by fastforce+
                        with 1 have False 
                          unfolding to_bit_signal_of'_eq by auto }
                      ultimately show False
                        by auto
                    qed
                    with `y \<le> t + dly` have "y \<le> ?time'"
                      unfolding time'_eq 
                      apply (intro Greatest_le_nat)
                      unfolding keys_def to_trans_raw_sig_def zero_option_def by auto }
                  ultimately show "y \<le> ?time'"
                    by auto
                qed
                have "?time' \<le> a"
                proof (rule ccontr)
                  have len_map: "length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) \<le> length bs - 0"
                    by auto
                  assume "\<not> ?time' \<le> a" hence "a \<le> ?time'" by auto
                  hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) ?time' sig = None"
                    using Some \<open>\<forall>t\<in>dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig). t \<le> t' \<longrightarrow> t \<le> a\<close>
                    by (metis `?time = ?time'` \<open>?time \<le> t'\<close> \<open>\<not> ?time' \<le> a\<close> domIff to_trans_raw_sig_def)
                  hence "?time' \<notin> fold (\<union>)
                        (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                        (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                    unfolding purge_raw'_def combine_trans_bit_def Let_def
                    using \<open>?time = ?time'\<close> \<open>t < ?time\<close> \<open>?time \<le> t + dly\<close> by auto
                  hence "?time' \<notin> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                    using \<open>b < length bs\<close>  unfolding map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt take_all[OF len_map] member_fold_union2 by auto
                  moreover have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (\<lambda>siga n. to_trans_raw_bit (\<sigma> sig) \<tau> b sig n siga) sig (t + dly))) sig \<noteq> 0"
                    using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> unfolding keys_def to_trans_raw_sig_def by auto
                  ultimately show "False"
                    using h0 h1
                    unfolding to_trans_raw_sig_def keys_def purge_raw_def Let_def by auto
                qed
                have "t < a"
                proof (rule ccontr)
                  assume "\<not> t < a" hence "a \<le> t" by auto
                  hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = None"
                    unfolding purge_raw'_def combine_trans_bit_def Let_def 
                    using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                  with Some show False
                    by (metis (mono_tags, lifting) inf_time_some_exists keys_def mem_Collect_eq to_trans_raw_sig_def zero_option_def)
                qed
                have "a \<le> t + dly"
                  using Some  by (meson \<open>t' < t + dly\<close> inf_time_some_exists le_trans less_imp_le_nat)
                have ainset: "a \<in> fold (\<union>)
                        (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                        (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                proof (rule ccontr)
                  assume "a \<notin> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
                  hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = None"
                    using `t < a` `a \<le> t + dly` unfolding purge_raw'_def combine_trans_bit_def Let_def by auto
                  with Some show False
                    by (metis (mono_tags, lifting) inf_time_some_exists keys_def mem_Collect_eq to_trans_raw_sig_def zero_option_def)
                qed
                have " purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = 
                        combine_trans_bit \<tau>
                          (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                               (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))
                        sign sig t dly a sig"
                  unfolding purge_raw'_def by auto
                also have "... = Some
                         (Lv sign
                           (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig a))
                             (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))" (is "_ = Some (Lv sign ?list)")
                  using ainset `t < a` `a \<le> t + dly` unfolding combine_trans_bit_def by auto
                finally have "to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t') = Bv (?list ! b)"
                  using \<open>signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = the (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig)\<close> by auto
                also have "... = Bv (bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                    (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a))"
                  using `b < length bs`  by (simp add: val.case_eq_if)
                finally have imp: "bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t')) = 
                              bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                      (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a)"
                  by auto
                have "a \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig) \<or>
                      a \<notin> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                  by auto
                moreover
                { assume ainkeys2: "a \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                  hence cond0: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b)"
                    using \<open>t < a\<close> \<open>a \<le> t + dly\<close> unfolding purge_raw_def to_trans_raw_sig_def keys_def Let_def override_on_def 
                    using zero_option_def by auto
                  moreover have cond1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                    using ainkeys2 \<open>t < a\<close> \<open>a \<le> t + dly\<close> unfolding purge_raw_def to_trans_raw_sig_def keys_def Let_def override_on_def 
                    using zero_option_def fun_upd_eqD by fastforce
                  ultimately have somea: "Some a = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)"
                    using ainkeys2 unfolding purge_raw_def
                    by (metis Some \<open>a \<le> t + dly\<close> \<open>t < a\<close> \<open>t' < t + dly\<close> ainkeys2 domIff dom_def inf_time_some_exists keys_def le_antisym not_le purge_raw_neq_0_imp to_trans_raw_sig_def zero_option_def)
                  hence "inf_time (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)))) sig a = Some a"
                    apply (intro inf_time_someI)
                    by(metis ainkeys2 dom_def keys_def zero_option_def)auto
                  hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                      (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a = 
                         the (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a)"
                    unfolding to_signal_def comp_def by auto
                  also have "... = the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig a sig)"
                    using cond0 cond1 somea unfolding to_trans_raw_sig_def purge_raw_def Let_def override_on_def 
                    by (smt UnE \<open>inf_time (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b
                    sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs !
                    b)))) sig a = Some a\<close> greaterThanAtMost_iff greaterThanLessThan_iff
                    inf_time_at_most leD option.sel)
                  also have "... = Bv (bs ! b)"
                    using cond1 somea unfolding to_signal_def comp_def  by (metis option.simps(5) to_trans_raw_sig_def)
                  finally have " bs ! b = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                    using imp by auto }
                moreover
                { assume anotinkeys2: "a \<notin> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                  have "inf_time (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)))) sig a = Some ?time'"
                  proof (rule inf_time_someI)
                    have "\<exists>y. to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (\<lambda>siga n. to_trans_raw_bit (\<sigma> sig) \<tau> b sig n siga) sig (t + dly))) sig = Some y"
                      using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> unfolding keys_def to_trans_raw_sig_def 
                      by (simp add: zero_option_def)
                    thus "?time' \<in> dom (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                      using h0 h1
                      unfolding to_trans_raw_sig_def dom_def purge_raw_def Let_def by auto
                  next
                    show "?time' \<le> a" using \<open>?time' \<le> a\<close> by auto
                  next
                    show "\<forall>ta\<in>dom (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig).
         ta \<le> a \<longrightarrow> ta \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))"
                      using h0 h1 \<open>?time' \<le> a\<close>
                      unfolding purge_raw_def Let_def to_trans_raw_sig_def dom_def  using \<open>a \<le> t + dly\<close> leI by fastforce
                  qed
                  hence "(signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                 (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a) = 
                         the (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig ?time')"
                    using \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)\<close> unfolding to_signal_def comp_def by auto
                  also have "... =  the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (?time') sig)"
                    using h0 h1 unfolding to_trans_raw_sig_def purge_raw_def Let_def by auto
                  also have "... = (Bv (bs ! b))"
                    using \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)\<close> by auto
                  finally have "bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                      (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a) = bs ! b"
                    by auto
                  hence " bs ! b = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                    using imp by auto }
                ultimately show ?thesis 
                  by auto
              qed
              finally have "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                            bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                by auto }
            moreover
            { assume "t' < ?time"
              hence "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = bval_of ( ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t)"
                unfolding * using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig :=
                to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)\<close> by auto
              also have "... = bval_of (to_bit b (snd \<omega> sig t))"
                unfolding fun_upd_def by auto
              also have "... = bval_of (to_bit b (signal_of (\<sigma> sig) \<tau> sig t))"
                unfolding assms(1) worldline_raw_def by auto
              also have "... = bval_of (to_bit b (\<sigma> sig))"
                by (metis (full_types, hide_lams) assms(2) context_invariant_def signal_of_def zero_fun_def)
              finally have "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                            bval_of (to_bit b (\<sigma> sig))"
                by auto
              also have "... = bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              proof (cases "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t'")
                case None
                then show ?thesis 
                  unfolding to_signal_def comp_def by auto
              next
                case (Some a)
                hence "signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = the (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig)"
                  by (simp add: to_signal_def to_trans_raw_sig_def)
                have "\<forall>t\<in>dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig). t \<le> t' \<longrightarrow> t \<le> a"
                  using inf_time_someE[OF Some] by auto
                have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time - 1) \<noteq> Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)"
                  using `((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time = Bv (bs ! b)` `?time \<le> t + dly` `t < ?time`
                  unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  by presburger
                ultimately have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig) ?time sig \<noteq> None"
                  by (metis (no_types, lifting) signal_of_less_sig to_bit_signal_of' zero_option_def)
                have h0: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                have h1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                  using 1 unfolding to_bit_signal_of'_eq assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                  using to_bit_signal_of'_eq by fastforce
                let ?time' = "the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))"
                obtain val where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val" 
                    using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig \<noteq> None\<close> by auto
                have "\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly"
                 by (metis (mono_tags, lifting) \<open>?time \<le> t + dly\<close> \<open>\<And>thesis. (\<And>val.
                    to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> keys_def
                    mem_Collect_eq option.simps(3) to_trans_raw_sig_def zero_option_def)
                hence time'_eq: "?time' = (GREATEST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig) \<and> k \<le> t + dly)"
                  unfolding inf_time_def by auto
                hence "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)" and "?time' \<le> t + dly"
                  using GreatestI_ex_nat 
                  by (metis (mono_tags, lifting) \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly\<close> inf_time_def inf_time_ex1 inf_time_some_exists)+
                have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)"
                proof -
                  have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) = Some ?time'"
                    by (simp add: \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). k \<le> t + dly\<close> inf_time_def)
                  thus "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Bv (bs ! b)"
                    using h1 unfolding to_signal_def comp_def 
                    by (metis option.simps(5) to_trans_raw_sig_def)
                qed
                have "the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time sig) = Bv (bs ! b)"
                proof - 
                  have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?time = Bv (bs ! b)"
                    using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! b)\<close> unfolding to_bit_signal_of'_eq[THEN sym] by auto
                  moreover have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig ?time = Some ?time"
                  proof (intro inf_time_someI)
                    show "?time \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                    proof -
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None"
                      by (metis (full_types) \<open>\<And>thesis. (\<And>val. to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> option.simps(3))
                    then show ?thesis
                        by (simp add: domIff to_trans_raw_sig_def)
                    qed
                  qed (auto)
                  ultimately show ?thesis
                    unfolding to_signal_def comp_def  by (simp add: to_trans_raw_sig_def)
                qed
                have "?time = ?time'"
                proof (rule Greatest_equality)
                  have "t \<le> ?time' - 1" 
                  proof (rule ccontr)
                    assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                      by auto
                    hence "?time' \<le> t" by auto
                    hence "\<tau> ?time' sig = None"
                      using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig \<noteq> None"
                      using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> 
                      by (metis domIff dom_is_keys to_trans_raw_sig_def)
                    thus "False"
                      using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                  qed
                  moreover have "to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)"
                    unfolding to_bit_signal_of'_eq[THEN sym]
                  proof (cases "\<exists>n. t < n \<and> n < ?time' \<and> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig \<noteq> None")
                    case False
                    hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time' - 1 \<Longrightarrow> (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) n sig = 0"
                      by (auto simp add: zero_option_def)
                    have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                            signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t"
                      using signal_of_less_ind'[of "t" "?time' - 1" "to_trans_raw_bit (\<sigma> sig) \<tau> b sig" "sig", OF none] `t \<le> ?time' - 1`
                      by auto                    
                    also have "... \<noteq> (Bv (bs ! b))"
                      using h0 to_bit_signal_of'_eq by force
                    finally show " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                      by auto
                  next
                    case True
                    let ?key1 = "(GREATEST n. t < n \<and> n < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)"
                    from True have "t < ?key1" and "?key1 < ?time'" and " to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None"
                      using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
                    have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time' \<Longrightarrow> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig = None"
                      using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig x sig \<noteq> None" and b="?time'"]
                      by (smt \<open>t < (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
                    have inf_some: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (?time' - 1) = Some ?key1"
                    proof (rule inf_time_someI)
                      show "?key1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
                    next
                      show "?key1 \<le> ?time' - 1"
                        using `?key1 < ?time'`  by linarith
                    next
                      { fix ta
                        assume "ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        assume "ta \<le> ?time' - 1"
                        assume "?key1 < ta"
                        hence "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ta sig = None"
                          using *[OF `?key1 < ta`] `ta \<le> ?time' - 1` by simp
                        hence "ta \<notin> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                          by (simp add: domIff to_trans_raw_sig_def)
                        with `ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)` have False by auto }
                      thus "\<forall>ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig). ta \<le> ?time' - 1 \<longrightarrow> ta \<le> ?key1"
                        using not_le_imp_less by blast
                    qed
                    have non_stut: " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) (to_bit b o \<sigma>) sig"
                      using assms(5) non_stuttering_to_trans_raw_bit by force
                    hence "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig  ?key1 sig) \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig"
                    proof -
                      have "?key1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                      moreover have "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> by blast
                      moreover have "\<forall>k. ?key1 < k \<and> k < ?time' \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)"
                        using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                        zero_option_def)
                      ultimately show ?thesis    
                        using `?key1 < ?time'` non_stut unfolding non_stuttering_def
                        by (simp add: to_trans_raw_sig_def)
                    qed
                    moreover have "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig) = Some (Bv (bs ! b))"
                      by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                    ultimately have neq: "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) \<noteq> Some (Bv (bs ! b))"
                      by auto
                    then obtain valu where "(to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig) = Some valu" and "valu \<noteq> Bv (bs ! b)"
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> by blast
                    have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) = 
                          the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig ?key1)"
                      using inf_some unfolding to_signal_def comp_def
                      by auto
                    also have "... \<noteq> Bv (bs ! b)"
                      using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?key1 sig \<noteq> None\<close> neq 
                      by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> b sig n sig \<noteq> None) sig = Some valu\<close> option.sel to_trans_raw_sig_def)
                    finally show "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (?time' - 1) \<noteq> (Bv (bs ! b))"
                      by blast
                  qed
                  ultimately have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) = to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1))"
                    unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def by auto
                  hence *: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b)"
                    using \<open>to_bit b (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! b)\<close> by auto
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                  have "to_bit b (signal_of (\<sigma> sig) \<tau> sig ?time') = (Bv (bs ! b))"
                    using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig) \<tau> b sig", OF `to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))`]
                    using to_bit_signal_of'_eq by fastforce
                  hence " ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) = Bv (bs ! b)"
                    unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def 
                    using \<open>t \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) - 1\<close> by auto
                  thus "?time' \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time' = Bv (bs ! b)"    
                    using * `?time' \<le> t + dly` by auto  
                next
                  have "t \<le> ?time' - 1" 
                  proof (rule ccontr)
                    assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                      by auto
                    hence "?time' \<le> t" by auto
                    hence "\<tau> ?time' sig = None"
                      using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig \<noteq> None"
                      using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> 
                      by (metis domIff dom_is_keys to_trans_raw_sig_def)
                    thus "False"
                      using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                  qed
                  fix y
                  assume "y \<le> t + dly \<and>  ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)"
                  hence "y \<le> t + dly" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)" and "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y) = Bv (bs ! b)"
                    by auto
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig ?time' sig = Some (Bv (bs ! b))"
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))) sig) = Bv (bs ! b)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                  hence "t < ?time'"
                    by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig) = Bv (bs ! b)\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig = Some val\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) sig \<noteq> None\<close> leI option.sel option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                  have "y \<le> t \<or> t < y"
                    by auto
                  moreover
                  { assume "y \<le> t"
                    hence "y < ?time'" using `t < ?time'` by linarith }
                  moreover
                  { assume "t < y"
                    hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) =  to_bit b (signal_of (\<sigma> sig) \<tau> sig (y - 1))"
                      unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                    hence 0: "... \<noteq> (Bv (bs ! b))"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! b)\<close> by auto
                    have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y =  to_bit b (signal_of (\<sigma> sig) \<tau> sig y)"
                      using `t < y`  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                    hence 1: "... = Bv (bs ! b)"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig y = Bv (bs ! b)\<close> by auto
                    have "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                    proof (rule ccontr)
                      assume "\<not> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some (Bv (bs ! b))"
                      then obtain x' where "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None \<or> to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                        using domIff by fastforce
                      moreover
                      { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None"
                        hence "signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = 
                               signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (y - 1)"
                          by (intro signal_of_less_sig)(simp add: zero_option_def)
                        with 0 1 have False 
                          by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = None\<close> signal_of_less_sig to_bit_signal_of' zero_option_def) }
                      moreover
                      { assume "to_trans_raw_bit (\<sigma> sig) \<tau> b sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! b))"
                        hence "signal_of ((Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig y = x'" and "x' \<noteq> (Bv (bs ! b))"
                          using trans_some_signal_of' by fastforce+
                        with 1 have False 
                          unfolding to_bit_signal_of'_eq by auto }
                      ultimately show False
                        by auto
                    qed
                    with `y \<le> t + dly` have "y \<le> ?time'"
                      unfolding time'_eq 
                      apply (intro Greatest_le_nat)
                      unfolding keys_def to_trans_raw_sig_def zero_option_def by auto }
                  ultimately show "y \<le> ?time'"
                    by auto
                qed
                have "a < ?time'"
                  using Some \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n
                  - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) =
                  the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))\<close>
                  \<open>t' < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1)
                  \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close>
                  inf_time_some_exists by fastforce
                have "t < a"
                proof (rule ccontr)
                  assume "\<not> t < a" hence "a \<le> t" by auto
                  hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = None"
                    unfolding purge_raw'_def combine_trans_bit_def Let_def 
                    using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                  with Some show False
                    by (metis (mono_tags, lifting) inf_time_some_exists keys_def mem_Collect_eq to_trans_raw_sig_def zero_option_def)
                qed
                have "a \<le> t + dly"
                  using Some  by (meson \<open>t' < t + dly\<close> inf_time_some_exists le_trans less_imp_le_nat)
                have ainset: "a \<in> fold (\<union>)
                        (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                        (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                             (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                proof (rule ccontr)
                  assume "a \<notin> fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
              (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
                  hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = None"
                    using `t < a` `a \<le> t + dly` unfolding purge_raw'_def combine_trans_bit_def Let_def by auto
                  with Some show False
                    by (metis (mono_tags, lifting) inf_time_some_exists keys_def mem_Collect_eq to_trans_raw_sig_def zero_option_def)
                qed
                have " purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = 
                        combine_trans_bit \<tau>
                          (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                               (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))
                        sign sig t dly a sig"
                  unfolding purge_raw'_def by auto
                also have "... = Some
                         (Lv sign
                           (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig a))
                             (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))))" (is "_ = Some (Lv sign ?list)")
                  using ainset `t < a` `a \<le> t + dly` unfolding combine_trans_bit_def by auto
                finally have "to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t') = Bv (?list ! b)"
                  using \<open>signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = the (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig)\<close> by auto
                also have "... = Bv (bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                    (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a))"
                  using `b < length bs`  by (simp add: val.case_eq_if)
                finally have imp: "bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t')) = 
                              bval_of (signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) 
                                      (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a)"
                  by auto
                have "inf_time (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)))) sig a = None"
                proof (unfold inf_time_none_iff[THEN sym], rule)
                  fix x
                  assume "x \<in> dom (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig)"
                  thus "a < x"
                    using h0 h1 `a < ?time'` assms(2) 
                    unfolding context_invariant_def dom_def to_trans_raw_sig_def purge_raw_def Let_def 
                    by (smt Un_iff fun_upd_eqD fun_upd_triv greaterThanLessThan_iff leI le_less_trans mem_Collect_eq option.case_eq_if override_on_apply_in override_on_apply_notin to_trans_raw_bit_def zero_fun_def zero_option_def)
                qed
                hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) sig a = 
                      (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))" 
                  unfolding to_signal_def comp_def by auto
                moreover have "to_bit b (\<sigma> sig) = (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! b))"
                  by (auto split: val.splits)
                ultimately show ?thesis
                  unfolding imp by auto 
              qed
              finally have "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                            bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
                by auto }
            ultimately have "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                            bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              by auto }
          ultimately show "bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t') = 
                            bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
            by auto 
        qed
        have "?zeit \<le> t' \<or> t' < ?zeit"
          by auto
        moreover
        { assume "?zeit \<le> t'"
          have "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = 
                Lv sign (map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs])"
            unfolding worldline_inert_upd2.simps snd_conv `s' = sig` fun_upd_def using \<open>t \<le> t'\<close> \<open>?zeit \<le> t'\<close> thereis by auto
          hence midway: "\<And>b. b < length bs \<Longrightarrow> lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t') ! b = 
                                       bval_of (snd (to_worldline_init_bit \<omega> sig b)[sig, t, dly := Bv (bs ! b)] sig t')"
            by auto
          hence midway2: "\<And>b. b < length bs \<Longrightarrow> lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t') ! b = 
                          bval_of (to_bit b (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
             using \<open>\<And>ba. ba < length bs \<Longrightarrow> bval_of (snd to_worldline_init_bit \<omega> sig ba[sig, t, dly :=
             Bv (bs ! ba)] sig t') = bval_of (to_bit ba (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig
             (\<sigma> sig) (Lv sign bs)) sig t'))\<close> by blast
          have "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' \<noteq> None"
            unfolding inf_time_none_iff[THEN sym]
          proof (rule)
            assume "Ball (dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)) ((<) t')"
            hence "\<forall>x\<in>dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig). t' < x"
              by auto
            have helper: "length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))
                         (Bv (bs ! n)))
                [0..<length bs]) \<le> length bs - 0"
              by auto
            have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index) \<or> 
                  ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
              by auto
            moreover
            { assume "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index)"
              hence "zeit = t + dly"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index) \<Longrightarrow> zeit = t + dly\<close> by blast
              hence "?zeit = t + dly"
                unfolding zeit_def by auto
              with \<open>t' < t + dly\<close> \<open>?zeit \<le> t'\<close> have "False"
                by linarith }
            moreover
            { assume "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)"
              hence zeit_def': "zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by blast
              have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig t \<noteq> Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t) \<noteq> Bv (bs ! index)\<close>
                unfolding assms(1) worldline_raw_def snd_conv fun_upd_def to_bit_signal_of'_eq by auto
              moreover have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close>
                unfolding assms(1) worldline_raw_def snd_conv fun_upd_def to_bit_signal_of'_eq by auto
              let ?time' = " the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))"
              let ?time = "(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))"
              have "?time \<le> t + dly"
                using \<open>(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) \<le> t'\<close> \<open>t' < t + dly\<close> \<open>zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> zeit_def by linarith
              have "t < ?time"
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> zeit_def by linarith
              have "to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time - 1)) \<noteq> Bv (bs ! index)"
                using `?w' index sig (zeit - 1) \<noteq> Bv (bs ! index)`  unfolding \<open>?w' index sig (zeit - 1) = ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig t\<close>
                using `?time \<le> t + dly` `t < ?time` zeit_def zeit_def' unfolding assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                by (smt \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index) \<Longrightarrow> False\<close> \<open>\<not> zeit - 1 < t\<close> assms(1) fun_upd_same o_apply prod.sel(2) worldline_raw_def) 
              moreover have "to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! index)"
                using  `?time \<le> t + dly` `t < ?time`
                assms(1) comp_def fun_upd_def worldline_raw_def snd_conv 
                by (smt \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> leD less_or_eq_imp_le)
              ultimately have "(to_trans_raw_bit (\<sigma> sig) \<tau> index sig) ?time sig \<noteq> None"
                by (metis (no_types, lifting) signal_of_less_sig to_bit_signal_of' zero_option_def)
              obtain val where "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time sig = Some val" 
                  using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time sig \<noteq> None\<close> by auto
              have "\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig). k \<le> t + dly"
              proof -
                have "to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) = Some val"
                  by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig = Some val\<close> to_trans_raw_sig_def)
                then have "\<exists>n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig n \<noteq> None \<and> n \<le> t + dly"
                  using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) \<le> t + dly\<close> by blast
                then show ?thesis
                  by (simp add: keys_def zero_option_def)
              qed
              hence time'_eq: "?time' = (GREATEST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig) \<and> k \<le> t + dly)"
                unfolding inf_time_def by auto
              hence "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)" and "?time' \<le> t + dly"
                using GreatestI_ex_nat 
                by (metis (mono_tags, lifting) \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig). k \<le> t + dly\<close> inf_time_def inf_time_ex1 inf_time_some_exists)+
              have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time sig"
              proof (rule ccontr)
                assume "\<not> to_trans_raw_bit (\<sigma> sig)  \<tau> index sig ?time' sig = to_trans_raw_bit (\<sigma> sig)  \<tau> index sig ?time sig"
                hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time =  val"
                  using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> index sig" "?time" "sig" "(\<lambda>x. _)(sig := val)"]
                  using \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig :=
                  to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ>
                  snd \<omega> sig)) sig n = Bv (bs ! index)) sig = Some val\<close> by auto
                then obtain val' where "to_trans_raw_bit (\<sigma> sig)  \<tau> index sig ?time' sig = Some val'"
                proof -
                  assume "\<And>val'. to_trans_raw_bit (\<sigma> sig)  \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly))) sig = Some val' \<Longrightarrow> thesis"
                  then show ?thesis
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig)\<close> domIff dom_def keys_def not_None_eq to_trans_raw_sig_def zero_option_def)
                qed
                hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time' =  val'"
                  using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> index sig" "?time" "sig" "(\<lambda>x. _)(sig := val')"] time'_eq
                  by (meson trans_some_signal_of')
                also have "... \<noteq> val"
                  using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd
                  \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig
                  := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig = Some val\<close>
                  \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig
                  (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig = Some val'\<close>
                  using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig\<close> by auto
                finally have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time' \<noteq> 
                              signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time "
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index))
                  (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig
                  := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig :=
                  to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) = val\<close> by blast
                have "t < ?time'"
                  by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig = Some val'\<close> leI option.simps(3) option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time') = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time'"
                  using `t < ?time'` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                moreover have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time"
                  using `t < ?time` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                ultimately have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time') \<noteq> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time)"
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) \<noteq> signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by auto                  
                have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time' = val'"
                  using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> index sig" "?time'" "sig" "(\<lambda>x. _)(sig := val')"] \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> index sig ?time' sig = Some val'\<close>
                  by auto
                have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly))) = 
                      inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly)"
                  using time'_eq 
                proof -
                  obtain nn :: nat where
                    f1: "nn \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig) \<and> nn \<le> t + dly"
                      using \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig). k \<le> t + dly\<close> by blast
                  have f2: "to_signal (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv s bs \<Rightarrow> bs ! index)) (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly) = Bv (bs ! index)"
                    using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)\<close> by auto
                  have f3: "\<forall>v n a f. to_signal v f (a::'a) n = the (f a (the (inf_time f a n))) \<or> inf_time f a n = None"
                    by (simp add: option.case_eq_if to_signal_def)
                  have f4: "\<forall>f. f (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly)))) = f (Some val')"
                    by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig = Some val'\<close> to_trans_raw_sig_def)
                  have "Bv (bs ! index) \<noteq> val'"
                    using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) = val\<close> \<open>val' \<noteq> val\<close> by auto
                  then have f5: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly) = None"
                    using f4 f3 f2 option.sel 
                    by (metis \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig (t + dly))) sig = Some val'\<close> to_trans_raw_sig_def)
                  have "\<forall>n. Some (GREATEST na. na \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig) \<and> na \<le> n) = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig)) sig n \<or> \<not> nn \<le> n"
                  using f1 by (simp add: inf_time_def)
                    then show ?thesis
                  using f5 f1 by force
                qed
                hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig (t + dly) = 
                      signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time'"
                  unfolding to_signal_def comp_def by auto
                hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig)  \<tau> index sig) sig ?time' = Bv (bs ! index)"
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)\<close> by auto
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time) = Bv (bs ! index)"
                  using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (zeit - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig zeit = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index)\<close> by blast
                have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time') = Bv (bs ! index)"
                  using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)))\<close> \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) = Bv (bs ! index)\<close> by auto
                show False
                  using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) = Bv (bs ! index)\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) \<noteq> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> by auto
              qed
              have h1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)"
                using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)\<close> by blast
              have "the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig) = Bv (bs ! index)"
              proof -
                have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly) = Some ?time'"
                  by (simp add: \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig). k \<le> t + dly\<close> inf_time_def)
                thus "the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig) = Bv (bs ! index)"
                  using h1 unfolding to_signal_def comp_def  by (metis option.simps(5) to_trans_raw_sig_def)
              qed
              have "the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time sig) = Bv (bs ! index)"
              proof- 
                have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig ?time = Bv (bs ! index)"
                  using \<open>to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time)) = Bv (bs ! index)\<close>
                  unfolding to_bit_signal_of'_eq[THEN sym] by auto
                moreover have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig ?time = Some ?time"
                proof (intro inf_time_someI)
                  show "?time \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                  proof -
                    have "\<exists>v. to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig = Some v"
                      by (metis \<open>\<And>thesis. (\<And>val. to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
                    then show ?thesis
                      by (simp add: domIff to_trans_raw_sig_def)
                  qed
                qed (auto)
                ultimately show ?thesis
                  unfolding to_signal_def comp_def 
                  by (simp add: to_trans_raw_sig_def)
              qed
              have "?time = ?time'"
              proof (rule Greatest_equality)
                have "t \<le> ?time' - 1" 
                proof (rule ccontr)
                  assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                    by auto
                  hence "?time' \<le> t" by auto
                  hence "\<tau> ?time' sig = None"
                    using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig \<noteq> None"
                    using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)\<close> 
                    by (metis domIff dom_is_keys to_trans_raw_sig_def)
                  thus "False"
                    using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                qed
                moreover have "to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! index)"
                  unfolding to_bit_signal_of'_eq[THEN sym]
                proof (cases "\<exists>n. t < n \<and> n < ?time' \<and> (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) n sig \<noteq> None")
                  case False
                  hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time' - 1 \<Longrightarrow> (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) n sig = 0"
                    by (auto simp add: zero_option_def)
                  have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (?time' - 1) = 
                          signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig t"
                    using signal_of_less_ind'[of "t" "?time' - 1" "to_trans_raw_bit (\<sigma> sig) \<tau> index sig" "sig", OF none] `t \<le> ?time' - 1`
                    by auto                    
                  also have "... \<noteq> (Bv (bs ! index))"
                    using to_bit_signal_of'_eq 
                    using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig t \<noteq> Bv (bs ! index)\<close> by blast
                  finally show " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (?time' - 1) \<noteq> (Bv (bs ! index))"
                    by auto
                next
                  case True
                  let ?key1 = "(GREATEST n. t < n \<and> n < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> index sig n sig \<noteq> None)"
                  from True have "t < ?key1" and "?key1 < ?time'" and " to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig \<noteq> None"
                    using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
                  have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time' \<Longrightarrow> to_trans_raw_bit (\<sigma> sig) \<tau> index sig n sig = None"
                    using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> index sig x sig \<noteq> None" and b="?time'"]
                    by (smt \<open>t < (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> index sig n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
                  have inf_some: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (?time' - 1) = Some ?key1"
                  proof (rule inf_time_someI)
                    show "?key1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                      using `to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
                  next
                    show "?key1 \<le> ?time' - 1"
                      using `?key1 < ?time'`  by linarith
                  next
                    { fix ta
                      assume "ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                      assume "ta \<le> ?time' - 1"
                      assume "?key1 < ta"
                      hence "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ta sig = None"
                        using *[OF `?key1 < ta`] `ta \<le> ?time' - 1` by simp
                      hence "ta \<notin> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                        by (simp add: domIff to_trans_raw_sig_def)
                      with `ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)` have False by auto }
                    thus "\<forall>ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig). ta \<le> ?time' - 1 \<longrightarrow> ta \<le> ?key1"
                      using not_le_imp_less by blast
                  qed
                  have non_stut: " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) (to_bit index o \<sigma>) sig"
                    using assms(5) non_stuttering_to_trans_raw_bit by force
                  hence "(to_trans_raw_bit (\<sigma> sig) \<tau> index sig  ?key1 sig) \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig"
                  proof -
                    have "?key1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                      using `to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                    moreover have "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                      using \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)\<close> by blast
                    moreover have "\<forall>k. ?key1 < k \<and> k < ?time' \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)"
                      using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                      zero_option_def)
                    ultimately show ?thesis    
                      using `?key1 < ?time'` non_stut unfolding non_stuttering_def
                      by (simp add: to_trans_raw_sig_def)
                  qed
                  moreover have "(to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig) = Some (Bv (bs ! index))"
                    by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index
                    sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau>
                    index sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig
                    (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig) = Bv (bs ! index)\<close>
                    domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                  ultimately have neq: "(to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig) \<noteq> Some (Bv (bs ! index))"
                    by auto
                  then obtain valu where "(to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig) = Some valu" and "valu \<noteq> Bv (bs ! index)"
                    using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig \<noteq> None\<close> by blast
                  have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (?time' - 1) = 
                        the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig ?key1)"
                    using inf_some unfolding to_signal_def comp_def
                    by auto
                  also have "... \<noteq> Bv (bs ! index)"
                    using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?key1 sig \<noteq> None\<close> neq 
                    by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> index sig n sig \<noteq> None) sig = Some valu\<close> option.sel to_trans_raw_sig_def)
                  finally show "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (?time' - 1) \<noteq> (Bv (bs ! index))"
                    by blast
                qed
                ultimately have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time' - 1) = to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time' - 1))"
                  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def by auto
                hence *: "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! index)"
                  using \<open>to_bit index (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! index)\<close> by auto
                have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig = Some (Bv (bs ! index))"
                  using \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig
                  (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig) = Bv (bs ! index)\<close>
                  \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig :=
                  to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit
                  index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig \<noteq> None\<close> \<open>to_trans_raw_bit (\<sigma> sig)
                  \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index
                  sig)) sig (t + dly))) sig = to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le>
                  t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index)
                  \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig\<close> by
                  force
                have "to_bit index (signal_of (\<sigma> sig) \<tau> sig ?time') = (Bv (bs ! index))"
                  using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig) \<tau> index sig", OF `to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig = Some (Bv (bs ! index))`]
                  using to_bit_signal_of'_eq by fastforce
                hence " ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) = Bv (bs ! index)"
                  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def 
                  using \<open>t \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)) - 1\<close> by auto
                thus "?time' \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig ?time' = Bv (bs ! index)"    
                  using * `?time' \<le> t + dly` by auto  
              next
                have "t \<le> ?time' - 1" 
                proof (rule ccontr)
                  assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                    by auto
                  hence "?time' \<le> t" by auto
                  hence "\<tau> ?time' sig = None"
                    using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig \<noteq> None"
                    using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)\<close> 
                    by (metis domIff dom_is_keys to_trans_raw_sig_def)
                  thus "False"
                    using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                qed
                fix y
                assume "y \<le> t + dly \<and>  ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig y = Bv (bs ! index)"
                hence "y \<le> t + dly" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! index)" and "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (y) = Bv (bs ! index)"
                  by auto
                have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig = Some (Bv (bs ! index))"
                  by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig) = Bv (bs ! index)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                hence "t < ?time'"
                  by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig \<noteq> None\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig = to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig\<close> leI option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                have "y \<le> t \<or> t < y"
                  by auto
                moreover
                { assume "y \<le> t"
                  hence "y < ?time'" using `t < ?time'` by linarith }
                moreover
                { assume "t < y"
                  hence "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (y - 1) =  to_bit index (signal_of (\<sigma> sig) \<tau> sig (y - 1))"
                    unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                  hence 0: "... \<noteq> (Bv (bs ! index))"
                    using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! index)\<close> by auto
                  have "((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig y =  to_bit index (signal_of (\<sigma> sig) \<tau> sig y)"
                    using `t < y`  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                  hence 1: "... = Bv (bs ! index)"
                    using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig y = Bv (bs ! index)\<close> by auto
                  have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = Some (Bv (bs ! index))"
                  proof (rule ccontr)
                    assume "\<not> to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = Some (Bv (bs ! index))"
                    then obtain x' where "to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = None \<or> to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! index))"
                      using domIff by fastforce
                    moreover
                    { assume "to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = None"
                      hence "signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig y = 
                             signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (y - 1)"
                        by (intro signal_of_less_sig)(simp add: zero_option_def)
                      with 0 1 have False 
                        by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = None\<close> signal_of_less_sig to_bit_signal_of' zero_option_def) }
                    moreover
                    { assume "to_trans_raw_bit (\<sigma> sig) \<tau> index sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! index))"
                      hence "signal_of ((Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! index))) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig y = x'" and "x' \<noteq> (Bv (bs ! index))"
                        using trans_some_signal_of' by fastforce+
                      with 1 have False 
                        unfolding to_bit_signal_of'_eq by auto }
                    ultimately show False
                      by auto
                  qed
                  with `y \<le> t + dly` have "y \<le> ?time'"
                    unfolding time'_eq 
                    apply (intro Greatest_le_nat)
                    unfolding keys_def to_trans_raw_sig_def zero_option_def by auto }
                ultimately show "y \<le> ?time'"
                  by auto  
              qed
              have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (Bv (bs ! index)) zeit sig \<noteq> 0"
              proof -
                have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig t \<noteq> Bv (bs ! index)"
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig t \<noteq> Bv (bs ! index)\<close> by blast
                moreover have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! index)) (to_trans_raw_bit (\<sigma> sig) \<tau> index sig) sig (t + dly) = Bv (bs ! index)"
                  using h1 by blast
                moreover have "to_trans_raw_bit (\<sigma> sig) \<tau> index sig ?time' sig \<noteq> None"
                  using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd
                  \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig
                  := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index)) sig \<noteq> None\<close>
                  \<open>to_trans_raw_bit (\<sigma> sig) \<tau> index sig (the (inf_time (to_trans_raw_sig
                  (to_trans_raw_bit (\<sigma> sig) \<tau> index sig)) sig (t + dly))) sig = to_trans_raw_bit (\<sigma>
                  sig) \<tau> index sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega>
                  sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig))
                  sig n = Bv (bs ! index)) sig\<close> by auto
                ultimately show ?thesis
                  using \<open>?time = ?time'\<close> unfolding purge_raw_def Let_def 
                  by (smt UnE \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs !
                  index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega>
                  sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig))
                  sig n = Bv (bs ! index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t +
                  dly) \<noteq> Bv (bs ! index) \<Longrightarrow> False\<close> greaterThanAtMost_iff greaterThanLessThan_iff
                  order_less_irrefl override_on_apply_notin zero_option_def)
              qed
              hence "\<exists>x\<in>{0..<length bs}. zeit \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> x sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) sig)"
                apply (intro bexI[where x="index"])
                unfolding to_trans_raw_sig_def keys_def apply blast
                using \<open>index \<in> set [0..<length bs]\<close> set_upt by blast
              hence "zeit \<in> fold (\<union>) (map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                unfolding member_fold_union2 by auto
              hence "zeit \<in> fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}" 
                unfolding map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt take_all[OF helper] by auto
              hence "combine_trans_bit \<tau> (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) sign sig t dly zeit sig \<noteq> None"
                unfolding combine_trans_bit_def 
                using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow>
                zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n
                - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs !
                index))\<close> \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) \<noteq> Bv (bs ! index)
                \<Longrightarrow> False\<close> \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig
                (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv
                (bs ! index)) \<le> t + dly\<close> \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length
                bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd
                to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> zeit_def by
                fastforce
              hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) zeit sig \<noteq> None"
                unfolding purge_raw'_def by auto
              hence False
                by (metis (full_types) \<open>(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) \<le> t'\<close> \<open>\<forall>x\<in>dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig). t' < x\<close> domIff not_le to_trans_raw_sig_def zeit_def) }
            ultimately show False
              by auto
          qed
          have "(\<exists>list. signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = Lv sign list \<and> length list = length bs)"
          proof (cases "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t'")
            case None         
            then show ?thesis 
              using \<open>inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' \<noteq> None\<close> by auto
          next
            case (Some a)
            hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None"
              by (metis domIff dom_def inf_time_some_exists keys_def to_trans_raw_sig_def zero_option_def)
            have "a \<le> t + dly"
              by (meson Some \<open>t' < t + dly\<close> inf_time_at_most le_less_trans less_imp_le_nat)
            have "t < a"
              using assms(2) \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> 
              unfolding context_invariant_def purge_raw'_def 
              by (metis \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> leI purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
            then obtain list where "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = Some (Lv sign list) \<and> length list = length bs"
              using \<open>a \<le> t + dly\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> unfolding purge_raw'_def 
              combine_trans_bit_def   by (smt leD length_map length_zip map_nth min.idem val.simps(6))
            then show ?thesis 
              using Some unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
          qed
          then obtain list where "(signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = Lv sign list \<and> length list = length bs)"
            by auto
          have " 
                lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t') = 
                lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t')"  
          proof (intro nth_equalityI)
            have "length (lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t')) = length bs"
              using \<open>snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = Lv sign (map (\<lambda>b.
              bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t'))
              [0..<length bs])\<close> by auto                              
            also have "... = length (lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
            proof (cases "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t'")
              case None
              hence "signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = (\<sigma> sig)"
                unfolding to_signal_def comp_def by auto
              then show ?thesis 
                using None \<open>inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' \<noteq> None\<close> by blast
            next
              case (Some a)
              hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None"
                by (metis domIff dom_def inf_time_some_exists keys_def to_trans_raw_sig_def zero_option_def)
              have "a \<le> t + dly"
                by (meson Some \<open>t' < t + dly\<close> inf_time_at_most le_less_trans less_imp_le_nat)
              have "t < a"
                using assms(2) \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> 
                unfolding context_invariant_def purge_raw'_def 
                by (metis \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> leI purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
              then obtain list where "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig = Some (Lv sign list) \<and> length list = length bs"
                using \<open>a \<le> t + dly\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) a sig \<noteq> None\<close> unfolding purge_raw'_def 
                combine_trans_bit_def   by (smt leD length_map length_zip map_nth min.idem val.simps(6))
              then show ?thesis 
                using Some  by (simp add: to_signal_def to_trans_raw_sig_def)
            qed
            finally show "length (lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t')) = length (lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              by auto
          next
            fix i
            assume " i < length (lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t'))"
            hence "i < length bs"
              using \<open>snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = Lv sign (map (\<lambda>b.
              bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t'))
              [0..<length bs])\<close> by auto                 
            have "lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t') ! i = list ! i"
              using \<open>inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' \<noteq> None\<close> \<open>signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = Lv sign list \<and> length list = length bs \<close> by auto
            also have "... = bval_of (to_bit i (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              using \<open>i < length bs\<close> 
              using \<open>inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' \<noteq> None\<close> \<open>signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = Lv sign list \<and> length list = length bs \<close> by auto
            finally have "lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t') ! i = 
                          bval_of (to_bit i (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'))"
              by auto
            thus "lval_of (snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t') ! i = lval_of (signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t') ! i"
              using midway2 \<open>i < length bs\<close>  by blast
          qed
          hence " snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
            using \<open>signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = Lv sign list \<and> length list = length bs\<close> \<open>snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = Lv sign (map (\<lambda>b. bval_of (snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig t')) [0..<length bs])\<close> 
            by auto }
        moreover
        { assume "t' < ?zeit"
          hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' =  snd \<omega> sig t"
            unfolding worldline_inert_upd2.simps snd_conv \<open>s' = sig\<close> Let_def fun_upd_def
            using thereis  by (simp add: \<open>t \<le> t'\<close> leD)
          also have "... = signal_of (\<sigma> sig) \<tau> sig t"
            unfolding assms(1) worldline_raw_def snd_conv by auto
          also have "... = \<sigma> sig"
            by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> signal_of_def zero_fun_def)
          finally have "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = \<sigma> sig"
            by auto
          have "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' = None"
            unfolding inf_time_none_iff[THEN sym]
          proof 
            { fix x 
              assume "x \<le> t'"
              assume "x \<in> dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)"
              hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None"
                unfolding to_trans_raw_sig_def dom_def  by auto
              hence comb: "combine_trans_bit \<tau>
                      (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                           (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))
                      sign sig t dly x sig \<noteq> None"
                unfolding purge_raw'_def by auto
              have help_len: "length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) \<le> length bs - 0"
                by auto
              have "\<forall>xa\<in>{0..<length bs}. x \<notin> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa))) sig)"
                unfolding keys_def to_trans_raw_sig_def
              proof 
                fix xa
                assume "xa \<in> {0..<length bs}"
                have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t = Bv (bs ! xa) \<or> 
                      signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) \<noteq> Bv (bs ! xa) \<or> 
                      signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> 
                      signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)"
                  by auto
                moreover
                { assume "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t = Bv (bs ! xa) \<or> 
                      signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) \<noteq> Bv (bs ! xa)"
                  hence "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa)) x sig = 0"
                    unfolding purge_raw_def Let_def zero_option_def 
                    apply (cases "x \<le> t")
                    apply (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None\<close> purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
                    using \<open>t' < t + dly\<close> \<open>x \<le> t'\<close> by auto }
                moreover
                { assume "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> 
                          signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)"
                  hence "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa)) x sig = 
                         override_on (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) (\<lambda>n. (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig n)(sig := None))
                           ({t<..<the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))} 
                          \<union> {the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))<..t + dly}) x sig"
                    unfolding purge_raw_def Let_def zero_option_def by auto
                  also have "... = None"
                  proof (cases "x \<le> t")
                    case True
                    thus ?thesis
                      by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None\<close> purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
                  next
                    case False
                    have "x < ?zeit"
                      using \<open>t' < ?zeit\<close> \<open>x \<le> t'\<close> dual_order.strict_trans2 by blast
                    also have "... \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))"
                    proof -
                      have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! xa)" and "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! xa)"
                        using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> 
                          signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)\<close>
                        unfolding assms(1) worldline_raw_def snd_conv fun_upd_def to_bit_signal_of'_eq by auto
                      have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)"
                      proof (rule ccontr)
                        assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))"
                        hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<Longrightarrow> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! xa)"
                          by auto
                        { fix n 
                          assume "t \<le> n" and "n \<le> t + dly"
                          hence "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! xa)"
                            using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! xa)\<close> imp
                          proof (induction "n - t" arbitrary: t dly)
                            case 0 hence "n = t" by auto
                            then show ?case 
                              using 0 by auto
                          next
                            case (Suc x)
                            hence 0: "x = n - Suc t"
                              by auto
                            have 2: "n \<le> Suc t + (dly - 1) "
                              using Suc by auto
                            hence 1: "Suc t \<le> n "
                              using Suc by linarith
                            hence "Suc t \<le> t + dly"
                              using Suc by linarith
                            hence 3: "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! xa)"
                              using Suc(5-6) by auto
                            have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<Longrightarrow> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! xa)"
                              using Suc(6) by auto
                            have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! xa)"
                              using  Suc(1)[OF 0 1 2 3 4] by auto
                            thus ?case
                              by auto
                          qed }
                        hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! xa)"
                          by auto
                        thus False
                          using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! xa)\<close> le_add1 by blast
                      qed
                      let ?time_again ="GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)"    
                      have "t < ?time_again"
                        using * 
                      proof -
                        have f1: "\<forall>p n na. (n::nat) \<le> Greatest p \<or> (\<exists>n. \<not> n \<le> na \<and> p n) \<or> \<not> p n"
                          by (metis (lifting) Greatest_le_nat)
                        obtain nn :: nat where
                          f2: "Bv (bs ! xa) = ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig nn \<and> Bv (bs ! xa) \<noteq> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (nn - 1) \<and> nn \<le> t + dly \<and> t < nn"
                          by (metis (no_types) "*")
                        then have "nn \<le> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))"
                          using f1 by force
                        then show ?thesis
                          using f2 by (meson less_le_trans)
                      qed
                      hence "?time_again - 1 < ?time_again"
                        by auto
                      have "?time_again \<le> t + dly" and "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time_again - 1) \<noteq> Bv (bs ! xa)" and "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig ?time_again = Bv (bs ! xa)"
                        using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
                        using GreatestI_ex_nat *  apply (metis (mono_tags, lifting))
                        using GreatestI_ex_nat *  by smt
                      have "?w' xa sig (?time_again - 1) = ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig t"
                        using \<open>t < ?time_again\<close> \<open>?time_again - 1 < ?time_again\<close> 
                        unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
                        by (smt One_nat_def Suc_leI \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! xa)\<close> gr_implies_not0 le_add_diff_inverse not_less_iff_gr_or_eq plus_1_eq_Suc zero_less_diff)
                      moreover have "?w' xa sig (?time_again) = Bv (bs ! xa)"
                        unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
                        using False \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> 
                        using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! xa)\<close> by auto
                      ultimately have "?w' xa sig (?time_again - 1) \<noteq> ?w' xa sig ?time_again"
                        using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! xa)\<close> by auto
                      hence "?zeit \<le> ?time_again"
                      proof -
                        have "t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) \<and> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) \<le> t + dly \<and> (\<exists>n. n \<in> set [0..<length bs] \<and> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig n[sig, t, dly := Bv (bs ! n)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)))"
                          using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) \<le> t + dly\<close> \<open>xa \<in> {0..<length bs}\<close> \<open>snd to_worldline_init_bit \<omega> sig xa[sig, t, dly := Bv (bs ! xa)] sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) - 1) \<noteq> snd to_worldline_init_bit \<omega> sig xa[sig, t, dly := Bv (bs ! xa)] sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> 
                          using set_upt by blast
                        then show ?thesis
                          by (simp add: Bex_def_raw Least_le)
                      qed
                      let ?time' = " the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))"
                      have "?time_again \<le> t + dly"
                        using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) \<le> t + dly\<close> by blast
                      have "t < ?time_again"
                        using \<open>((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! index) \<Longrightarrow> zeit = (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! index) \<and> ((snd \<omega>)(sig := to_bit index \<circ> snd \<omega> sig)) sig n = Bv (bs ! index))\<close> 
                            \<open>t < (LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n))\<close> zeit_def 
                        using \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> by linarith
                      have "to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time_again - 1)) \<noteq> Bv (bs ! xa)"
                        by (smt One_nat_def Suc_leI Suc_pred \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig ((GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) - 1) \<noteq> Bv (bs ! xa)\<close> \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) - 1 < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> assms(1) fun_upd_same leD leI le_zero_eq o_apply prod.sel(2) worldline_raw_def)
                      moreover have "to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time_again)) = Bv (bs ! xa)"
                        using  `?time_again \<le> t + dly` `t < ?time_again`
                        assms(1) comp_def fun_upd_def worldline_raw_def snd_conv
                        by (smt \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) = Bv (bs ! xa)\<close> order.asym)
                      ultimately have "(to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) ?time_again sig \<noteq> None"
                        by (metis (no_types, lifting) signal_of_less_sig to_bit_signal_of' zero_option_def)
                      obtain val where "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time_again sig = Some val" 
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time_again sig \<noteq> None\<close> by auto
                      have "\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig). k \<le> t + dly"
                      proof -
                        have "to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) = Some val"
                          by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig = Some val\<close> to_trans_raw_sig_def)
                        then have "\<exists>n. to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig n \<noteq> None \<and> n \<le> t + dly"
                          using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) \<le> t + dly\<close> by blast
                        then show ?thesis
                          by (simp add: keys_def zero_option_def)
                      qed
                      hence time'_eq: "?time' = (GREATEST k. k \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig) \<and> k \<le> t + dly)"
                        unfolding inf_time_def by auto
                      hence "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)" and "?time' \<le> t + dly"
                        using GreatestI_ex_nat 
                        by (metis (mono_tags, lifting) \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig). k \<le> t + dly\<close> inf_time_def inf_time_ex1 inf_time_some_exists)+
                      have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig = to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time_again sig"
                      proof (rule ccontr)
                        assume "\<not> to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig ?time' sig = to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig ?time_again sig"
                        hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time_again =  val"
                          using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig" "?time_again" "sig" "(\<lambda>x. _)(sig := val)"]
                          using \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig :=
                          to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ>
                          snd \<omega> sig)) sig n = Bv (bs ! xa)) sig = Some val\<close> by auto
                        then obtain val' where "to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig ?time' sig = Some val'"
                        proof -
                          assume "\<And>val'. to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig)) sig (t + dly))) sig = Some val' \<Longrightarrow> thesis"
                          then show ?thesis
                            by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig)\<close> domIff dom_def keys_def not_None_eq to_trans_raw_sig_def zero_option_def)
                        qed
                        hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time' =  val'"
                          using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig" "?time_again" "sig" "(\<lambda>x. _)(sig := val')"] time'_eq
                          by (meson trans_some_signal_of')
                        also have "... \<noteq> val"
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd
                          \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig
                          := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig = Some val\<close>
                          \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig
                          (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig = Some val'\<close>
                          using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig\<close> by auto
                        finally have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time' \<noteq> 
                                      signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time_again "
                          using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa))
                          (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig
                          := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig :=
                          to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) = val\<close> by blast
                        have "t < ?time'"
                          by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig = Some val'\<close> leI option.simps(3) option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                        have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time') = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time'"
                          using `t < ?time'` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                        moreover have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time_again) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time_again"
                          using `t < ?time_again` to_bit_signal_of'_eq unfolding assms(1) time'_eq worldline_raw_def snd_conv fun_upd_def  by fastforce
                        ultimately have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time') \<noteq> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time_again)"
                          using \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) \<noteq> signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> by auto                  
                        have "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time' = val'"
                          using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig" "?time'" "sig" "(\<lambda>x. _)(sig := val')"] \<open>to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig ?time' sig = Some val'\<close>
                          by auto
                        have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig)) sig (t + dly))) = 
                              inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig)) sig (t + dly)"
                          using time'_eq 
                        proof -
                          have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly) \<noteq> None"
                            by (metis (no_types) \<open>\<And>thesis. (\<And>val'. to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig = Some val' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<le> t + dly\<close> inf_time_noneE2 option.simps(3) to_trans_raw_sig_def zero_option_def)
                          then show ?thesis
                            by (metis (no_types) \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)\<close> dom_def inf_time_someI keys_def option.exhaust_sel order_refl zero_option_def)
                        qed
                        hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig (t + dly) = 
                              signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time'"
                          unfolding to_signal_def comp_def by auto
                        hence "signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig)  \<tau> xa sig) sig ?time' = Bv (bs ! xa)"
                          using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)\<close> by auto
                        have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time_again) = Bv (bs ! xa)"
                          using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) = Bv (bs ! xa)\<close> by blast
                        have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time') = Bv (bs ! xa)"
                          using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) = signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)))\<close> \<open>signal_of (Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) = Bv (bs ! xa)\<close> by auto
                        show False
                          using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) = Bv (bs ! xa)\<close> \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) = Bv (bs ! xa)\<close> \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) \<noteq> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> by auto
                      qed
                      have h1: "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)"
                        using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)\<close> by blast
                      have "the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig) = Bv (bs ! xa)"
                      proof -
                        have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly) = Some ?time'"
                          by (simp add: \<open>\<exists>k\<in>keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig). k \<le> t + dly\<close> inf_time_def)
                        thus "the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig) = Bv (bs ! xa)"
                          using h1 unfolding to_signal_def comp_def  by (metis option.simps(5) to_trans_raw_sig_def)
                      qed
                      have "the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time_again sig) = Bv (bs ! xa)"
                      proof- 
                        have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig ?time_again = Bv (bs ! xa)"
                          using \<open>to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time_again)) = Bv (bs ! xa)\<close>
                          unfolding to_bit_signal_of'_eq[THEN sym] by auto
                        moreover have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig ?time_again = Some ?time_again"
                        proof (intro inf_time_someI)
                          show "?time_again \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                          proof -
                            have "\<exists>v. to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig = Some v"
                              by (metis \<open>\<And>thesis. (\<And>val. to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig = Some val \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
                            then show ?thesis
                              by (simp add: domIff to_trans_raw_sig_def)
                          qed
                        qed (auto)
                        ultimately show ?thesis
                          unfolding to_signal_def comp_def 
                          by (simp add: to_trans_raw_sig_def)
                      qed
                      have "?time_again = ?time'"
                      proof (rule Greatest_equality)
                        have "t \<le> ?time' - 1" 
                        proof (rule ccontr)
                          assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                            by auto
                          hence "?time' \<le> t" by auto
                          hence "\<tau> ?time' sig = None"
                            using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                          have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig \<noteq> None"
                            using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)\<close> 
                            by (metis domIff dom_is_keys to_trans_raw_sig_def)
                          thus "False"
                            using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                        qed
                        moreover have "to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! xa)"
                          unfolding to_bit_signal_of'_eq[THEN sym]
                        proof (cases "\<exists>n. t < n \<and> n < ?time' \<and> (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) n sig \<noteq> None")
                          case False
                          hence none: "\<And>n. t < n \<Longrightarrow> n \<le> ?time' - 1 \<Longrightarrow> (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) n sig = 0"
                            by (auto simp add: zero_option_def)
                          have " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (?time' - 1) = 
                                  signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t"
                            using signal_of_less_ind'[of "t" "?time' - 1" "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig" "sig", OF none] `t \<le> ?time' - 1`
                            by auto                    
                          also have "... \<noteq> (Bv (bs ! xa))"
                            using to_bit_signal_of'_eq 
                            using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig t \<noteq> Bv (bs ! xa) \<and> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (t + dly) = Bv (bs ! xa)\<close> by blast
                          finally show " signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (?time' - 1) \<noteq> (Bv (bs ! xa))"
                            by auto
                        next
                          case True
                          let ?key1 = "(GREATEST n. t < n \<and> n < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig n sig \<noteq> None)"
                          from True have "t < ?key1" and "?key1 < ?time'" and " to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig \<noteq> None"
                            using GreatestI_ex_nat[OF True]  using less_imp_le_nat by blast+
                          have *: "\<And>n. n > ?key1 \<Longrightarrow> n < ?time' \<Longrightarrow> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig n sig = None"
                            using Greatest_le_nat[where P="\<lambda>x. t < x \<and> x < ?time' \<and> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig x sig \<noteq> None" and b="?time'"]
                            by (smt \<open>t < (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig n sig \<noteq> None)\<close> leD less_imp_le_nat less_trans)
                          have inf_some: "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (?time' - 1) = Some ?key1"
                          proof (rule inf_time_someI)
                            show "?key1 \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                              using `to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig \<noteq> None`  by (simp add: domIff to_trans_raw_sig_def)
                          next
                            show "?key1 \<le> ?time' - 1"
                              using `?key1 < ?time'`  by linarith
                          next
                            { fix ta
                              assume "ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                              assume "ta \<le> ?time' - 1"
                              assume "?key1 < ta"
                              hence "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ta sig = None"
                                using *[OF `?key1 < ta`] `ta \<le> ?time' - 1` by simp
                              hence "ta \<notin> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                                by (simp add: domIff to_trans_raw_sig_def)
                              with `ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)` have False by auto }
                            thus "\<forall>ta \<in> dom (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig). ta \<le> ?time' - 1 \<longrightarrow> ta \<le> ?key1"
                              using not_le_imp_less by blast
                          qed
                          have non_stut: " non_stuttering (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) (to_bit xa o \<sigma>) sig"
                            using assms(5) non_stuttering_to_trans_raw_bit by force
                          hence "(to_trans_raw_bit (\<sigma> sig) \<tau> xa sig  ?key1 sig) \<noteq> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig"
                          proof -
                            have "?key1 \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                              using `to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig \<noteq> None`  by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
                            moreover have "?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                              using \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)\<close> by blast
                            moreover have "\<forall>k. ?key1 < k \<and> k < ?time' \<longrightarrow> k \<notin> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)"
                              using *  by (metis (mono_tags, lifting) domIff keys_def mem_Collect_eq to_trans_raw_sig_def
                              zero_option_def)
                            ultimately show ?thesis    
                              using `?key1 < ?time'` non_stut unfolding non_stuttering_def
                              by (simp add: to_trans_raw_sig_def)
                          qed
                          moreover have "(to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig) = Some (Bv (bs ! xa))"
                            by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa
                            sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau>
                            xa sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig
                            (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig) = Bv (bs ! xa)\<close>
                            domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                          ultimately have neq: "(to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig) \<noteq> Some (Bv (bs ! xa))"
                            by auto
                          then obtain valu where "(to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig) = Some valu" and "valu \<noteq> Bv (bs ! xa)"
                            using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig \<noteq> None\<close> by blast
                          have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (?time' - 1) = 
                                the (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig ?key1)"
                            using inf_some unfolding to_signal_def comp_def
                            by auto
                          also have "... \<noteq> Bv (bs ! xa)"
                            using \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?key1 sig \<noteq> None\<close> neq 
                            by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. t < n \<and> n < the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<and> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig n sig \<noteq> None) sig = Some valu\<close> option.sel to_trans_raw_sig_def)
                          finally show "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (?time' - 1) \<noteq> (Bv (bs ! xa))"
                            by blast
                        qed
                        ultimately have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time' - 1) = to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time' - 1))"
                          unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def by auto
                        hence *: "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! xa)"
                          using \<open>to_bit xa (signal_of (\<sigma> sig) \<tau> sig (?time' - 1)) \<noteq> Bv (bs ! xa)\<close> by auto
                        have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig = Some (Bv (bs ! xa))"
                          using \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig
                          (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig) = Bv (bs ! xa)\<close>
                          \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig :=
                          to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit
                          xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig \<noteq> None\<close> \<open>to_trans_raw_bit (\<sigma> sig)
                          \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa
                          sig)) sig (t + dly))) sig = to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le>
                          t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa)
                          \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig\<close> by
                          force
                        have "to_bit xa (signal_of (\<sigma> sig) \<tau> sig ?time') = (Bv (bs ! xa))"
                          using trans_some_signal_of'[of "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig", OF `to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig = Some (Bv (bs ! xa))`]
                          using to_bit_signal_of'_eq by fastforce
                        hence " ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) = Bv (bs ! xa)"
                          unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def 
                          using \<open>t \<le> the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) - 1\<close> by auto
                        thus "?time' \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (?time' - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig ?time' = Bv (bs ! xa)"    
                          using * `?time' \<le> t + dly` by auto  
                      next
                        have "t \<le> ?time' - 1" 
                        proof (rule ccontr)
                          assume "\<not> t \<le> ?time' - 1" hence "?time' - 1 < t"
                            by auto
                          hence "?time' \<le> t" by auto
                          hence "\<tau> ?time' sig = None"
                            using assms(2) unfolding context_invariant_def by (auto simp add: zero_fun_def zero_option_def)
                          have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig \<noteq> None"
                            using \<open>?time' \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)\<close> 
                            by (metis domIff dom_is_keys to_trans_raw_sig_def)
                          thus "False"
                            using \<open>\<tau> ?time' sig = None\<close> unfolding to_trans_raw_bit_def by auto
                        qed
                        fix y
                        assume "y \<le> t + dly \<and>  ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig y = Bv (bs ! xa)"
                        hence "y \<le> t + dly" and "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! xa)" and "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (y) = Bv (bs ! xa)"
                          by auto
                        have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig ?time' sig = Some (Bv (bs ! xa))"
                          by (metis \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly)) \<in> keys (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig)\<close> \<open>the (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig) = Bv (bs ! xa)\<close> domIff dom_def keys_def option.exhaust_sel to_trans_raw_sig_def zero_option_def)
                        hence "t < ?time'"
                          by (smt \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig \<noteq> None\<close> \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig)) sig (t + dly))) sig = to_trans_raw_bit (\<sigma> sig) \<tau> xa sig (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa)) sig\<close> leI option.simps(4) to_trans_raw_bit_def zero_fun_def zero_option_def)
                        have "y \<le> t \<or> t < y"
                          by auto
                        moreover
                        { assume "y \<le> t"
                          hence "y < ?time'" using `t < ?time'` by linarith }
                        moreover
                        { assume "t < y"
                          hence "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (y - 1) =  to_bit xa (signal_of (\<sigma> sig) \<tau> sig (y - 1))"
                            unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                          hence 0: "... \<noteq> (Bv (bs ! xa))"
                            using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (y - 1) \<noteq> Bv (bs ! xa)\<close> by auto
                          have "((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig y =  to_bit xa (signal_of (\<sigma> sig) \<tau> sig y)"
                            using `t < y`  unfolding assms(1) worldline_raw_def snd_conv fun_upd_def comp_def  by auto
                          hence 1: "... = Bv (bs ! xa)"
                            using \<open>((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig y = Bv (bs ! xa)\<close> by auto
                          have "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = Some (Bv (bs ! xa))"
                          proof (rule ccontr)
                            assume "\<not> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = Some (Bv (bs ! xa))"
                            then obtain x' where "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = None \<or> to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! xa))"
                              using domIff by fastforce
                            moreover
                            { assume "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = None"
                              hence "signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig y = 
                                     signal_of (\<sigma> sig) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig (y - 1)"
                                by (intro signal_of_less_sig)(simp add: zero_option_def)
                              with 0 1 have False 
                                by (metis \<open>to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = None\<close> signal_of_less_sig to_bit_signal_of' zero_option_def) }
                            moreover
                            { assume "to_trans_raw_bit (\<sigma> sig) \<tau> xa sig y sig = Some x' \<and> x' \<noteq> (Bv (bs ! xa))"
                              hence "signal_of ((Bv (case \<sigma> sig of Bv b' \<Rightarrow> b' | Lv sign bs \<Rightarrow> bs ! xa))) (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) sig y = x'" and "x' \<noteq> (Bv (bs ! xa))"
                                using trans_some_signal_of' by fastforce+
                              with 1 have False 
                                unfolding to_bit_signal_of'_eq by auto }
                            ultimately show False
                              by auto
                          qed
                          with `y \<le> t + dly` have "y \<le> ?time'"
                            unfolding time'_eq 
                            apply (intro Greatest_le_nat)
                            unfolding keys_def to_trans_raw_sig_def zero_option_def by auto }
                        ultimately show "y \<le> ?time'"
                          by auto  
                      qed
                      thus ?thesis    
                        using \<open>(LEAST n. t < n \<and> n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig (n - 1) \<noteq> snd to_worldline_init_bit \<omega> sig b[sig, t, dly := Bv (bs ! b)] sig n)) \<le> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! xa) \<and> ((snd \<omega>)(sig := to_bit xa \<circ> snd \<omega> sig)) sig n = Bv (bs ! xa))\<close> by linarith
                    qed
                    finally show ?thesis
                      by (simp add: False not_le_imp_less)
                  qed
                  finally have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa)) x sig = 0"
                    by (auto simp add: zero_option_def) }
                ultimately have "purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa)) x sig = 0"
                  by auto
                thus "x \<notin> {k. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa)) k sig \<noteq> 0}"
                  by auto
              qed
              hence "x \<notin> fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd) (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                unfolding member_fold_union2 map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt
                take_all[OF help_len] by auto                  
              with comb have "False"
                unfolding combine_trans_bit_def 
                by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>t' < t + dly\<close> \<open>x \<le> t'\<close> diff_diff_cancel less_imp_diff_less less_not_refl nat_diff_split zero_fun_def zero_less_diff zero_option_def) }
            thus " \<And>x. x \<in> dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig) \<Longrightarrow> t' < x"
              using leI by blast
          qed
          hence "signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = \<sigma> sig"
            unfolding to_signal_def comp_def by auto
          hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
            using \<open>snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = \<sigma> sig\<close> by auto }
        ultimately have "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
          by blast }
      moreover
      { assume thereisnt: "\<not> (\<exists>n>t. n \<le> t + dly \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b sig (n - 1) \<noteq> ?w' b sig n))"
        hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = snd \<omega> sig t"
          unfolding worldline_inert_upd2.simps snd_conv using \<open>t' < t + dly\<close> 
          using \<open>s' = sig\<close> \<open>t \<le> t'\<close> by auto
        also have "... = signal_of (\<sigma> sig) \<tau> sig t"
          unfolding assms(1) worldline_raw_def snd_conv by auto
        also have "... = \<sigma> sig"
          by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> signal_of_def zero_fun_def)
        finally have "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = \<sigma> sig"
          by auto
        have "inf_time (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs))) sig t' = None"
          unfolding inf_time_none_iff[THEN sym]
        proof 
          { fix x 
            assume "\<not> t' < x" hence "x \<le> t'" by auto
            hence "x < t + dly"
              using \<open>t' < t + dly\<close> le_less_trans by blast
            assume "x \<in> dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig)"
            hence "purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None"
              unfolding dom_def to_trans_raw_sig_def by auto
            hence *: "combine_trans_bit \<tau>
                    (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                         (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) sign sig t dly x sig \<noteq> None"
              unfolding purge_raw'_def by auto
            have **: "length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) \<le> length bs - 0"
              by auto
              
            have "x < t \<or> t \<le> x"
              by auto
            moreover
            { assume "x < t"
              hence "False"
                using * unfolding combine_trans_bit_def 
                by (simp add: \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> zero_fun_def zero_option_def) }
            moreover
            { assume "t \<le> x"
              hence "x \<in> fold (\<union>)
              (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                (zip (map (\<lambda>n. Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                  (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
              {}"
                using * unfolding combine_trans_bit_def 
                by (metis (full_types) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>x < t + dly\<close> dual_order.asym zero_fun_def zero_option_def)
              also have "... = fold (\<union>) (map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> n sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
                unfolding map_map[THEN sym] map_snd_zip_take length_map length_upt min.idem take_all[OF **]
                by auto
              finally have "\<exists>xa\<in>{0..<length bs}. 
                x \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> xa sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! xa)) (Bv (bs ! xa))) sig)"
                unfolding member_fold_union2 by auto
              then obtain b where pnone: "(purge_raw (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) t dly sig (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) x sig \<noteq> None" and "b < length bs"
                unfolding to_trans_raw_sig_def keys_def zero_option_def  using atLeastLessThan_iff by blast
              have "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t = Bv (bs ! b) 
                  \<or> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) \<noteq> Bv (bs ! b)
                  \<or> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq>  Bv (bs ! b) \<and> 
                    signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                by auto
              moreover
              { assume "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t = Bv (bs ! b) 
                  \<or> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) \<noteq> Bv (bs ! b)"
                hence "False"
                  using pnone unfolding purge_raw_def Let_def
                  by (metis (no_types, lifting) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None\<close> \<open>x < t + dly\<close> less_or_eq_imp_le linorder_neqE_nat pnone purge_raw_before_now_unchanged' purge_raw_neq_0_imp zero_fun_def zero_option_def) }
              moreover
              { assume "signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq>  Bv (bs ! b) \<and> 
                        signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)"
                hence "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly) = Some x"
                  using pnone unfolding purge_raw_def Let_def 
                  by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs) x sig \<noteq> None\<close> \<open>x < t + dly\<close> not_le_imp_less pnone purge_raw_before_now_unchanged' purge_raw_neq_0_imp zero_fun_def zero_option_def)
                let ?time' = " the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> sig) \<tau> b sig)) sig (t + dly))"
                let ?time = "(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
                have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b)"
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b) \<and> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)\<close> \<open>snd \<omega> sig t = signal_of (\<sigma> sig) \<tau> sig t\<close> to_bit_signal_of'_eq by fastforce
                have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)"
                  using \<open>signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig t \<noteq> Bv (bs ! b) \<and> signal_of (Bv (case \<sigma> sig of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> sig) \<tau> b sig) sig (t + dly) = Bv (bs ! b)\<close>  
                  unfolding to_bit_signal_of'_eq fun_upd_def  assms(1) worldline_raw_def snd_conv by auto
                have *: "\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)"
                proof (rule ccontr)
                  assume "\<not> (\<exists>n. t < n \<and> n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
                  hence imp: "\<And>n. t < n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                    by auto
                  { fix n 
                    assume "t \<le> n" and "n \<le> t + dly"
                    hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                      using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b)\<close> imp
                    proof (induction "n - t" arbitrary: t dly)
                      case 0 hence "n = t" by auto
                      then show ?case 
                        using 0 by auto
                    next
                      case (Suc x)
                      hence 0: "x = n - Suc t"
                        by auto
                      have 2: "n \<le> Suc t + (dly - 1) "
                        using Suc by auto
                      hence 1: "Suc t \<le> n "
                        using Suc by linarith
                      hence "Suc t \<le> t + dly"
                        using Suc by linarith
                      hence 3: "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (Suc t) \<noteq> Bv (bs ! b)"
                        using Suc(5-6) by auto
                      have 4: "\<And>n. Suc t < n \<Longrightarrow> n \<le> Suc t + (dly - 1) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                        using Suc(6) by auto
                      have "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                        using  Suc(1)[OF 0 1 2 3 4] by auto
                      thus ?case
                        by auto
                    qed }
                  hence "\<And>n. t \<le> n \<Longrightarrow> n \<le> t + dly \<Longrightarrow> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n \<noteq> Bv (bs ! b)"
                    by auto
                  thus False
                    using \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)\<close> le_add1 by blast
                qed
                have "t < ?time"
                proof -
                  have f1: "\<forall>p n na. (n::nat) \<le> Greatest p \<or> (\<exists>n. \<not> n \<le> na \<and> p n) \<or> \<not> p n"
                    by (metis (lifting) Greatest_le_nat)
                  obtain nn :: nat where
                    f2: "Bv (bs ! b) = ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig nn \<and> Bv (bs ! b) \<noteq> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (nn - 1) \<and> nn \<le> t + dly \<and> t < nn"
                    by (metis (lifting) "*")
                  then have "nn \<le> (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))"
                    using f1 by fastforce
                  then show ?thesis
                    using f2 order.strict_trans2 by blast
                qed
                have "?time \<le> t + dly"
                  by (metis (mono_tags, lifting) "*" GreatestI_ex_nat fun_upd_same)
                hence "((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (?time - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig ?time = Bv (bs ! b)"
                  by (smt "*" GreatestI_nat)
                hence "?w' b sig (?time - 1) \<noteq> ?w' b sig (?time)"
                  unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv
                  by (smt \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (t + dly) = Bv (bs ! b)\<close> \<open>((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig t \<noteq> Bv (bs ! b)\<close> diff_le_self order.strict_iff_order)
                with thereisnt have False
                  using \<open>(GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b)) \<le> t + dly\<close> \<open>b < length bs\<close> \<open>t < (GREATEST n. n \<le> t + dly \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig (n - 1) \<noteq> Bv (bs ! b) \<and> ((snd \<omega>)(sig := to_bit b \<circ> snd \<omega> sig)) sig n = Bv (bs ! b))\<close> by auto }
              ultimately have False
                by auto }
            ultimately have False
              by auto }
          thus "\<And>x. x \<in> dom (to_trans_raw_sig (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig) \<Longrightarrow> t' < x"
            by auto
        qed
        hence "signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t' = \<sigma> sig"
          unfolding to_signal_def comp_def by auto
        hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
          using \<open>snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = \<sigma> sig\<close> by auto }
      ultimately have "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = signal_of (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (Lv sign bs)) sig t'"
        by blast }
    ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t'"
      by (smt \<tau>'_def inr_post_raw'_def not_le signal_of_trans_post2 snd_conv worldline_raw_def) }
  moreover
  { assume "s' \<noteq> sig \<or> t' < t"
    moreover
    { assume "t' < t"
      hence 0: " snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =  signal_of (def s') \<theta> s' t'"
        unfolding worldline_raw_def by auto
      have "t' < t + dly"
        using `t' < t` by auto
      have "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t'"
        using `t' < t`  by (simp add: worldline_raw_def)
      hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t'"
        using `t' < t`  unfolding assms(1) worldline_inert_upd2.simps snd_conv worldline_inert_upd_def fun_upd_def
        by auto }
    moreover
    { assume "s' \<noteq> sig"
      hence "snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        unfolding worldline_inert_upd2.simps snd_conv fun_upd_def assms(1) by auto
      also have "... = snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t'"
      proof -
        have "\<And>n. (to_trans_raw_sig \<tau> s') n = (to_trans_raw_sig \<tau>' s') n"
          using `s' \<noteq> sig` unfolding \<tau>'_def inr_post_raw'_def
          by (metis purge_raw_does_not_affect_other_sig' to_trans_raw_sig_def trans_post_raw_diff_sig)
        hence "signal_of (\<sigma> s') \<tau> s' t' = signal_of (\<sigma> s') \<tau>'  s' t'"
          by (meson signal_of_equal_when_trans_sig_equal_upto)
        thus ?thesis
          unfolding worldline_raw_def by auto
      qed
      finally have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' "
        by auto }
    ultimately have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t'"
      by auto }
  ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_inert_upd2 \<omega> sig t dly (Lv sign bs)) s' t' "
    by blast
qed (simp add: assms(1) worldline_inert_upd_def worldline_raw_def)

lemma lift_inr_post_worldline_upd_comb:
  assumes "\<omega> = worldline_raw t \<sigma> \<theta> def \<tau>"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "0 < dly"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  assumes "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
  assumes "beval_world_raw \<omega> t exp v"
  shows "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_inert_upd2 \<omega> sig t dly v"
  using lift_inr_post_worldline_upd2 lift_inr_post_worldline_upd
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) val.exhaust)

lemma Bassign_inert_sound:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> (\<exists>x. beval_world_raw w t exp x \<and> Q (worldline_inert_upd2 w sig t dly x))"
    by (auto dest!: Bassign_inertE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a trans_raw"
    fix w w' :: "'a  worldline_init"
    fix \<gamma> def
    assume c: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    assume "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    assume "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    assume "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    assume "P w"
    assume ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    obtain x where "beval_world_raw w t exp x"
      using \<open>P w\<close> imp by metis
    have "snd (worldline_raw t \<sigma> \<theta> def \<tau>') = snd (worldline_inert_upd2 w sig t dly x)"
      using lift_inr_post_worldline_upd_comb[OF `w = worldline_raw t \<sigma> \<theta> def \<tau>` c ex assms] \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close>
      \<open>beval_world_raw w t exp x\<close> \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close> by auto
    with imp and `P w` have "Q(worldline_inert_upd2 w sig t dly x)"
      using \<open>beval_world_raw w t exp x\<close> beval_world_raw_deterministic by metis
    assume "w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
    hence "Q w'"
      using `Q(worldline_inert_upd2 w sig t dly x)` `snd (worldline_raw t \<sigma> \<theta> def \<tau>') = snd (worldline_inert_upd2 w sig t dly x)`
      by (metis (full_types) \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> \<open>All (non_stuttering
      (to_trans_raw_sig \<theta>) def)\<close> \<open>beval_world_raw w t exp x\<close> \<open>w = worldline_raw t \<sigma> \<theta> def \<tau>\<close> assms c
      ex lift_inr_post_worldline_upd_comb) }
  thus " \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
    unfolding seq_hoare_valid_def  by meson
qed

lemma Bcase_empty_valid:
  "\<Turnstile>\<^sub>t {P} Bcase exp [] {P}"
proof -
  { fix \<sigma> :: "'a state"
    fix \<tau> :: "'a trans_raw"
    fix \<gamma> \<theta> \<tau>' w w' def
    assume w_def: "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    assume " P w"
    assume " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bcase exp [] , \<tau>> \<longrightarrow>\<^sub>s \<tau>' "
    hence "\<tau>' = \<tau>"
      using b_seq_exec.intros(10) b_seq_exec_deterministic  by blast
    assume " w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
    hence "w' = w"
      unfolding \<open>\<tau>' = \<tau>\<close> w_def by auto
    hence "P w'"
      using \<open>P w\<close> by auto }
  thus ?thesis
    unfolding seq_hoare_valid_def by metis
qed

lemma Bcase_other_valid:
  assumes " \<Turnstile>\<^sub>t {P} ss {Q}"
  shows "\<Turnstile>\<^sub>t {P} Bcase exp ((Others, ss) # choices) {Q}"
proof -
  { fix \<sigma> :: "'a state"
    fix \<tau> :: "'a trans_raw"
    fix \<gamma> \<theta> \<tau>' w w' def
    assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bcase exp ((Others, ss) # choices) , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using Femto_VHDL_raw.seq_cases_bcase by fastforce
    assume "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    assume "P w"
    assume "context_invariant t \<sigma> \<gamma> \<theta> def \<tau> "
    assume "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    assume "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    assume "w' = worldline_raw t \<sigma> \<theta> def \<tau>' "
    hence  "Q w'"
      using assms unfolding seq_hoare_valid_def
      by (metis \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> \<open>All (non_stuttering (to_trans_raw_sig
      \<theta>) def)\<close> \<open>P w\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> \<open>w =
      worldline_raw t \<sigma> \<theta> def \<tau>\<close>) }
  thus ?thesis
    unfolding seq_hoare_valid_def  by metis
qed

lemma Bcase_if_valid:
  assumes "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x. beval_world_raw a t exp x \<and> beval_world_raw a t exp' x)} ss {Q}"
  assumes "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x x'. beval_world_raw a t exp x \<and> beval_world_raw a t exp' x' \<and> x \<noteq> x')} Bcase exp choices {Q}"
  shows   "\<Turnstile>\<^sub>t {P} Bcase exp ((Explicit exp', ss) # choices) {Q}"
proof -
  { fix \<sigma> :: "'a state"
    fix \<tau> :: "'a trans_raw"
    fix \<gamma> \<theta> \<tau>' w w' def
    assume *: " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bcase exp ((Explicit exp', ss) # choices) , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    have "\<exists>x x'. t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x \<and> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
      apply (rule Femto_VHDL_raw.seq_cases_bcase[OF *, rotated])
      by (metis Pair_inject choices.inject list.inject) blast+
    then obtain x x' where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
      by blast
    assume "P w"
    assume "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
      unfolding context_invariant_def by auto
    assume w_def: "w = worldline_raw t \<sigma> \<theta> def \<tau>"
    hence "state_of_world w t = \<sigma>"
      using state_of_world[OF _ `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`] by auto
    have "event_of_world w t = \<gamma>"
    proof (cases "0 < t")
      case True
      fix s
      have "snd w s t = \<sigma> s"
        using `state_of_world w t = \<sigma>` unfolding state_of_world_def by auto
      moreover have "snd w s (t - 1) = signal_of (def s) \<theta> s (t - 1)"
        using True  by (simp add: w_def worldline_raw_def)
      ultimately show ?thesis
        using True \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close>
        unfolding event_of_world_def context_invariant_def
        by (smt Collect_cong \<open>state_of_world w t = \<sigma>\<close> diff_less less_numeral_extra(1)
        less_numeral_extra(3) snd_conv state_of_world_def w_def worldline_raw_def)
    next
      case False
      hence "t = 0" by auto
      hence ev: "event_of_world w t = {s. snd w s 0 \<noteq> def s}"
        unfolding event_of_world_def by (simp add: w_def worldline_raw_def)
      have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
        using `t = 0` \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> unfolding context_invariant_def
        by auto
      have "\<theta> = 0"
        using \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> unfolding `t = 0`
        by (auto simp add: context_invariant_def zero_fun_def)
      hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
        using signal_of_empty by metis
      hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
        using \<gamma>_def' by auto
      moreover have "\<And>s.  snd w s 0 = \<sigma> s"
        using `state_of_world w t = \<sigma>` `t = 0` unfolding state_of_world_def by auto
      ultimately  have "\<gamma> = {s. snd w s 0 \<noteq> def s}"
        by auto
      thus ?thesis  using ev by auto
    qed
    assume "All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)"
    assume "All (non_stuttering (to_trans_raw_sig \<theta>) def)"
    hence "derivative_hist_raw w t = \<theta>"
      using derivative_is_history unfolding w_def
      by (metis \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> context_invariant_def)
    hence "beval_world_raw w t exp x"
    proof -
      have "get_time w = def"
        by (simp add: w_def worldline_raw_def)
      then show ?thesis
        by (simp add: \<open>derivative_hist_raw w t = \<theta>\<close> \<open>event_of_world w t = \<gamma>\<close> \<open>state_of_world w t = \<sigma>\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> beval_world_raw.intros)
    qed
    have "beval_world_raw w t exp' x'"
      using \<open>All (non_stuttering (to_trans_raw_sig \<theta>) def)\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>t , \<sigma>
      , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close> beval_beval_world_raw_ci w_def by fastforce
    assume "w' = worldline_raw t \<sigma> \<theta> def \<tau>'"
    have "x = x' \<or> x \<noteq> x'"
      by auto
    moreover
    { assume "x = x'"
      have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
        apply (rule seq_cases_bcase[OF *, rotated])
        by (metis Pair_inject \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close> \<open>x
        = x'\<close> beval_raw_deterministic choices.inject list.inject)blast+
      with `P w` have "Q w'"
        using assms unfolding seq_hoare_valid_def
        by (metis \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> \<open>All (non_stuttering
        (to_trans_raw_sig \<theta>) def)\<close> \<open>beval_world_raw w t exp x\<close> \<open>beval_world_raw w t exp' x'\<close>
        \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>w' = worldline_raw t \<sigma> \<theta> def \<tau>'\<close> \<open>x = x'\<close> w_def) }
    moreover
    { assume "x \<noteq> x'"
      have "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < Bcase exp choices, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
        apply (rule seq_cases_bcase[OF *])
        by (metis Pair_inject \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close>
        \<open>x \<noteq> x'\<close> beval_raw_deterministic choices.inject list.inject) auto
      with `P w` have "Q w'"
        using assms(2) unfolding seq_hoare_valid_def
        by (metis \<open>All (non_stuttering (to_trans_raw_sig \<tau>) \<sigma>)\<close> \<open>All (non_stuttering
        (to_trans_raw_sig \<theta>) def)\<close> \<open>beval_world_raw w t exp x\<close> \<open>beval_world_raw w t exp' x'\<close>
        \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>w' = worldline_raw t \<sigma> \<theta> def \<tau>'\<close> \<open>x \<noteq> x'\<close> w_def) }
    ultimately have "Q w'"
      by auto }
  thus ?thesis
    unfolding seq_hoare_valid_def by metis
qed

lemma soundness:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "nonneg_delay s"
  shows "\<Turnstile>\<^sub>t {P} s {R}"
  using assms
proof (induction rule:seq_hoare.induct)
  case (Bcase_others t P ss Q exp choices)
  hence "nonneg_delay ss"
    by auto
  hence " \<Turnstile>\<^sub>t {P} ss {Q}"
    using Bcase_others by auto
  then show ?case using Bcase_other_valid
    by blast
next
  case (Bcase_if t P exp exp' ss Q choices)
  hence " \<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x. beval_world_raw a t exp x \<and> beval_world_raw a t exp' x)} ss {Q}"
    by auto
  moreover have "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> (\<exists>x x'. beval_world_raw a t exp x \<and> beval_world_raw a t exp' x' \<and> x \<noteq> x')} Bcase exp choices {Q}"
    using Bcase_if by auto
  ultimately show ?case
    using Bcase_if_valid by blast
next
  case (AssignI t exp P sig dly)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound[OF `0 < dly`]  using seq_hoare.AssignI by fastforce
next
  case (Conseq P' P t s Q Q')
  then show ?case
    unfolding seq_hoare_valid_def by metis
qed (auto simp add: Bnull_sound Bassign_trans_sound Bcomp_hoare_valid Bguarded_hoare_valid Bcase_empty_valid)

end