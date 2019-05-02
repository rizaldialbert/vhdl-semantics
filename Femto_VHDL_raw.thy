(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Femto_VHDL_raw
  imports Main
          "HOL-Library.Infinite_Set"
          "HOL-IMP.Star"
begin

section "Syntax and Semantics"

text \<open> This theory formalises the syntax and semantics of a very small subset of VHDL --- hence the
prefix "Femto" in the name of this theory. This theory is heavily based on the work by van Tassel
@{cite "VanTassel1995"}, @{cite "Tassel1992"}.

This theory is divided into three parts:
  1. Syntax
  2. Elements of the semantics
  3. Semantics
      3.1. Big-step semantics
      3.2. Small-step semantics
\<close>

subsection \<open>Auxiliary developments\<close>

instantiation option :: (type) zero
begin

definition zero_option :: "'a option" where
  "zero_option = None"

instance proof qed
end

instantiation "fun" :: (type, zero) zero
begin

definition zero_fun :: "'a \<Rightarrow> 'b" where
  "zero_fun = (\<lambda>x. 0)"

instance proof qed
end

instantiation set :: (type) zero
begin

definition zero_set :: "'a set" where
  "zero_set = {}"

instance proof qed
end

lemma upd_eventually_cofinite:
  assumes  "\<forall>\<^sub>\<infinity>n. f n = 0"
  shows "\<forall>\<^sub>\<infinity>n. (f(m := k)) n = 0"
  using assms
  by (smt MOST_neq(2) eventually_elim2 fun_upd_def)

subsection "Core syntax"

text \<open>There are three elements of VHDL's syntax: expression, sequential statements, and concurrent
statements. Each data type for these elements is parameterised with a type variable. This type
variable is the placeholder for the type of the signals in a VHDL text. \<close>

type_synonym delay = nat

text \<open> Expressions contain logical operations such as conjunction, disjunction, etc. Included in
this expression are the construct for detecting whether a signal has changed from its previous value
--- @{term "Bsig_event"}. Construct @{term "Bsig_delayed"} checks the signal value in the previous
@{term "delay"} unit of time.\<close>

datatype 'signal bexp =
    Bsig 'signal
  | Bsig_event 'signal
  | Bsig_delayed 'signal delay
  | Bnot "'signal bexp"
  | Band "'signal bexp" "'signal bexp"
  | Bor "'signal bexp" "'signal bexp"
  | Bnand "'signal bexp" "'signal bexp"
  | Bnor "'signal bexp" "'signal bexp"
  | Bxor "'signal bexp" "'signal bexp"
  | Bxnor "'signal bexp" "'signal bexp"
  | Btrue
  | Bfalse

text \<open>Sequential statements in VHDL are standard. They include skip statements @{term "Bnull"},
sequential compositions @{term "Bcomp"}, branching statements @{term "Bguarded"}, and assignments.
Two types of assignment are formalised here: transport and inertial. The explanation of these two
assignments are best explained elsewhere (for example here \<^url>\<open>http://gmvhdl.com/delay.htm\<close>).
\<close>

datatype 'signal seq_stmt =
    Bcomp "'signal seq_stmt" "'signal seq_stmt"
  | Bguarded "'signal bexp" "'signal seq_stmt" "'signal seq_stmt"
  | Bassign_trans 'signal "'signal bexp" delay
  | Bassign_inert 'signal "'signal bexp" delay
  | Bnull

fun nonneg_delay :: "'signal seq_stmt \<Rightarrow> bool" where
  "nonneg_delay Bnull = True"
| "nonneg_delay (Bcomp s1 s2) \<longleftrightarrow> nonneg_delay s1 \<and> nonneg_delay s2"
| "nonneg_delay (Bguarded g s1 s2) \<longleftrightarrow> nonneg_delay s1 \<and> nonneg_delay s2"
| "nonneg_delay (Bassign_trans sig exp dly) \<longleftrightarrow> 0 < dly"
| "nonneg_delay (Bassign_inert sig exp dly) \<longleftrightarrow> 0 < dly"

fun signals_in :: "'signal seq_stmt \<Rightarrow> 'signal list" where
  "signals_in (Bnull) = []"
| "signals_in (Bassign_trans sig _ _) = [sig]"
| "signals_in (Bassign_inert sig _ _) = [sig]"
| "signals_in (Bguarded sig ss1 ss2) =  remdups (signals_in ss1 @ signals_in ss2)"
| "signals_in (Bcomp ss1 ss2) = remdups (signals_in ss1 @ signals_in ss2)"

lemma
  "distinct (signals_in ss)"
  by (induction ss) (auto)

abbreviation
  "signals_of s \<equiv> set (signals_in s)"

text \<open>Concurrent statements in VHDL is very simple: it is either a process running by itself, or
a composition of several processes. Each process is a sequential statement guarded by its
sensitivity list --- a set of signals which, if any of them changes, will trigger the execution of
the process it guards.\<close>

datatype 'signal conc_stmt =
      Bpar "'signal conc_stmt" "'signal conc_stmt" ( "_ || _" [81, 82]80)
    | Bsingle "'signal set" (get_seq: "'signal seq_stmt") (" process _ : _" [81, 82]80)

fun nonneg_delay_conc :: "'signal conc_stmt \<Rightarrow> bool" where
  "nonneg_delay_conc (Bsingle sl ss) \<longleftrightarrow> nonneg_delay ss"
| "nonneg_delay_conc (Bpar cs1 cs2) \<longleftrightarrow> nonneg_delay_conc cs1 \<and> nonneg_delay_conc cs2"

fun signals_from :: "'signal conc_stmt \<Rightarrow> 'signal list" where
  "signals_from (Bsingle _ s) = signals_in s"
| "signals_from (Bpar c1 c2)  = signals_from c1 @ signals_from c2"

text \<open>The well-formedness for the current formalisation is very simple. None of any two processes in
the VHDL text contains the same signals in the LHS of their sequential statements.\<close>

definition
  "conc_stmt_wf c = distinct (signals_from c)"

lemma
  "conc_stmt_wf (cs1 || cs2) \<Longrightarrow> disjnt ((set o signals_from) cs1)  ((set o signals_from) cs2)"
  unfolding conc_stmt_wf_def by (auto simp add:disjnt_def)

lemma
  "conc_stmt_wf (cs1 || cs2) \<Longrightarrow> conc_stmt_wf (cs2 || cs1)"
  unfolding conc_stmt_wf_def by auto

lemma [elim]:
  "conc_stmt_wf (cs1 || cs2) \<Longrightarrow> conc_stmt_wf cs1"
  unfolding conc_stmt_wf_def by auto

lemma [elim]:
  "conc_stmt_wf (cs1 || cs2) \<Longrightarrow> conc_stmt_wf cs2"
  unfolding conc_stmt_wf_def by auto

subsection \<open>Operational Semantics\<close>

type_synonym val = bool
type_synonym 'signal event = "'signal set"
type_synonym 'signal state = "'signal \<Rightarrow> val"

abbreviation def_state :: "'signal state" where
  "def_state \<equiv> (\<lambda>s. False)"

type_synonym 'signal valuation = "'signal \<rightharpoonup> val"

\<comment> \<open> represents scheduling \<close>
type_synonym 'signal trans_raw     = "nat \<Rightarrow> 'signal \<rightharpoonup> val"
type_synonym 'signal trans_raw_sig = "'signal \<Rightarrow> nat \<rightharpoonup> val"

definition to_trans_raw_sig :: "'signal trans_raw \<Rightarrow> 'signal trans_raw_sig" where
  "to_trans_raw_sig \<tau> = (\<lambda>sig n. \<tau> n sig)"

definition keys :: "('a::linorder \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where
  "keys f = {k. f k \<noteq> 0}"

lemma keys_at_most_to_trans_raw_sig:
  assumes "\<forall>k \<in> keys \<theta>. k < t"
  shows "\<forall>k \<in> keys (to_trans_raw_sig \<theta> s). k < t"
  using assms unfolding to_trans_raw_sig_def
  by (metis (mono_tags) keys_def mem_Collect_eq zero_fun_def)

text \<open>From transaction to function of time (signal)\<close>

lemma trans_empty_keys:
  fixes \<tau> :: "'signal trans_raw"
  shows "\<tau> = 0 \<longleftrightarrow> keys \<tau> = {}"
  unfolding zero_fun_def zero_option_def keys_def by auto

(*TODO: Would this be more appropriate if we use Inf? *)
definition inf_time :: "'signal trans_raw_sig \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat option" where
  "inf_time \<tau> sig n = 
           (if \<exists>k\<in> keys(\<tau> sig). k \<le> n then Some (GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> n)  else None)"

lemma inf_time_when_exist:
  "inf_time \<tau> sig n = Some k \<Longrightarrow> k = (GREATEST l. l \<in> keys (\<tau> sig) \<and> l \<le> n)"
    unfolding inf_time_def by (auto split:if_splits)

lemma inf_time_some_exists:
  assumes "inf_time \<tau> sig n = Some k"
  shows "k \<in> keys (\<tau> sig) \<and> k \<le> n"
  using assms unfolding inf_time_when_exist[OF assms]
  by (auto intro!: GreatestI_ex_nat[where P="\<lambda>k. k \<in> keys (\<tau> sig) \<and> k \<le> n"] 
           simp add: inf_time_def split:if_splits)

lemma inf_time_at_most:
  assumes "inf_time \<tau> sig i = Some k"
  shows "k \<le> i"
  using assms unfolding inf_time_def
  by (metis (no_types, lifting) GreatestI_nat option.distinct(1) option.inject)

lemma dom_imp_keys:
  fixes \<tau> :: "'a trans_raw"
  shows "t \<in> dom (to_trans_raw_sig \<tau> sig) \<Longrightarrow> t \<in> keys \<tau>"
  by (metis (mono_tags) dom_def keys_def mem_Collect_eq to_trans_raw_sig_def zero_fun_def zero_option_def)

lemma dom_is_keys:
  fixes \<tau> :: "'a trans_raw_sig"
  shows "dom (\<tau> sig) = keys (\<tau> sig)"
  by (simp add: dom_def keys_def zero_option_def)

lemma inf_time_someE:
  assumes "inf_time \<tau> sig n = Some k"
  shows "\<forall>t \<in> dom (\<tau> sig). t \<le> n \<longrightarrow> t \<le> k"
proof -
  have "\<exists>k \<in> keys (\<tau> sig). k \<le> n"
    using assms unfolding inf_time_def by (metis option.simps(3))
  hence k_def: "k = (GREATEST l. l \<in> keys (\<tau> sig) \<and> l \<le> n)"
    using assms unfolding inf_time_def by auto
  have "\<forall>t \<in> keys (\<tau> sig). t \<le> n \<longrightarrow> t \<le> k"
    unfolding k_def by (auto intro!: Greatest_le_nat)
  thus ?thesis
    unfolding dom_is_keys by auto
qed

lemma inf_time_none_iff:
  "(\<forall>t \<in> dom (\<tau> sig). n < t) \<longleftrightarrow> inf_time \<tau> sig n = None"
  unfolding dom_is_keys inf_time_def  using leD by auto

lemma inf_time_noneE2:
  fixes  \<tau> :: "'signal trans_raw_sig"
  assumes "inf_time \<tau> sig n = None"
  shows "\<forall>k. k \<le> n \<longrightarrow> (\<tau> sig) k = 0"
  using assms
  by (metis domIff inf_time_none_iff less_diff_conv2 not_less_zero plus_nat.add_0 zero_option_def)

lemma inf_time_neq_t_choice:
  assumes "inf_time (to_trans_raw_sig \<tau>) s i \<noteq> Some t"
  assumes "t \<le> i"
  assumes "t \<in> dom (to_trans_raw_sig \<tau> s)"
  shows "\<exists>t' > t. inf_time (to_trans_raw_sig \<tau>) s i = Some t'"
proof -
  obtain t' where *: "inf_time (to_trans_raw_sig \<tau>) s i = Some t' \<and> t' \<noteq> t"
    using assms  option.exhaust_sel  by (metis inf_time_none_iff leD)
  have "t' > t"
  proof (rule ccontr)
    assume "\<not> t' > t"  hence "t' < t" using * by auto
    have " \<forall>n \<in> dom (to_trans_raw_sig \<tau> s). n \<le> i \<longrightarrow> n \<le> t'"
      using * by (auto dest!: inf_time_someE)
    with assms(2-3) `t' < t` show "False" by auto
  qed
  thus ?thesis using * by auto
qed

lemma inf_time_equal_when_same_trans_upto:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> \<tau>1 n =  \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "inf_time (to_trans_raw_sig \<tau>1) sig n = inf_time (to_trans_raw_sig \<tau>2) sig n"
proof -
  have 0: "\<And>n. n \<le> maxtime \<Longrightarrow> (to_trans_raw_sig \<tau>1 sig) n = (to_trans_raw_sig \<tau>2 sig) n"
    using assms(1) unfolding to_trans_raw_sig_def by auto
  let ?\<tau>1' = "to_trans_raw_sig \<tau>1"
  let ?\<tau>2' = "to_trans_raw_sig \<tau>2"
  have "(\<exists>k\<in>keys (to_trans_raw_sig \<tau>1 sig). k \<le> n) \<longleftrightarrow> (\<exists>k\<in>keys (to_trans_raw_sig \<tau>1 sig). k \<le> n)"
    using 0 by blast
  moreover have "(GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>1 sig) \<and> k \<le> n) = 
                 (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>2 sig) \<and> k \<le> n)"
    using 0 by (metis assms(2) domIff dom_def keys_def le_trans zero_option_def)
  ultimately show "inf_time ?\<tau>1' sig n = inf_time ?\<tau>2' sig n"
    unfolding inf_time_def 
    by (metis (mono_tags) "0" assms(2) domIff dom_def keys_def le_trans zero_option_def)
qed

lemma inf_time_equal_when_same_trans_upto_strict:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n < maxtime \<Longrightarrow> (to_trans_raw_sig \<tau>1 sig) n = (to_trans_raw_sig \<tau>2 sig) n"
  assumes "n < maxtime"
  shows "inf_time (to_trans_raw_sig \<tau>1) sig n = inf_time (to_trans_raw_sig \<tau>2) sig n"
proof -
  have 0: "\<And>n. n < maxtime \<Longrightarrow> (to_trans_raw_sig \<tau>1 sig) n = (to_trans_raw_sig \<tau>2 sig) n"
    using assms(1) unfolding to_trans_raw_sig_def by auto
  let ?\<tau>1' = "to_trans_raw_sig \<tau>1"
  let ?\<tau>2' = "to_trans_raw_sig \<tau>2"
  have "(\<exists>k\<in>keys (to_trans_raw_sig \<tau>1 sig). k \<le> n) \<longleftrightarrow> (\<exists>k\<in>keys (to_trans_raw_sig \<tau>1 sig). k \<le> n)"
    using 0 by blast
  moreover have "(GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>1 sig) \<and> k \<le> n) = 
                 (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>2 sig) \<and> k \<le> n)"
    using 0 `n < maxtime` by (metis domIff dom_def keys_def le_less_trans zero_option_def)
  ultimately show "inf_time ?\<tau>1' sig n = inf_time ?\<tau>2' sig n"
    unfolding inf_time_def by (smt "0" assms(2) keys_def le_less_trans mem_Collect_eq)
qed

lemma inf_time_update:
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  assumes "res = \<theta>(t := Some o \<sigma>)"
  assumes "t \<le> i"
  shows "inf_time (to_trans_raw_sig res) sig i = Some t"
proof -
  have f1: "\<And>f a n na. inf_time f (a::'a) n \<noteq> Some na \<or> na \<in> {n. f a n \<noteq> 0}"
    by (metis inf_time_some_exists keys_def)
  have f2: "res t sig \<noteq> None"
    by (simp add: assms(2))
  have "\<forall>n f a na. \<exists>nb. (\<not> n \<le> na \<or> n \<notin> dom (to_trans_raw_sig f (a::'a)) \<or> n < nb \<or> inf_time (to_trans_raw_sig f) a na = Some n) \<and> (\<not> n \<le> na \<or> n \<notin> dom (to_trans_raw_sig f a) \<or> inf_time (to_trans_raw_sig f) a na = Some n \<or> inf_time (to_trans_raw_sig f) a na = Some nb)"
    by (metis (lifting) inf_time_neq_t_choice)
  then obtain nn :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> bool option) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
    f3: "\<And>n na f a. (\<not> n \<le> na \<or> n \<notin> dom (to_trans_raw_sig f a) \<or> n < nn n f a na \<or> inf_time (to_trans_raw_sig f) a na = Some n) \<and> (\<not> n \<le> na \<or> n \<notin> dom (to_trans_raw_sig f a) \<or> inf_time (to_trans_raw_sig f) a na = Some n \<or> inf_time (to_trans_raw_sig f) a na = Some (nn n f a na))"
    by moura
  moreover
  { assume "nn t res sig i \<noteq> t \<and> res t sig \<noteq> None"
    moreover
    { assume "\<theta> (nn t res sig i) sig = 0 \<and> nn t res sig i \<noteq> t \<and> res t sig \<noteq> None"
      then have "\<exists>n. t \<in> dom (to_trans_raw_sig res sig) \<and> Some (nn t res sig i) = Some n \<and> to_trans_raw_sig res sig n = 0"
        by (simp add: assms(2) domIff to_trans_raw_sig_def)
      then have ?thesis
        using f3 f1 assms(3) by blast }
    ultimately have "res t sig \<noteq> None \<and> \<not> t < nn t res sig i \<or> inf_time (to_trans_raw_sig res) sig i = Some t"
      by (simp add: assms(1) zero_fun_def) }
  ultimately show ?thesis
    using f2 by (metis (no_types) assms(3) domIff to_trans_raw_sig_def)
qed

lemma some_inf_time:
  "\<tau> n = Some o \<sigma> \<Longrightarrow> inf_time (to_trans_raw_sig \<tau>) sig n = Some n" 
    by (metis (mono_tags, hide_lams) comp_eq_dest_lhs domIff inf_time_at_most inf_time_neq_t_choice
    not_le option.simps(3) order_refl to_trans_raw_sig_def)

lemma some_inf_time':
  "\<tau> n sig = Some (\<sigma> sig) \<Longrightarrow> inf_time (to_trans_raw_sig \<tau>) sig n = Some n" 
    by (metis (no_types, hide_lams) domIff inf_time_at_most inf_time_neq_t_choice le_less_trans
    less_irrefl option.simps(3) order_refl to_trans_raw_sig_def)

lemma inf_time_at_zero:
  "\<tau> 0 = 0 \<Longrightarrow> inf_time (to_trans_raw_sig \<tau>) sig 0 = None"
    by (metis domIff inf_time_none_iff neq0_conv to_trans_raw_sig_def zero_fun_def zero_option_def)

lemma inf_time_less:
  assumes "\<tau> sig t = 0"
  shows "inf_time \<tau> sig t = inf_time \<tau> sig (t - 1)"
proof -
  have "(\<exists>k\<in>keys (\<tau> sig). k \<le> t) \<longleftrightarrow> (\<exists>k\<in>keys (\<tau> sig). k \<le> t - 1)" 
    using assms  keys_def le_less le_simps(2) by fastforce
  moreover have "(GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> t) = 
                 (GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> t - 1)"
    using assms  
    by (metis Suc_diff_1 diff_le_self domIff dom_def keys_def le0 le_less le_simps(2) le_trans
    zero_option_def)
  ultimately show ?thesis
    unfolding inf_time_def by auto
qed

lemma inf_time_someI:
  assumes "k \<in> dom (\<tau> sig)" and "k \<le> n"
  assumes "\<forall>t \<in> dom (\<tau> sig). t \<le> n \<longrightarrow> t \<le> k"
  shows "inf_time \<tau> sig n = Some k"
  using assms unfolding dom_is_keys inf_time_def
  by (metis (no_types, lifting) Greatest_equality)

definition to_signal :: "val \<Rightarrow> 'signal trans_raw_sig \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val" where
  "to_signal def \<tau> sig t = (case inf_time \<tau> sig t of
                              None    \<Rightarrow> def
                            | Some t' \<Rightarrow> the ((\<tau> sig) t'))"

lemma to_signal_equal_when_trans_equal_upto:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> \<tau>1 n = \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "to_signal def (to_trans_raw_sig \<tau>1) sig n = to_signal def (to_trans_raw_sig \<tau>2) sig n"
proof -
  have "inf_time (to_trans_raw_sig \<tau>1) sig n = inf_time (to_trans_raw_sig \<tau>2) sig n"
    using inf_time_equal_when_same_trans_upto[OF assms] by auto
  moreover have "\<And>n. n \<le> maxtime \<Longrightarrow> (to_trans_raw_sig \<tau>1 sig) n =  (to_trans_raw_sig \<tau>2 sig) n"
    using assms unfolding to_trans_raw_sig_def by auto
  ultimately show ?thesis
    using assms unfolding to_signal_def by (auto dest!: inf_time_at_most split:option.splits)
qed

abbreviation "signal_of def \<equiv> to_signal def o to_trans_raw_sig"

lemma [simp]:
  "to_trans_raw_sig 0 = 0"
    by (simp add: zero_fun_def to_trans_raw_sig_def)

lemma [simp]:
  "inf_time 0 sig t = None"
  by (simp add: zero_fun_def inf_time_def keys_def)

lemma signal_of_empty[simp]:
  "signal_of def 0 sig t = def"
  unfolding to_signal_def comp_def by auto
 
lemma signal_of_zero:
  "\<tau> 0 sig = 0 \<Longrightarrow> signal_of def \<tau> sig 0 = def"
    by (metis comp_apply domIff inf_time_none_iff neq0_conv option.case(1) to_signal_def to_trans_raw_sig_def zero_option_def)

lemma signal_of_equal_when_trans_equal_upto:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow>  \<tau>1 n = \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "signal_of def \<tau>1 sig n = signal_of def \<tau>2 sig n"
  using to_signal_equal_when_trans_equal_upto[OF assms] by auto

lemma signal_of_equal_when_trans_sig_equal_upto:
  assumes "\<And>n. to_trans_raw_sig \<tau>1 sig n =  to_trans_raw_sig \<tau>2 sig n"
  shows "signal_of def \<tau>1 sig m = signal_of def \<tau>2 sig m"
proof -
  have "to_trans_raw_sig \<tau>1 sig = to_trans_raw_sig \<tau>2 sig"
    using assms by (intro ext, auto)
  hence "inf_time (to_trans_raw_sig \<tau>1) sig m = inf_time (to_trans_raw_sig \<tau>2) sig m"
    unfolding inf_time_def by auto
  thus ?thesis
    using assms unfolding to_signal_def comp_def  by (simp add: option.case_eq_if)
qed

lemma trans_some_signal_of:
  assumes "\<tau> n = Some o \<sigma>"
  shows "signal_of def \<tau> sig n = \<sigma> sig"
  using assms 
  by (metis (mono_tags, lifting) comp_apply not_None_eq option.case_eq_if option.sel some_inf_time
  to_signal_def to_trans_raw_sig_def)

lemma trans_some_signal_of':
  assumes "\<tau> n sig = Some (\<sigma> sig)"
  shows "signal_of def \<tau> sig n = \<sigma> sig"
  using assms some_inf_time'[of "\<tau>" "n" "sig" "\<sigma>", OF assms]
  unfolding to_signal_def comp_def to_trans_raw_sig_def by auto

lemma signal_of_less_sig:
  assumes "\<tau> t sig = 0"
  shows "signal_of def \<tau> sig t = signal_of def \<tau> sig (t - 1)"
  using assms by (simp add: inf_time_less to_signal_def to_trans_raw_sig_def)

lemma signal_of_suc_sig:
  assumes "\<tau> (Suc t) sig = 0"
  shows "signal_of def \<tau> sig (Suc t) = signal_of def \<tau> sig t"
  using assms by (simp add: inf_time_less to_signal_def to_trans_raw_sig_def)
 
lemma signal_of_less:
  assumes "\<tau> t = 0"
  shows "signal_of def \<tau> sig t = signal_of def \<tau> sig (t - 1)"
  using assms by (metis signal_of_less_sig zero_fun_def)

lemma signal_of_less_ind':
  assumes "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> \<tau> n sig = 0"
  assumes "k1 \<le> k2"
  shows "signal_of def \<tau> sig k2 = signal_of def \<tau> sig k1"
  using assms
  by (induction "k2", simp)
     (metis (no_types, lifting) Suc_diff_1 le_Suc_eq le_eq_less_or_eq nat.simps(1)
     signal_of_less_sig zero_less_Suc)

lemma signal_of_less_ind:
  assumes "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> \<tau> n = 0"
  assumes "k1 \<le> k2"
  shows "signal_of def \<tau> sig k2 = signal_of def \<tau> sig k1"
  using assms by (metis signal_of_less_ind' zero_fun_def)

lemma signal_of_elim:
  assumes "signal_of def \<tau> sig k = val"
  shows "(\<exists>m \<le> k.  (to_trans_raw_sig \<tau> sig) m = Some val) \<or>
         (\<forall>m \<le> k.  (to_trans_raw_sig \<tau> sig) m = None \<and> val = def)"
proof -
  obtain t' where "inf_time (to_trans_raw_sig \<tau>) sig k = None \<or> 
                   inf_time (to_trans_raw_sig \<tau>) sig k = Some t'"
    by (meson inf_time_def)
  moreover
  { assume none: "inf_time (to_trans_raw_sig \<tau>) sig k = None"
    have "\<forall>m \<le> k.  (to_trans_raw_sig \<tau> sig) m = None"
      using inf_time_noneE2[OF none] unfolding to_trans_raw_sig_def by (auto simp add: zero_option_def)
    moreover have "val = def"
      using assms none unfolding to_signal_def comp_def by auto
    ultimately have ?thesis 
      by auto }
  moreover
  { assume some: "inf_time (to_trans_raw_sig \<tau>) sig k = Some t'"
    have "t' \<in> keys (to_trans_raw_sig \<tau> sig) \<and> t' \<le> k"
      using inf_time_some_exists[OF some] by auto
    then obtain val' where "to_trans_raw_sig \<tau> sig t' = Some val'" and "t' \<le> k"
      unfolding to_trans_raw_sig_def keys_def by (auto simp add: zero_option_def)
    moreover have "the (to_trans_raw_sig \<tau> sig t') = val"
      using assms some unfolding to_signal_def comp_def by auto
    ultimately have "val = val'"
      by auto
    with \<open>t' \<le> k\<close> have ?thesis
      using \<open>to_trans_raw_sig \<tau> sig t' = Some val'\<close> by auto }
  ultimately show ?thesis by auto
qed

subsection \<open>Semantics of @{typ "'signal bexp"}\<close>

fun xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<longleftrightarrow> (x \<or> y) \<and> (x \<noteq> y)"

text \<open>The semantics of expression is standard. A slightly more involved denotation is for
@{term "Bsig_delayed"}. Basically, it gets the value in the history @{term "snd \<theta> :: 'signal trans_raw"}
at time @{term "now - t"} where @{term "t"} is the delay.\<close>

fun beval_raw :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal bexp \<Rightarrow> val"
  where
  "beval_raw now \<sigma> \<gamma> \<theta> (Bsig sig) = \<sigma> sig"
| "beval_raw now \<sigma> \<gamma> \<theta> (Btrue) = True"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bfalse) = False"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bsig_delayed sig t) = signal_of False \<theta> sig (now - t)"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bsig_event sig) = (sig \<in> \<gamma>)"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bnot e) \<longleftrightarrow> \<not> beval_raw now \<sigma> \<gamma> \<theta> e"
| "beval_raw now \<sigma> \<gamma> \<theta> (Band e1 e2) \<longleftrightarrow> beval_raw now \<sigma> \<gamma> \<theta> e1 \<and> beval_raw now \<sigma> \<gamma> \<theta> e2"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bor e1 e2) \<longleftrightarrow> beval_raw now \<sigma> \<gamma> \<theta> e1 \<or> beval_raw now \<sigma> \<gamma> \<theta> e2"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bnand e1 e2) \<longleftrightarrow> \<not> (beval_raw now \<sigma> \<gamma> \<theta> e1 \<and> beval_raw now \<sigma> \<gamma> \<theta> e2)"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bnor e1 e2) \<longleftrightarrow> \<not> (beval_raw now \<sigma> \<gamma> \<theta> e1 \<or> beval_raw now \<sigma> \<gamma> \<theta> e2)"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bxor e1 e2) \<longleftrightarrow> xor (beval_raw now \<sigma> \<gamma> \<theta> e1) (beval_raw now \<sigma> \<gamma> \<theta> e2)"
| "beval_raw now \<sigma> \<gamma> \<theta> (Bxnor e1 e2) \<longleftrightarrow> \<not> xor (beval_raw now \<sigma> \<gamma> \<theta> e1) (beval_raw now \<sigma> \<gamma> \<theta> e2)"

abbreviation beval_raw_abb :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw
                                                                      \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
 ("_ , _ , _ , _ \<turnstile> _ \<longrightarrow>\<^sub>b _") where
  "now, \<sigma>, \<gamma>, \<theta> \<turnstile> e \<longrightarrow>\<^sub>b val \<equiv> beval_raw now \<sigma> \<gamma> \<theta> e = val"

subsection \<open>Semantics of @{typ "'signal seq_stmt"}\<close>

text \<open>The semantics for @{term "Bcomp"} @{term "Bnull"} and @{term "Bguarded"} is very
straightforward, but not so for @{term "Bassign_trans"} and @{term "Bassign_inert"}. The previous
one relies on the following function of @{term "trans_post"} which has the meaning of posting a
transaction (as is database transaction). The latter needs additional function of @{term "purge"}
which eliminates signal spikes before it posts a transaction. Jump (or search more precisely) for
@{term "b_seq_exec"} immediately for the semantics of sequential statements.\<close>

definition post_raw :: "'signal \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where
  "post_raw sig v \<tau> t = (\<lambda>t'. if t' = t    then (\<tau> t') (sig := Some v) else
                              if t' > t    then (\<tau> t') (sig := None) else
                             \<comment> \<open>t' < t\<close>  \<tau> t')"

definition preempt_raw :: "'signal \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where
  "preempt_raw sig \<tau> t = (\<lambda>t'. if t' \<ge> t then (\<tau> t') (sig := None) else \<tau> t')"

(* Is this used elsewhere? *)
definition preempt_raw_strict :: "'signal \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal trans_raw"
  where
  "preempt_raw_strict sig \<tau> t = (\<lambda>t'. if t' > t then (\<tau> t') (sig := None) else \<tau> t')"

fun post_necessary_raw :: "nat \<Rightarrow> (nat \<Rightarrow> 'signal \<rightharpoonup> bool) \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "post_necessary_raw 0       \<tau> t s val def \<longleftrightarrow> (case \<tau> t s of None \<Rightarrow> val \<noteq> def | Some v \<Rightarrow> v \<noteq> val)"
| "post_necessary_raw (Suc n) \<tau> t s val def \<longleftrightarrow> (case \<tau> (t + Suc n) s of None \<Rightarrow> post_necessary_raw n \<tau> t s val def | Some v \<Rightarrow> v \<noteq> val)"

lemma post_necessary_raw_correctness:
  "\<not> post_necessary_raw n \<tau> t s val def \<longleftrightarrow> (\<exists>i\<ge>t. i \<le> t + n \<and> \<tau> i s = Some val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None))
                                        \<or>   (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val = def"
proof (induction n)
  case 0
  then show ?case by (auto split:option.splits)
next
  case (Suc n)
  obtain v where "\<tau> (t + Suc n) s = None \<or> \<tau> (t + Suc n) s = Some v"
    by (meson not_None_eq)
  moreover
  { assume "\<tau> (t + Suc n) s = None"
    hence "\<not> post_necessary_raw (Suc n) \<tau> t s val def \<longleftrightarrow> \<not> post_necessary_raw n \<tau> t s val def"
      by auto
    also have "... \<longleftrightarrow> ((\<exists>i\<ge>t. i \<le> t + n \<and> \<tau> i s = Some val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val = def)"
      using Suc by auto
    also have "... \<longleftrightarrow> ((\<exists>i\<ge>t. i \<le> t + Suc n \<and> \<tau> i s = Some val \<and> (\<forall>j>i. j \<le> t + Suc n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<ge>t. i \<le> t + Suc n \<longrightarrow> \<tau> i s = None) \<and> val = def)"
      using `\<tau> (t + Suc n) s = None` by (metis add_Suc_right le_SucE le_SucI option.distinct(1))
    finally have ?case by auto }
  moreover
  { assume "\<tau> (t + Suc n) s = Some v"
    hence "\<not> post_necessary_raw (Suc n) \<tau> t s val def \<longleftrightarrow> v = val"
      by auto
    hence ?case
      using `\<tau> (t + Suc n) s = Some v`
      by (smt le_add1 le_eq_less_or_eq not_le option.distinct(1) option.inject) }
  ultimately show ?case by fastforce
qed  

lemma post_necessary_raw_correctness2:
  "post_necessary_raw n \<tau> t s val def \<longleftrightarrow> (\<exists>i\<ge>t. i \<le> t + n \<and> \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None))
                                      \<or>   (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val \<noteq> def"
proof (induction n)
  case 0
  then show ?case by (auto split:option.splits)
next
  case (Suc n)
  obtain v where "\<tau> (t + Suc n) s = None \<or> \<tau> (t + Suc n) s = Some v"
    by (meson not_None_eq)
  moreover
  { assume "\<tau> (t + Suc n) s = None"
    hence "post_necessary_raw (Suc n) \<tau> t s val def \<longleftrightarrow> post_necessary_raw n \<tau> t s val def"
      by auto
    also have "... \<longleftrightarrow> ((\<exists>i\<ge>t. i \<le> t + n \<and> \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val \<noteq> def)"
      using Suc by auto
    also have "... \<longleftrightarrow> ((\<exists>i\<ge>t. i \<le> t + Suc n \<and> \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + Suc n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<ge>t. i \<le> t + Suc n \<longrightarrow> \<tau> i s = None) \<and> val \<noteq> def)"
      using `\<tau> (t + Suc n) s = None` by (metis add_Suc_right le_SucE le_SucI option.distinct(1))
    finally have ?case by auto }
  moreover
  { assume "\<tau> (t + Suc n) s = Some v"
    hence "post_necessary_raw (Suc n) \<tau> t s val def \<longleftrightarrow> v \<noteq> val"
      by auto
    hence ?case
      using `\<tau> (t + Suc n) s = Some v`
      by (smt calculation(2) leD le_add1 le_eq_less_or_eq option.inject) }
  ultimately show ?case by fastforce
qed

lemma post_necessary_raw_same:
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  shows "post_necessary_raw n \<tau>1 t s val def = post_necessary_raw n \<tau>2 t s val def"
  using assms  by (smt post_necessary_raw_correctness)

definition trans_post_raw :: 
  "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal trans_raw" where
  "trans_post_raw s val def \<tau> t dly = 
      (if post_necessary_raw (dly - 1) \<tau> t s val def then 
          post_raw s val \<tau> (t + dly) 
       else 
          preempt_raw s \<tau> (t + dly))"

lemma trans_post_raw_imply_neq_map_empty:
  assumes "\<tau>' =  trans_post_raw sig e def \<tau> t dly"
  assumes "(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> \<tau> i sig = None) \<Longrightarrow> e \<noteq> def"
  assumes "0 < dly"
  shows "\<tau>' \<noteq> 0"
proof (cases "post_necessary_raw (dly - 1) \<tau> t sig e def ")
  case True
  then show ?thesis
    using assms unfolding trans_post_raw_def 
    by (metis fun_upd_apply option.distinct(1) post_raw_def zero_fun_def zero_option_def)
next
  case False
  hence *: "(\<exists>i\<ge>t. i \<le> t + (dly-1) \<and> \<tau> i sig = Some e \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> \<tau> j sig = None))"
    using post_necessary_raw_correctness[of "dly-1" "\<tau>" "t" "sig" "e" "def"] assms(2)
    by auto
  hence lookup: "\<tau>' =  preempt_raw sig \<tau> (t + dly)"
    using assms(1) False  by (simp add: trans_post_raw_def)
  obtain i where "t \<le> i" and "i \<le> t + (dly - 1)" and "\<tau> i sig = Some e"
    using * by auto
  hence "\<tau>' i sig = Some e"
    using lookup `0 < dly`  unfolding preempt_raw_def by auto
  thus ?thesis
    by (transfer', metis option.distinct(1) zero_fun_def zero_option_def)
qed

lemma trans_post_raw_diff_sig:
  assumes "s' \<noteq> s"
  shows "(to_trans_raw_sig (trans_post_raw s' v def \<tau> t dly) s) n = (to_trans_raw_sig \<tau> s) n"
  using assms unfolding to_trans_raw_sig_def trans_post_raw_def 
  by (auto simp add: post_raw_def preempt_raw_def)

lemma trans_post_less:
  assumes "n < t + dly"
  shows " (to_trans_raw_sig (trans_post_raw s' v def \<tau> t dly) s) n = (to_trans_raw_sig \<tau> s) n"
  using assms unfolding to_trans_raw_sig_def trans_post_raw_def 
  by (auto simp add: post_raw_def preempt_raw_def)

lemma inf_time_trans_post:
  assumes "s' \<noteq> s"
  shows "inf_time (to_trans_raw_sig (trans_post_raw s' v def \<tau> k dly)) s t = inf_time (to_trans_raw_sig \<tau>) s t"
proof -
  have "\<And>n.  (to_trans_raw_sig (trans_post_raw s' v def \<tau> k dly) s) n =  (to_trans_raw_sig \<tau> s) n"
    by (simp add: trans_post_raw_diff_sig assms)
  hence "keys (to_trans_raw_sig (trans_post_raw s' v def \<tau> k dly) s) = keys (to_trans_raw_sig \<tau> s)"
    by presburger
  thus ?thesis
    unfolding inf_time_def by auto
qed

lemma inf_time_trans_post_raw_less:
  assumes "t < k + dly"
  shows "inf_time (to_trans_raw_sig (trans_post_raw s' v def \<tau> k dly)) s t = inf_time (to_trans_raw_sig \<tau>) s t"
proof -
  have "\<And>n. n < k + dly \<Longrightarrow>  (to_trans_raw_sig (trans_post_raw s' v def \<tau> k dly) s) n =  (to_trans_raw_sig \<tau> s) n"
    by (simp add: trans_post_less)
  with inf_time_equal_when_same_trans_upto_strict [OF _ assms(1), of "trans_post_raw s' v def \<tau> k dly"]
  show ?thesis by auto
qed

lemma signal_of_trans_post:
  assumes "s' \<noteq> s"
  shows "signal_of def (trans_post_raw s' v def' \<tau> k dly) s t = signal_of def \<tau> s t"
  using inf_time_trans_post[OF assms] trans_post_raw_diff_sig[OF assms]
  unfolding to_signal_def comp_def by (simp add: option.case_eq_if)

lemma signal_of_trans_post2:
  assumes "t < k + dly"
  shows "signal_of def (trans_post_raw s' v def' \<tau> k dly) s t = signal_of def \<tau> s t"
  using inf_time_trans_post_raw_less[OF assms] trans_post_less[OF assms]
  unfolding to_signal_def comp_def
  by (smt assms case_optionE inf_time_at_most le_less_trans option.case_eq_if option.sel trans_post_less)

lemma signal_of_trans_post3:
  assumes "k + dly \<le> t"
  assumes "\<forall>i < k. \<tau> i = 0"
  assumes "0 < dly"
  shows "signal_of def (trans_post_raw s v def \<tau> k dly) s t = v"
proof -
  have "post_necessary_raw (dly-1) \<tau> k s v def \<or> \<not> post_necessary_raw (dly-1) \<tau> k s v def"
    by auto
  moreover
  { assume "post_necessary_raw (dly-1) \<tau> k s v def"
    have "inf_time (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly)) s t = Some (k + dly)"
    proof (rule inf_time_someI)
      show " k + dly \<in> dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s)"
        using `post_necessary_raw (dly-1) \<tau> k s v def`
        by (auto simp  add: to_trans_raw_sig_def trans_post_raw_def post_raw_def)
    next
      show "k + dly \<le> t" using assms by auto
    next
      { fix ta
        assume *: "ta \<in> dom  (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s)"
        assume "ta \<le> t"
        have "ta \<le> k + dly"
        proof (rule ccontr)
          assume "\<not> ta \<le> k + dly"
          hence "k + dly < ta" by auto
          hence "to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s ta = None"
            using \<open>post_necessary_raw (dly-1) \<tau> k s v def\<close>
            by (auto simp add: to_trans_raw_sig_def trans_post_raw_def post_raw_def)
          with * show "False" by auto
        qed }
      thus " \<forall>ta\<in>dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s). ta \<le> t \<longrightarrow> ta \<le> k + dly"
        by auto
    qed
    moreover have "to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s (k + dly) = Some v"
      using \<open>post_necessary_raw (dly-1) \<tau> k s v def\<close>
      by (auto simp add: to_trans_raw_sig_def trans_post_raw_def post_raw_def)
    ultimately have ?thesis
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume as_not: "\<not> post_necessary_raw (dly-1) \<tau> k s v def"
    then obtain t' where "k \<le> t' \<and> t' \<le> k + (dly-1) \<and>  \<tau> t' s = Some v \<and> (\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)
                       \<or> (\<forall>j\<ge>k. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None) \<and> v = def"
      using post_necessary_raw_correctness[of "dly-1" "\<tau>" "k" "s" "v" "def"] by auto
    moreover
    { assume "k \<le> t' \<and> t' \<le> k + (dly-1) \<and>  \<tau> t' s = Some v \<and> (\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)"
      hence "k \<le> t'" and "t' \<le> k + (dly-1)" and " \<tau> t' s = Some v" and "(\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)"
        by auto
      have "inf_time (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly)) s t = Some t'"
      proof (rule inf_time_someI)
        show "t' \<in> dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s)"
          using \<open>\<not> post_necessary_raw (dly-1) ( \<tau>) k s v def\<close> ` \<tau> t' s = Some v` `t' \<le> k + (dly-1)` `0 < dly`
          by (auto simp  add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def)
      next
        show "t' \<le> t"
          using `t' \<le> k + (dly-1)` `k + dly \<le> t` by auto
      next
        { fix ta
          assume *: "ta \<in> dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s)"
          assume "ta \<le> t"
          have "ta \<le> t'"
          proof (rule ccontr)
            assume "\<not> ta \<le> t'"
            hence "t' < ta" by auto
            hence " (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta = None"
              using \<open>\<not> post_necessary_raw (dly-1) ( \<tau>) k s v def\<close> `(\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)`
              unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def by auto
            
            with * show "False" by auto
          qed }
        thus "\<forall>ta\<in>dom  (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s). ta \<le> t \<longrightarrow> ta \<le> t'"
          by auto
      qed
      moreover have "to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s t' = Some v"
        using \<open>\<not> post_necessary_raw (dly-1) \<tau> k s v def\<close> `\<tau> t' s = Some v` `t' \<le> k + (dly-1)` `0 < dly`
        by (auto simp add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def)
      ultimately have ?thesis
        unfolding to_signal_def comp_def by auto }
    moreover
    { assume "(\<forall>j\<ge>k. j \<le> k + (dly-1) \<longrightarrow> \<tau> j s = None) \<and> v = def"
      have "\<forall>ta\<in>dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s). t < ta"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s). t < ta)"
        then obtain ta where "ta \<in> dom (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s)" and "ta \<le> t"
          using leI by blast
        hence "to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s ta \<noteq> 0"
          by (simp add: domIff zero_option_def)
        have "ta < k \<or> k \<le> ta \<and> ta \<le> k + dly \<or> k + dly < ta" by linarith
        moreover
        { assume "ta < k"
          have "to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s ta = 0"
            using assms(2)  
            by (metis \<open>ta < k\<close> add.commute trans_post_less to_trans_raw_sig_def trans_less_add2 zero_fun_def)
          with ` (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta \<noteq> 0` have "False" by auto }
        moreover
        { assume "k \<le> ta \<and> ta \<le> k + dly"
          hence " (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta = 0"
            using `(\<forall>j\<ge>k. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None) \<and> v = def` as_not
            by (auto simp add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def zero_option_def)
          with ` (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta \<noteq> 0` have "False" by auto }
        moreover
        { assume "k + dly < ta"
          hence " (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta = 0"
            using as_not  unfolding to_trans_raw_sig_def 
            by (auto simp add: preempt_raw_def trans_post_raw_def zero_option_def)
          with ` (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta \<noteq> 0` have "False" by auto }
        ultimately show "False"by auto
      qed
      hence "inf_time (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly)) s t = None"
        by (auto simp add: inf_time_none_iff)
      hence ?thesis
        unfolding to_signal_def comp_def using `(\<forall>j\<ge>k. j \<le> k + (dly-1) \<longrightarrow> \<tau> j s = None) \<and> v = def`
        by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis
    by auto
qed

fun check :: "('signal \<rightharpoonup> val) \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool" where
  "check \<sigma> sig val = (case \<sigma> sig of None \<Rightarrow> True | Some val' \<Rightarrow> val = val')"

fun is_stable_raw :: "nat \<Rightarrow> (nat \<Rightarrow> 'signal \<rightharpoonup> bool) \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool" where
  "is_stable_raw 0 _ _ _ _ \<longleftrightarrow> True"
| "is_stable_raw (Suc n) \<tau> now sig val \<longleftrightarrow>
                                     check (\<tau> (now + Suc n)) sig val \<and> is_stable_raw n \<tau> now sig val"

lemma is_stable_raw_correct_only_if:
  "is_stable_raw dly \<tau> now sig val \<Longrightarrow> \<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (\<tau> m) sig val"
proof (rule allI, rule impI, induction dly)
  case 0
  then show ?case by auto
next
  case (Suc dly)
  have "m = now + Suc dly \<or> m \<noteq> now + Suc dly"
    by auto
  moreover
  { assume "m = now + Suc dly"
    hence ?case using Suc(2) by auto }
  moreover
  { assume "m \<noteq> now + Suc dly"
    with Suc(3) have *: "now < m \<and> m \<le> now + dly"  by auto
    have "is_stable_raw dly \<tau> now sig val" using Suc(2) by auto
    with Suc(1) and * have ?case by auto }
  ultimately show ?case by auto
qed

lemma is_stable_raw_correct_if:
  assumes "\<And>m. now < m \<and> m \<le> now + dly \<Longrightarrow> check (\<tau> m) sig val"
  shows "is_stable_raw dly \<tau> now sig val"
  using assms
  by (induction dly) auto

lemma is_stable_raw_correct:
  "is_stable_raw dly \<tau> now sig val \<longleftrightarrow> (\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (\<tau> m) sig val)"
  using is_stable_raw_correct_if is_stable_raw_correct_only_if by metis

definition purge_raw :: "'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> 'signal trans_raw" where
  "purge_raw \<tau> t dly sig = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t <.. t + dly}"

lemma purge_raw_induct:
  "\<And>m. now + Suc n \<le> m \<Longrightarrow> purge_raw \<tau> now n sig m = \<tau> m"
  by (auto simp add :  purge_raw_def override_on_def)

lemma purge_raw_induct':
  "purge_raw \<tau> now n sig = \<tau>' \<Longrightarrow>  \<tau>' (now + Suc n) = \<tau> (now + Suc n)"
  using purge_raw_induct[of "now" "n" "now + Suc n" "\<tau>"] by auto

lemma purge_raw_correctness':
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> \<tau>' m sig = None"
  using assms unfolding override_on_def purge_raw_def by auto

lemma purge_raw_before_now_unchanged:
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "\<forall>m. m \<le> now \<longrightarrow> \<tau> m =  \<tau>' m"
  using assms unfolding purge_raw_def by auto

lemma purge_raw_after_delay_unchanged:
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "\<forall>m. now + n < m \<longrightarrow> \<tau> m = \<tau>' m"
  using assms unfolding purge_raw_def by auto

lemma purge_raw_does_not_affect_other_sig:
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "\<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  using assms by (auto simp add: purge_raw_def override_on_def)

lemma purge_raw_correctness:
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> check (\<tau>' m) sig val"
  using assms unfolding purge_raw_def by auto

lemma stable_after_purge2:
  assumes "purge_raw \<tau> now n sig = \<tau>'"
  shows "is_stable_raw n \<tau>' now sig val"
  using purge_raw_correctness is_stable_raw_correct assms by fastforce

text \<open>This is the function for posting a transaction in an inertial assignment statement.\<close>

definition inr_post_raw :: "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat 
                                                                             \<Rightarrow> 'signal trans_raw"
  where
  "inr_post_raw sig val cur_val \<tau> now dly =
   (if is_stable_raw dly \<tau> now sig cur_val then
      trans_post_raw sig val cur_val \<tau> now dly
    else
      trans_post_raw sig val cur_val (purge_raw \<tau> now dly sig) now dly)"

lemma inr_post_purged:
  assumes "(\<forall>s. s \<in> dom (\<tau> now) \<longrightarrow> \<sigma> s = the (\<tau> now s))"
  shows "\<And>n. now \<le> n \<Longrightarrow> n < now + dly \<Longrightarrow>
                                     (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig)
                                  \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
proof -
  fix n
  assume "now \<le> n" and "n < now + dly"
  have "is_stable_raw dly \<tau> now sig (\<sigma> sig) \<or> \<not> is_stable_raw dly \<tau> now sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable_raw dly \<tau> now sig (\<sigma> sig)"
    hence "(\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check ( \<tau> m) sig (\<sigma> sig))"
      using is_stable_raw_correct by metis
    hence "\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> (case  \<tau> m sig of None \<Rightarrow> True | Some val' \<Rightarrow> \<sigma> sig = val')"
      by auto
    hence "\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow>  \<tau> m sig = None \<or>  \<tau> m sig = Some (\<sigma> sig)"
      using option.inject by fastforce
    hence disj: " \<tau> n sig = None \<or>  \<tau> n sig = Some (\<sigma> sig)"
      using `now \<le> n` `n < now + dly` using assms by (smt domIff le_eq_less_or_eq option.exhaust_sel)
    have "inr_post_raw sig val (\<sigma> sig) \<tau> now dly = trans_post_raw sig val (\<sigma> sig) \<tau> now dly" (is "?inr = ?trans")
      using `is_stable_raw dly \<tau> now sig (\<sigma> sig)` unfolding inr_post_raw_def by auto
    hence " ?inr n sig =  ?trans n sig"
      by auto
    also have "... =  \<tau> n sig"
      using `n < now + dly`  unfolding trans_post_raw_def post_raw_def preempt_raw_def by auto
    finally have " ?inr n sig =  \<tau> n sig"
      by auto
    hence " ?inr n sig = None \<or>  ?inr n sig = Some (\<sigma> sig)"
      using disj by auto }
  moreover
  { assume "\<not> is_stable_raw dly \<tau> now sig (\<sigma> sig)"
    hence "inr_post_raw sig val (\<sigma> sig) \<tau> now dly = trans_post_raw sig val (\<sigma> sig) (purge_raw \<tau> now dly sig) now dly"
      (is "?inr = ?trans") unfolding inr_post_raw_def by auto
    hence " ?inr n sig =  ?trans n sig"
      by auto
    also have "... =  (purge_raw \<tau> now dly sig) n sig" (is "_ =  ?purge_raw n sig")
      using `n < now + dly`  unfolding trans_post_raw_def post_raw_def preempt_raw_def by auto
    finally have " ?inr n sig =  ?purge_raw n sig"
      by auto
    moreover have " ?purge_raw n sig = None \<or>  ?purge_raw n sig = Some (\<sigma> sig)"
      using purge_raw_correctness'[where \<tau>'="?purge_raw"] `now \<le> n` `n < now + dly` assms
    proof -
      have f1: "\<forall>z b. ((Some b = z \<or> z = None) \<or> \<not> the z) \<or> \<not> b"
        by force
      moreover
      { assume "\<tau> now sig \<noteq> Some (now \<le> now)"
      moreover
      { assume "(Some (now \<le> n) \<noteq> purge_raw \<tau> now dly sig n sig \<and> Some (now \<le> n) \<noteq> \<tau> now sig) \<and> \<tau> now sig \<noteq> None"
      moreover
      { assume "(\<not> the (purge_raw \<tau> now dly sig n sig) \<and> \<not> the (\<tau> now sig)) \<and> sig \<in> dom (\<tau> now)"
        then have "(purge_raw \<tau> now dly sig n sig = None \<or> purge_raw \<tau> now dly sig n sig = Some (\<sigma> sig)) \<or> (\<exists>b. (\<not> \<sigma> sig \<and> \<not> b) \<and> Some b = purge_raw \<tau> now dly sig n sig)"
          by (metis (no_types) \<open>\<forall>s. s \<in> dom (\<tau> now) \<longrightarrow> \<sigma> s = the (\<tau> now s)\<close> option.exhaust_sel)
        then have ?thesis by fastforce }
        ultimately have ?thesis
          using f1 by (metis \<open>now \<le> n\<close> domIff) }
        ultimately have "n = now \<longrightarrow> (\<exists>a n f. purge_raw f now n (a::'a) now \<noteq> f now) \<or> \<tau> now sig = None \<or> purge_raw \<tau> now dly sig n sig = None \<or> purge_raw \<tau> now dly sig n sig = Some (\<sigma> sig)"
          by force }
      ultimately show ?thesis
        by (metis \<open>\<forall>s. s \<in> dom (\<tau> now) \<longrightarrow> \<sigma> s = the (\<tau> now s)\<close> \<open>n < now + dly\<close> \<open>now \<le> n\<close> domIff option.exhaust_sel option.simps(1) order.strict_iff_order purge_raw_before_now_unchanged purge_raw_correctness')
    qed
    ultimately have " ?inr n sig = None \<or>  ?inr n sig = Some (\<sigma> sig)"
      by auto }
  ultimately show " (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig) \<or>
                    (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
    by linarith
qed

lemma inr_post_purged': 
  assumes "\<tau> now = 0"
  shows "\<And>n. now \<le> n \<Longrightarrow> n < now + dly \<Longrightarrow>
                                     (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig)
                                  \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
proof -
  have "(\<forall>s. s \<in> dom (\<tau> now) \<longrightarrow> \<sigma> s = the (\<tau> now s))"
    using assms by (auto simp add: zero_fun_def zero_option_def)
  thus "\<And>n. now \<le> n \<Longrightarrow> n < now + dly \<Longrightarrow>
                                     (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig)
                                  \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
    using inr_post_purged by metis
qed

lemma signal_of_inr_post:
  assumes "now + dly \<le> t"
  assumes "\<forall>i < now. \<tau> i = 0"
  assumes "0 < dly"
  shows "signal_of c (inr_post_raw s v c \<tau> now dly) s t = v"
proof (cases "is_stable_raw dly \<tau> now s c")
  case True
  have "post_necessary_raw (dly-1) ( \<tau>) now s v c \<or> \<not> post_necessary_raw (dly-1) ( \<tau>) now s v c"
    by auto
  moreover
  { assume "post_necessary_raw (dly-1) ( \<tau>) now s v c"
    have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some (now + dly)"
    proof (rule inf_time_someI)
      show " now + dly \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
        using True `post_necessary_raw (dly-1) ( \<tau>) now s v c`
        unfolding inr_post_raw_def  unfolding trans_post_raw_def post_raw_def to_trans_raw_sig_def
        by auto
    next
      show "now + dly \<le> t" using assms by auto
    next
      { fix ta
        assume *: "ta \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
        assume "ta \<le> t"
        have "ta \<le> now + dly"
        proof (rule ccontr)
          assume "\<not> ta \<le> now + dly"
          hence "now + dly < ta" by auto
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = None"
            unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def
            post_raw_def preempt_raw_def by auto
          with * show "False" by auto
        qed }
      thus " \<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> now + dly"
        by auto
    qed
    moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) (now + dly) = Some v"
      using True `post_necessary_raw (dly-1) ( \<tau>) now s v c`
      unfolding inr_post_raw_def  unfolding to_trans_raw_sig_def trans_post_raw_def post_raw_def 
      by auto
    ultimately have ?thesis
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) ( \<tau>) now s v c"
    then obtain i where "now \<le> i \<and> i \<le> now + (dly-1) \<and>  \<tau> i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  \<tau> j s = None) \<or>
                        (\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  \<tau> i s = None) \<and> v = c"
      using post_necessary_raw_correctness[of "dly-1" " \<tau>" "now" "s" "v" "c"] by metis
    moreover
    { assume "now \<le> i \<and> i \<le> now + (dly-1) \<and>  \<tau> i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  \<tau> j s = None)"
      hence "now \<le> i" and "i \<le> now + (dly-1)" and " \<tau> i s = Some v" and **: "(\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  \<tau> j s = None)"
        by auto
      have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some i"
      proof (rule inf_time_someI)
        show "i \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          using True ` \<tau> i s = Some v` `\<not> post_necessary_raw (dly-1) ( \<tau>) now s v c` `i \<le> now + (dly-1)` `0 < dly`
          unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def
          by auto
      next
        show "i \<le> t"
          using `i  \<le> now + (dly-1)` assms by auto
      next
        { fix ta
          assume *: "ta \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          assume "ta \<le> t"
          have "ta \<le> i"
          proof (rule ccontr)
            assume "\<not> ta \<le> i"
            hence "i < ta" by auto
            hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = None"
              using True `\<not> post_necessary_raw (dly-1) ( \<tau>) now s v c` **
              unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              preempt_raw_def by auto
            with * show "False" by auto
          qed }
        thus "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> i"
          by auto
      qed
      moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) i = Some v"
        using True `\<not> post_necessary_raw (dly-1) ( \<tau>) now s v c` ` \<tau> i s = Some v` `i \<le> now + (dly-1)` `0 < dly`
        unfolding inr_post_raw_def  unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def
        by auto
      ultimately have ?thesis
        unfolding to_signal_def comp_def by auto }
    moreover
    { assume "(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  \<tau> i s = None) \<and> v = c"
      have " \<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta)"
        then obtain ta where "ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          and "ta \<le> t" using leI by blast
        hence absurd: " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta \<noteq> 0"
          by (simp add: domIff zero_option_def)
        have "ta < now \<or> now \<le> ta \<and> ta \<le> now + dly \<or> now + dly < ta"
          by auto
        moreover
        { assume "ta < now"
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = 0"
            by (metis True add_diff_cancel_left' assms(2) assms(3) inr_post_raw_def le_less_trans
            order.strict_iff_order to_trans_raw_sig_def trans_post_less zero_fun_def zero_less_diff)
          hence "False"
            using absurd by auto }
        moreover
        { assume "now \<le> ta \<and> ta \<le> now + dly"
          hence "inr_post_raw s v c \<tau> now dly = trans_post_raw s v c \<tau> now dly"
            using True unfolding inr_post_raw_def by auto
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta =
                  (to_trans_raw_sig (trans_post_raw s v c \<tau> now dly) s) ta"
            by auto
          also have "... = 0"
            using not_nec `now \<le> ta \<and> ta \<le> now + dly` `(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  \<tau> i s = None) \<and> v = c`
            by ( auto simp add :to_trans_raw_sig_def trans_post_raw_def preempt_raw_def zero_option_def)
          finally have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = 0"
            by auto
          with absurd have False by auto }
        moreover
        { assume "now + dly < ta"
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = 0"
            using True not_nec unfolding inr_post_raw_def
            by ( auto simp add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def zero_option_def)
          with absurd have False by auto }
        ultimately show False by auto
      qed
      hence "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = None"
        by (simp add: inf_time_none_iff) 
      hence ?thesis
        by (simp add: \<open>(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow> \<tau> i s = None) \<and> v = c\<close> to_signal_def) }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
next
  case False
  let ?\<tau>' = "purge_raw \<tau> now dly s"
  have "post_necessary_raw (dly - 1) ( ?\<tau>') now s v c \<or> \<not> post_necessary_raw (dly - 1) ( ?\<tau>') now s v c"
    by auto
  moreover
  { assume "post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some (now + dly)"
    proof (rule inf_time_someI)
      show " now + dly \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
        using False `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
        unfolding inr_post_raw_def  unfolding trans_post_raw_def post_raw_def to_trans_raw_sig_def
        by auto
    next
      show "now + dly \<le> t" using assms by auto
    next
      { fix ta
        assume *: "ta \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
        assume "ta \<le> t"
        have "ta \<le> now + dly"
        proof (rule ccontr)
          assume "\<not> ta \<le> now + dly"
          hence "now + dly < ta" by auto
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = None"
            unfolding inr_post_raw_def  unfolding trans_post_raw_def post_raw_def to_trans_raw_sig_def
            preempt_raw_def by auto
          with * show "False" by auto
        qed }
      thus " \<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> now + dly"
        by auto
    qed
    moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) (now + dly) = Some v"
      using False `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
      unfolding inr_post_raw_def  unfolding to_trans_raw_sig_def post_raw_def trans_post_raw_def 
      by auto
    ultimately have ?thesis
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    then obtain i where "now \<le> i \<and> i \<le> now + (dly-1) \<and>  (purge_raw \<tau> now dly s) i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s) j s = None) \<or>
                        (\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s) i s = None) \<and> v = c"
      using post_necessary_raw_correctness[of "dly-1" "(purge_raw \<tau> now dly s)" "now" "s" "v" "c"]
      by metis
    moreover
    { assume "now \<le> i \<and> i \<le> now + (dly-1) \<and>  ?\<tau>' i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None)"
      hence "now \<le> i" and "i \<le> now + (dly-1)" and " ?\<tau>' i s = Some v" and **: "\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None"
        by auto
      have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some i"
      proof (rule inf_time_someI)
        show "i \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          using False ` ?\<tau>' i s = Some v` not_nec `i \<le> now + (dly-1)` `0 < dly`
          unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def
          by auto
      next
        show "i \<le> t"
          using `i  \<le> now + (dly-1)` assms by auto
      next
        { fix ta
          assume *: "ta \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          assume "ta \<le> t"
          have "ta \<le> i"
          proof (rule ccontr)
            assume "\<not> ta \<le> i"
            hence "i < ta" by auto
            hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = None"
              using False `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` **
              unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              preempt_raw_def by auto
            with * show "False" by auto
          qed }
        thus "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> i"
          by auto
      qed
      moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) i = Some v"
        using False `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` ` ?\<tau>' i s = Some v` `i \<le> now + (dly-1)` `0 < dly`
        unfolding inr_post_raw_def  unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def
        by auto
      ultimately have ?thesis
        unfolding to_signal_def comp_def by auto }
    moreover
    { assume "(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s) i s = None) \<and> v = c"
      have "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta)"
        then obtain ta where "t \<ge> ta" and "ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          using leI by auto
        hence "( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)) ta \<noteq> 0"
          by (metis domD option.distinct(1) zero_option_def)
        moreover have "inr_post_raw s v c \<tau> now dly = trans_post_raw s v c (purge_raw \<tau> now dly s) now dly"
          using False unfolding inr_post_raw_def by auto
        ultimately have absurd: " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta \<noteq> 0"
          by auto
        have "ta < now \<or> now \<le> ta \<and> ta \<le> now + dly \<or> now + dly < ta"
          by auto
        moreover
        { assume "ta < now"
          hence " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta = 0"
            using assms(2) not_nec purge_raw_before_now_unchanged[of "\<tau>" "now" "dly" "s"]
            unfolding to_trans_raw_sig_def preempt_raw_def
            by (metis add_le_same_cancel1 assms(3) leI le_less_trans nat_less_le to_trans_raw_sig_def
            trans_post_less zero_fun_def)          
          with absurd have False by auto }
        moreover
        { assume "now \<le> ta \<and> ta \<le> now + dly"
          hence " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta = 0"
            using not_nec `(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s) i s = None) \<and> v = c`
            by ( auto simp add: zero_option_def to_trans_raw_sig_def trans_post_raw_def preempt_raw_def)
          with absurd have False by auto }
        moreover
        { assume "now + dly < ta"
          hence " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta = 0"
            using not_nec 
            by (auto simp add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def zero_option_def)
          with absurd have False by auto }
        ultimately show False by auto
      qed
      hence "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = None"
        by (auto simp add: inf_time_none_iff)
      hence ?thesis
        unfolding to_signal_def comp_def using `(\<forall>i\<ge>now. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s) i s = None) \<and> v = c`
        by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

fun b_seq_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                                         'signal seq_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw"
  where
  "b_seq_exec t \<sigma> \<gamma> \<theta> Bnull \<tau> = \<tau>"

| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau> =
                                    (let \<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau> in b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>')"

| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded guard ss1 ss2) \<tau> =
                (if beval_raw t \<sigma> \<gamma> \<theta> guard then b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau> else b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>)"

\<comment> \<open>we are making an assumption here: that the default value of @{term "\<tau>"} is @{term "\<sigma> sig"}\<close>
| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_trans sig e dly) \<tau> =
                                 (let x = (beval_raw t \<sigma> \<gamma> \<theta> e) in trans_post_raw sig x (\<sigma> sig) \<tau> t dly)"

| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau> =
                                   (let x = (beval_raw t \<sigma> \<gamma> \<theta> e) in inr_post_raw sig x (\<sigma> sig) \<tau> t dly)"

abbreviation b_seq_exec_abb :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                               'signal seq_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
    ("_ , _ , _ , _ \<turnstile> <_ , _> \<longrightarrow>\<^sub>s _") where
  "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>') \<equiv> (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>')"

definition
  "map_diff m1 m2 = (\<lambda>x. if m1 x = m2 x \<and> m1 x \<noteq> None then None else m1 x)"

lemma [simp]:
  "map_diff m1 Map.empty = m1"
  "map_diff Map.empty m1 = Map.empty"
  "map_diff m m = Map.empty"
  by (auto simp add:map_diff_def)

lemma map_diff_fin_variability:
  fixes f1 f2
  assumes "\<forall>\<^sub>\<infinity>n. f1 n = 0" and "\<forall>\<^sub>\<infinity>n. f2 n = 0"
  shows "\<forall>\<^sub>\<infinity>n. map_diff (f1 n) (f2 n) = 0"
  using assms eventually_elim2[where F="cofinite" and P="\<lambda>x. f1 x = 0" and Q="\<lambda>x. f2 x = 0"
                                                  and R="\<lambda>x. map_diff (f1 x) (f2 x) = 0"]
  by (simp add: zero_fun_def zero_option_def)

lemma map_add_fin_variability:
  fixes f1 f2
  assumes "\<forall>\<^sub>\<infinity>n. f1 n = 0" and "\<forall>\<^sub>\<infinity>n. f2 n = 0"
  shows "\<forall>\<^sub>\<infinity>n. map_add (f1 n) (f2 n) = 0"
  using assms eventually_elim2[where F="cofinite" and P="\<lambda>x. f1 x = 0" and Q="\<lambda>x. f2 x = 0"
                                                  and R="\<lambda>x. (f1 x) ++ (f2 x) = 0"]
  by (simp add: map_add_subsumed2)

abbreviation
  "map_diff_trans_raw \<tau>1 \<tau>2 \<equiv> (\<lambda>n. map_diff (\<tau>1 n) (\<tau>2 n))"

lemma
  "\<not>(\<exists> a val. (map_diff m1 m2) a = Some val \<and> m2 a = Some val)"
  by (metis map_diff_def option.simps(3))

lemma
  "\<forall> a val. m1 a = Some val \<and> m2 a = Some val  \<longrightarrow> (map_diff m1 m2) a = None"
  "\<forall> a val. m1 a = Some val \<and> m2 a = None      \<longrightarrow> (map_diff m1 m2) a = Some val"
  "\<forall> a val. m1 a = None     \<and> m2 a = Some val  \<longrightarrow> (map_diff m1 m2) a = None"
  "\<forall>a. m1 a = None \<and> m2 a = None \<longrightarrow> (map_diff m1 m2) a = None"
  by (auto simp add: map_diff_def)

lemma
  "\<forall>a val1 val2. m1 a = Some val1 \<and> m2 a = Some val2 \<and> val1 \<noteq> val2 \<longrightarrow>
                                                                      (map_diff m1 m2) a = Some val1"
  by (rule allI)+(rule impI, simp add:map_diff_def)

lemma mem_dom_map_diff_obtains:
  assumes "x \<in> dom (map_diff m1 m2)"
  assumes "m2 x \<noteq> None"
  obtains v1 and v2 where "v1 \<noteq> v2" and "m1 x = Some v1" and "m2 x = Some v2"
  by (metis assms domD domIff map_diff_def)

lemma dom_map_diff_subseteq:
  "dom (map_diff m3 m1) \<subseteq> dom (map_diff m3 m2) \<union> dom (map_diff m2 m1)"
  by (smt UnCI domIff map_diff_def subsetI)

lemma dom_map_diff_trans_post_raw:
  "dom (map_diff_trans_raw (post_raw sig x \<tau> (t + dly)) \<tau> n) \<subseteq> {sig}"
  by (smt domIff fun_upd_apply insertCI map_diff_def subsetI post_raw_def)

lemma dom_map_diff_preempt_raw:
  "dom (map_diff_trans_raw (preempt_raw sig \<tau> (t + dly)) \<tau> n) \<subseteq> {sig}"
  unfolding preempt_raw_def by (smt domIff fun_upd_other insertCI map_diff_def subsetI)

lemma dom_map_diff_trans_post:
  "dom (map_diff_trans_raw (trans_post_raw sig x def \<tau> t dly) \<tau> n)  \<subseteq> {sig}"
  by (simp add: dom_map_diff_preempt_raw dom_map_diff_trans_post_raw trans_post_raw_def)

lemma dom_map_diff_purge:
  "\<And>n. dom (map_diff_trans_raw (purge_raw \<tau> t dly sig) \<tau> n) \<subseteq> {sig}"
  by (smt domIff insertCI map_diff_def purge_raw_does_not_affect_other_sig subsetI)

lemma dom_map_diff_inr_post:
  fixes sig x cur_val \<tau> t dly n
  defines "\<tau>' \<equiv> inr_post_raw sig x cur_val \<tau> t dly"
  shows "dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> {sig}"
  by (metis Un_empty_right assms dom_map_diff_purge dom_map_diff_subseteq dom_map_diff_trans_post
  inr_post_raw_def subset_Un_eq subset_singleton_iff)

lemma seq_stmts_modify_local_only_raw:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
  shows "\<And>n. dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> set (signals_in ss)"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  define \<tau>'' where "\<tau>'' \<equiv> b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence *: "b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def by auto
  have **: "\<And>n. dom (map_diff (\<tau>'' n) (\<tau> n)) \<subseteq> signals_of ss1"
    using Bcomp(1)[of "\<tau>" "\<tau>''"] unfolding \<tau>''_def by auto 
  have ***: "\<And>n. dom (map_diff ( \<tau>' n) ( \<tau>'' n)) \<subseteq> signals_of ss2"
    using Bcomp(2)[of "\<tau>''" "\<tau>'"] *  Bcomp(3) by auto
  have "dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> dom (map_diff (\<tau>' n) (\<tau>'' n)) \<union> dom (map_diff (\<tau>'' n) (\<tau> n))"
    using dom_map_diff_subseteq by metis
  also have "... \<subseteq> signals_of ss2 \<union> dom (map_diff ( \<tau>'' n) ( \<tau> n))"
    using ***[of "n"]  by(auto intro: Un_mono)
  also have "... \<subseteq> signals_of ss2 \<union> signals_of ss1"
    using **[of "n"] by (auto intro:Un_mono)
  finally show ?case by auto
next
  case (Bguarded x1 ss1 ss2)
  have "beval_raw t \<sigma> \<gamma> \<theta> x1 = True \<or> beval_raw t \<sigma> \<gamma> \<theta> x1 = False" (is "?true \<or> ?false")
    by auto
  moreover
  { assume "?true"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded x1 ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
      by auto
    hence "... = \<tau>'"
      using Bguarded(3) by auto
    hence "dom (map_diff ( \<tau>' n) ( \<tau> n)) \<subseteq> signals_of ss1"
      using Bguarded(1) by auto
    hence ?case
      by auto }
  moreover
  { assume "?false"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded x1 ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>"
      by auto
    hence "... = \<tau>'" using Bguarded by auto
    hence "dom (map_diff ( \<tau>' n) ( \<tau> n)) \<subseteq> signals_of ss2" using Bguarded
      by auto
    hence ?case by auto }
  ultimately show ?case by auto
next
  case (Bassign_trans sig e dly)
  define x where "x = (beval_raw t \<sigma> \<gamma> \<theta> e)"
  hence "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
    using Bassign_trans by auto
  with dom_map_diff_trans_post_raw show ?case
    by (simp add: dom_map_diff_trans_post)
next
  case (Bassign_inert sig e dly)
  define x where "x = (beval_raw t \<sigma> \<gamma> \<theta> e)"
  hence "\<tau>' = inr_post_raw sig x (\<sigma> sig) \<tau> t dly"
    using Bassign_inert by auto
  then show ?case
    by (simp add: dom_map_diff_inr_post)
next
  case Bnull
  then show ?case by auto
qed  

text \<open>An important theorem: the semantics of sequential statements only modifies local variables.\<close>

theorem seq_stmts_modify_local_only:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
  shows "\<And>n. dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> set (signals_in ss)"
  using seq_stmts_modify_local_only_raw[OF assms] by auto

fun contain_null :: "'signal seq_stmt \<Rightarrow> bool" where
  "contain_null Bnull = True"
| "contain_null (Bassign_inert s expr n) = False"
| "contain_null (Bassign_trans s expr n) = False"
| "contain_null (Bguarded guard ss1 ss2) \<longleftrightarrow> contain_null ss1 \<or> contain_null ss2"
| "contain_null (Bcomp ss1 ss2) \<longleftrightarrow> contain_null ss1 \<or> contain_null ss2"

lemma post_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (post_raw sig x \<tau> (t + dly)) n = 0"
  using assms  by (auto simp add: post_raw_def)

lemma preempt_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (preempt_raw sig \<tau> t) n = 0"
  using assms  by (auto simp add: preempt_raw_def)

lemma trans_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (trans_post_raw sig x def \<tau> t dly) n = 0"
  using assms  by (auto simp add: preempt_raw_def trans_post_raw_def post_raw_def)

lemma purge_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (purge_raw \<tau> t dly sig) n = 0"
  using assms by (auto simp add: purge_raw_def)

lemma inr_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (inr_post_raw sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw_def 
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal)

lemma inr_post_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (inr_post_raw sig x c \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal)

lemma signal_of_inr_post2:
  assumes "now \<le> t" and "t < now + dly"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  shows "signal_of (\<sigma> s) (inr_post_raw s v (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)"
  using assms 
proof (cases "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = None")
  case True
  then show ?thesis  unfolding to_signal_def comp_def by auto
next
  case False
  then obtain t' where inf: "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = Some t'"
    by auto
  hence "t' \<le> t" and "t' < now + dly"
    using assms(2) by (auto dest!: inf_time_at_most)
  have *: "\<And>n. n < now \<Longrightarrow>  \<tau> n = 0"
    using assms(3) by auto
  have **: "\<And>n. n < now \<Longrightarrow>  (inr_post_raw s v (\<sigma> s) \<tau> now dly) n = 0"
    using inr_post_preserve_trans_removal'[OF *] by auto
  have "now \<le> t'"
  proof (rule ccontr)
    assume "\<not> now \<le> t'" hence "t' < now" by auto
    with assms(2) have " (inr_post_raw s v (\<sigma> s) \<tau> now dly) t' = 0"
      using ** by auto
    have "t' \<in> dom ( (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s))"
      using inf_time_some_exists[OF inf] unfolding dom_is_keys by auto
    hence " (inr_post_raw s v (\<sigma> s) \<tau> now dly) t' \<noteq> 0"
      unfolding inr_post_raw_def to_trans_raw_sig_def trans_post_raw_def
      by (metis domIff zero_fun_def zero_option_def)
    with ` (inr_post_raw s v (\<sigma> s) \<tau> now dly) t' = 0` show False by auto
  qed
  have ***: "t' \<in> dom ( (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s))"
    using inf_time_some_exists[OF inf] unfolding dom_is_keys by auto
  have asm4: "\<tau> now = 0"
    using assms(3) by (auto simp add: zero_fun_def zero_option_def)
  from inr_post_purged'[of "\<tau>", OF asm4 `now \<le> t'` `t' < now + dly`]
  have "the ( (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s) t') = (\<sigma> s)"
    using *** by (metis domIff option.sel to_trans_raw_sig_def)
  with inf show ?thesis unfolding to_signal_def comp_def by auto
qed

lemma b_seq_exec_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) n = 0"
  using assms
  by (induction ss arbitrary: \<tau>)
     (auto simp add: trans_post_preserve_trans_removal inr_post_preserve_trans_removal)

lemma b_seq_exec_modifies_local:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_in ss) \<Longrightarrow> i \<ge> t  \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  have "s \<notin> set (signals_in ss1)" and "s \<notin> set (signals_in ss2)"
    using Bcomp(3) by auto
  thus ?case
    by (metis Bcomp b_seq_exec.simps(2))
next
  case (Bguarded x1 ss1 ss2)
  have "s \<notin> set (signals_in ss1)" and "s \<notin> set (signals_in ss2)"
    using Bguarded by auto
  thus ?case
    by (metis (no_types) Bguarded b_seq_exec.simps(3))
next
  case (Bassign_trans x1 x2 x3)
  hence "s \<noteq> x1" by auto
  have "trans_post_raw x1 (beval_raw t \<sigma> \<gamma> \<theta> x2) (\<sigma> x1) \<tau> t x3 = \<tau>'"
    using Bassign_trans by auto
  thus ?case using `s \<noteq> x1`
    by (metis to_trans_raw_sig_def trans_post_raw_diff_sig)
next
  case (Bassign_inert sig e dly)
  hence "s \<noteq> sig" by auto
  have inr_post: "inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly = \<tau>'"
    using Bassign_inert by auto
  have "is_stable_raw dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
      using inr_post unfolding inr_post_raw_def by auto
    hence ?case
      using `s \<noteq> sig` by (metis to_trans_raw_sig_def trans_post_raw_diff_sig) }
  moreover
  { assume "\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly"
      using inr_post unfolding inr_post_raw_def by auto
    hence ?case using `s \<noteq> sig`
      using purge_raw_does_not_affect_other_sig[of "\<tau>" "t" "dly" "sig" "purge_raw \<tau> t dly sig"]
      by (metis to_trans_raw_sig_def trans_post_raw_diff_sig) }
  ultimately show ?case
    by auto
next
  case Bnull
  then show ?case by auto
qed

lemma b_seq_exec_modifies_local_before_now:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_in ss) \<Longrightarrow> i < t  \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  define \<tau>'' where "\<tau>'' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence " \<tau> i s =  \<tau>'' i s"
    using Bcomp(1) Bcomp(3-4)  by (metis Un_iff set_append set_remdups signals_in.simps(5))
  have "b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def by auto
  hence " \<tau>'' i s =  \<tau>' i s"
    using Bcomp(2-5) by (metis Un_iff set_append set_remdups signals_in.simps(5))
  thus ?case
    using ` \<tau> i s =  \<tau>'' i s` by auto
next
  case (Bguarded x1 ss1 ss2)
  then show ?case
    by (metis (no_types, lifting) Un_iff b_seq_exec.simps(3) set_append set_remdups signals_in.simps(4))
next
  case (Bassign_trans sig e dly)
  hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
    by auto
  then show ?case
    using `i < t`   by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
next
  case (Bassign_inert sig e dly)
  hence "s \<noteq> sig" by auto
  have inr_post_raw: "inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly = \<tau>'"
    using Bassign_inert by auto
  have "is_stable_raw dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
      using inr_post_raw unfolding inr_post_raw_def by auto
    hence ?case
      using `s \<noteq> sig` by (metis to_trans_raw_sig_def trans_post_raw_diff_sig) }
  moreover
  { assume "\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly"
      using inr_post_raw unfolding inr_post_raw_def by auto
    hence ?case using `s \<noteq> sig`
      using purge_raw_does_not_affect_other_sig[of "\<tau>" "t" "dly" "sig" "purge_raw \<tau> t dly sig"]
      by (metis to_trans_raw_sig_def trans_post_raw_diff_sig) }
  ultimately show ?case
    by auto
next
  case Bnull
  then show ?case by auto
qed

lemma b_seq_exec_modifies_local':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_in ss) \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms
  by (metis b_seq_exec_modifies_local b_seq_exec_preserve_trans_removal not_le)

lemma b_seq_exec_modifies_local_strongest:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_in ss) \<Longrightarrow> \<tau> i s = \<tau>' i s"
  by (metis assms b_seq_exec_modifies_local b_seq_exec_modifies_local_before_now not_le)

subsection \<open>Semantics of @{typ "'signal conc_stmt"}\<close>

text \<open>The semantics for the concurrent statement is very simple: execute each process independently
and then merge its result. To merge the results of all of the processes, the following function
@{term "clean_zip"} is used. Search for @{term "b_conc_exec"} for the semantics of concurrent
statements. \<close>

definition clean_zip_raw :: "'signal trans_raw \<Rightarrow> 'signal trans_raw \<times> 'signal set \<Rightarrow>
                                                   'signal trans_raw \<times> 'signal set \<Rightarrow>
                                                                                  'signal trans_raw"
  where
  "clean_zip_raw \<tau> \<tau>s1 \<tau>s2 = (let (\<tau>1, s1) = \<tau>s1; (\<tau>2, s2) = \<tau>s2
                              in (\<lambda>t s. if s \<in> s1 then \<tau>1 t s else if s \<in> s2 then \<tau>2 t s else \<tau> t s))"

lemma dom_map_diff_clean_zip_union:
  "\<And>n. dom (map_diff_trans_raw (clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'')) \<tau> n) \<subseteq>
                                  dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
proof
  fix n x
  assume asm: "x \<in> dom (map_diff_trans_raw (clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'')) \<tau> n)"
  have "\<tau> n x = None \<or> \<tau> n x \<noteq> None"
    by auto
  moreover
  { assume "\<tau> n x \<noteq> None"
    then obtain v1 v2  where czr: "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = Some v1" and "\<tau> n x = Some v2"
      and "v1 \<noteq> v2" using mem_dom_map_diff_obtains
      using \<open>x \<in> dom (map_diff_trans_raw (clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'')) \<tau> n)\<close> by fastforce
    have "x \<in> s' \<or> x \<notin> s' \<and> x \<in> s'' \<or> x \<notin> s' \<and> x \<notin> s''"
      by auto
    moreover
    { assume "x \<in> s'"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau>' n x"
        unfolding clean_zip_raw_def by auto
      hence "\<tau>' n x = Some v1"
        using czr by auto
      with `\<tau> n x \<noteq> None` have "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n)"
        using mem_dom_map_diff_obtains  by (simp add: \<open>\<tau> n x = Some v2\<close> \<open>v1 \<noteq> v2\<close> domIff map_diff_def)
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    moreover
    { assume "x \<notin> s' \<and> x \<in> s''"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau>'' n x"
        unfolding clean_zip_raw_def by auto
      hence "\<tau>'' n x = Some v1"
        using czr by auto
      with `\<tau> n x \<noteq> None` have "x \<in> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by (simp add: \<open>\<tau> n x = Some v2\<close> \<open>v1 \<noteq> v2\<close> domIff map_diff_def)
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    moreover
    { assume "x \<notin> s' \<and> x \<notin> s''"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau> n x"
        unfolding clean_zip_raw_def by auto
      hence False
        using czr `v1 \<noteq> v2` `\<tau> n x = Some v2` by auto
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    ultimately have "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
      by auto }
  moreover
  { assume "\<tau> n x = None"
    hence xdom: "x \<in> dom (clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n)"
      using asm by (metis domIff map_diff_def)
    have "x \<in> s' \<or> x \<notin> s' \<and> x \<in> s'' \<or> x \<notin> s' \<and> x \<notin> s''"
      by auto
    moreover
    { assume "x \<in> s'"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau>' n x"
        unfolding clean_zip_raw_def by auto
      with xdom have "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n)"
        using `\<tau> n x = None`  by (simp add: domIff map_diff_def)
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    moreover
    { assume "x \<notin> s' \<and> x \<in> s''"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau>'' n x"
        unfolding clean_zip_raw_def by auto
      with xdom have "x \<in> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        using `\<tau> n x = None`  by (simp add: domIff map_diff_def)
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    moreover
    { assume "x \<notin> s' \<and> x \<notin> s''"
      hence "clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'') n x = \<tau> n x"
        unfolding clean_zip_raw_def by auto
      with xdom have False
        by (simp add: \<open>\<tau> n x = None\<close> domIff)
      hence "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
        by auto }
    ultimately have "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
      by auto }
  ultimately show "x \<in> dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
    by auto
qed

lemma clean_zip_same:
  "clean_zip_raw \<tau> (\<tau>, s1) (\<tau>, s2) = \<tau>"
  unfolding clean_zip_raw_def Let_def by (auto split:prod.splits) presburger

lemma van_tassel_second_prop':
  assumes "disjnt s1 s2"
  shows "clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2) = clean_zip_raw \<tau> (\<tau>2, s2) (\<tau>1, s1)"
  using assms unfolding clean_zip_raw_def Let_def
  by (intro ext, auto split:prod.splits simp add: disjnt_def)

text \<open>Note that in the following semantics, if the process is not activated --- meaning the
sensitivity list does not contain recently changed signals --- then the returned transaction is
the original transaction.\<close>

fun b_conc_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw"
  where
    "b_conc_exec t \<sigma> \<gamma> \<theta> (process sl : ss) \<tau> = (if disjnt sl \<gamma> then \<tau> else b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>)"
  | "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =
           (let \<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>;  \<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau> in
                          clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)))"

abbreviation  b_conc_exec_abb :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  ("_ , _ , _ , _ \<turnstile> <_ , _> \<longrightarrow>\<^sub>c _") where
  "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<equiv> (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>')"

theorem conc_stmts_modify_local_only_raw:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>n. dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> set (signals_from cs)"
  using assms
proof (induction cs arbitrary:\<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence *: "\<And>n. dom (map_diff ( \<tau>1 n) ( \<tau> n)) \<subseteq> set (signals_from cs1)"
    using Bpar(1) by auto
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence **: "\<And>n. dom (map_diff ( \<tau>2 n) ( \<tau> n)) \<subseteq> set (signals_from cs2)"
    using Bpar(2) by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    unfolding \<tau>1_def \<tau>2_def by auto
  hence "... = \<tau>'"
    using Bpar(3) by auto
  hence "\<And>n. dom (map_diff ( \<tau>' n) ( \<tau> n))
                                                   \<subseteq> dom (map_diff ( \<tau>1 n) ( \<tau> n))
                                                   \<union> dom (map_diff ( \<tau>2 n) ( \<tau> n))"
    by (transfer', meson dom_map_diff_clean_zip_union)
  then show ?case
    using * **  by fastforce
next
  case (Bsingle sl ss)
  then show ?case
    by (cases "disjnt sl \<gamma>")  (auto simp add: seq_stmts_modify_local_only_raw zero_fun_def
          zero_option_def)
qed

text \<open>Similar to @{thm "seq_stmts_modify_local_only"}, we also prove that the semantics of the
concurrent statements only modifies the local variables.\<close>

theorem conc_stmts_modify_local_only:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  shows "\<And>n. dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> set (signals_from cs)"
  using assms conc_stmts_modify_local_only_raw by metis

lemma parallel_comp_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = \<tau>'"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> (cs2 || cs1) \<tau> = \<tau>'"
proof -
  have "disjnt (set (signals_from cs1)) (set (signals_from cs2))"
    using assms(1) unfolding conc_stmt_wf_def by (simp add: disjnt_def)
  thus ?thesis
    using van_tassel_second_prop' assms(2) by fastforce
qed

text \<open>The first property we prove for the semantics of the concurrent statement is that two
processes are commutative.\<close>

theorem parallel_comp_commute:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<longleftrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  using assms parallel_comp_commute' by metis

lemma clean_zip_raw_assoc:
  "clean_zip_raw \<tau> (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2), s1 \<union> s2) (\<tau>3, s3) =
   clean_zip_raw \<tau> (\<tau>1, s1) (clean_zip_raw \<tau> (\<tau>2, s2) (\<tau>3, s3), (s2 \<union> s3))"
  unfolding clean_zip_raw_def Let_def by (auto intro!: ext)

text \<open>The second property of the semantics of concurrent statements: they are associative. Together
with the first property of being commutative, they in some sense provide a guarantee that they are
truly parallel; we can execute whichever process in any order and the merging will always be the
same.\<close>

theorem parallel_comp_assoc:
  "b_conc_exec t \<sigma> \<gamma> \<theta> ((cs1 || cs2) || cs3) \<tau> = b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || (cs2 || cs3)) \<tau>"
  by (auto simp add: clean_zip_raw_assoc) 

text \<open>The Language Reference Manual for VHDL stipulates that each process will be executed initially
regardless of their sensitivity list.\<close>

fun init' :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw"
  where
    "init' t \<sigma> \<gamma> \<theta> (process sl : ss) \<tau> =  b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
  | "init' t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =
                       (let \<tau>1 = init' t \<sigma> \<gamma> \<theta> cs1 \<tau>;  \<tau>2 = init' t \<sigma> \<gamma> \<theta> cs2 \<tau> in 
                          clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)))"

definition rem_curr_trans :: "nat \<Rightarrow> 'signal trans_raw_sig \<Rightarrow> 'signal trans_raw_sig" where
  "rem_curr_trans t \<tau> s = (\<tau> s)(t := 0)"

lemma [simp]:
  "rem_curr_trans t 0 = 0"
  unfolding rem_curr_trans_def by (auto simp add: zero_fun_def)

lemma key_trans2_rem_curr_trans:
  "keys (rem_curr_trans t \<tau> s) = keys (\<tau> s) - {t}" for \<tau> :: "'a trans_raw_sig"
  unfolding rem_curr_trans_def
  by (auto simp add: zero_fun_def to_trans_raw_sig_def keys_def)

lemma trans_value_same_except_at_removed:
  "\<And>i s. i \<noteq> t \<Longrightarrow>  \<tau> s i = rem_curr_trans t \<tau> s i" for \<tau> :: "'a trans_raw_sig" 
  unfolding rem_curr_trans_def by auto

lemma inf_time_rem_curr_trans1:
  fixes \<tau> :: "'a trans_raw_sig"
  assumes "inf_time \<tau> s i \<noteq> Some t"
  assumes "t \<in> dom (\<tau> s)"
  shows "inf_time (rem_curr_trans t \<tau>) s i =  inf_time \<tau> s i"
proof (cases "i < t")
  case True
  hence "(\<exists>k\<in>keys ((\<tau> s)(t := 0)). k \<le> i) \<longleftrightarrow> (\<exists>k\<in>keys (\<tau> s). k \<le> i)"
    by (metis (no_types, lifting) fun_upd_apply keys_def mem_Collect_eq not_le)
  moreover have "(GREATEST k. k \<in> keys (\<tau> s) \<and> k \<le> i) = 
                 (GREATEST k. k \<in> keys ((\<tau> s)(t := 0)) \<and> k \<le> i)"
    by (metis (no_types) True domIff dom_def fun_upd_apply keys_def le_antisym nat_less_le 
    zero_option_def)
  ultimately show ?thesis
    by (simp add: inf_time_def to_trans_raw_sig_def rem_curr_trans_def)
next
  case False
  then obtain t' where *: "inf_time \<tau> s i = Some t'" and "t' > t"
    using assms
    by (metis (mono_tags, lifting) dual_order.strict_iff_order inf_time_def inf_time_none_iff
    inf_time_someE leI)
  hence "i \<ge> t'" and "i > t" and "t' \<in> keys (\<tau> s)"
    by (auto dest!:inf_time_at_most inf_time_some_exists simp add: to_trans_raw_sig_def)
  hence "t' \<in> keys ((\<tau> s)(t := 0)) \<and> t' \<le> i"
    using `t' > t` by (auto simp add: keys_def)
  hence exi: "\<exists>k\<in>keys ((\<tau> s)(t := 0)). k \<le> i"
    by (auto intro!: bexI[where x="t'"])
  have "(GREATEST k. k \<in> keys ((\<tau> s)(t := 0)) \<and> k \<le> i) = t'"
  proof (intro Greatest_equality)
    have **: "(GREATEST k. k \<in> keys (\<tau> s) \<and> k \<le> i) = t'"
      using * unfolding inf_time_def to_trans_raw_sig_def by (auto split:if_splits)
    { fix y
      assume "\<not> y \<le> t'" hence "t' < y" by auto
      have "i < y \<or> y \<le> i"
        by auto
      moreover
      { assume "i < y"
        hence "\<not> (y \<in> keys ((\<tau> s)(t := 0)) \<and> y \<le> i)"
          by auto }
      moreover
      { assume "y \<le> i"
        hence "y \<notin> keys (\<tau> s)"
          using ** `t' < y`  by (metis (no_types, lifting) Greatest_le_nat \<open>\<not> y \<le> t'\<close>)
        hence "y \<notin> keys ((\<tau> s)(t := 0))"
          using `t' < y` unfolding keys_def by (auto simp add: zero_fun_def)
        hence "\<not> (y \<in> keys ((\<tau> s)(t := 0)) \<and> y \<le> i)"
          by auto }
      ultimately have "\<not> (y \<in> keys ((\<tau> s)(t := 0)) \<and> y \<le> i)"
        by auto }
    thus "\<And>y. y \<in> keys ((\<tau> s)(t := 0)) \<and> y \<le> i \<Longrightarrow> y \<le> t'"
      by auto
  next
    show "t' \<in> keys ((\<tau> s)(t := 0)) \<and> t' \<le> i"
      using `t' \<in> keys ((\<tau> s)(t := 0)) \<and> t' \<le> i` by auto
  qed
  thus ?thesis
    unfolding * by (auto simp add: inf_time_def to_trans_raw_sig_def exi rem_curr_trans_def)
qed

lemma inf_time_rem_curr_trans2:
  fixes \<tau> :: "'a trans_raw_sig"
  assumes "inf_time \<tau> s i \<noteq> Some t"
  assumes "t \<notin> dom (\<tau> s)"
  shows "inf_time (rem_curr_trans t \<tau>) s i =  inf_time \<tau> s i"
proof -
  have "(\<tau> s)(t := 0) = \<tau> s"
    using assms(2)   by (auto simp add: zero_option_def )
  thus ?thesis
    by (simp add: inf_time_def rem_curr_trans_def)
qed

lemma inf_time_rem_curr_trans:
  "inf_time \<tau> s i \<noteq> Some t \<Longrightarrow> inf_time (rem_curr_trans t \<tau>) s i =  inf_time \<tau> s i" 
  for \<tau> :: "'a trans_raw_sig"
  using inf_time_rem_curr_trans1 inf_time_rem_curr_trans2 by fastforce

lemma inf_time_rem_curr_trans_at_t:
  fixes \<tau> :: "'a trans_raw_sig"
  assumes " inf_time \<tau> sig i = Some t"
  assumes " \<And>n s. n < t \<Longrightarrow> \<tau> s n = None"
  shows "inf_time (rem_curr_trans t \<tau>) sig i = None"
proof -
  have "\<forall>k \<in> dom (\<tau> sig). k \<le> i \<longrightarrow> k \<le> t"
    using assms by (auto dest!:inf_time_someE)
  hence "\<forall>k \<in> dom (\<tau> sig). t < k \<longrightarrow> i < k"
    using not_le by auto
  hence "\<forall>k \<in> dom (\<tau> sig) - {t}. i < k"
    using assms(2) by (metis DiffE domIff insertI1 nat_neq_iff)
  moreover have "dom (rem_curr_trans t \<tau> sig) = dom (\<tau> sig) - {t}"
    by (simp add:  rem_curr_trans_def to_trans_raw_sig_def zero_option_def)
  ultimately have "\<forall>t \<in> dom ( ( (rem_curr_trans t \<tau>) sig)). i < t"
    by auto
  thus "inf_time (rem_curr_trans t \<tau>) sig i = None"
    by (auto simp add: inf_time_none_iff)
qed

lemma rem_curr_trans_to_trans_raw_sig [simp]:
  "rem_curr_trans t (to_trans_raw_sig \<tau>) = to_trans_raw_sig (\<tau>(t := 0))"
  unfolding rem_curr_trans_def to_trans_raw_sig_def  by (metis fun_upd_apply zero_fun_def)

lemma inf_time_rem_curr_trans_at_0:
  "inf_time \<tau> sig i = Some 0 \<Longrightarrow> inf_time (rem_curr_trans 0 \<tau>) sig i = None" for k :: "'a trans_raw_sig"
  by (auto dest!: inf_time_rem_curr_trans_at_t)

lemma signal_of_rem_curr_trans_at_t:
  fixes \<tau> :: "'a trans_raw"
  assumes "\<And>s. s \<in> dom (\<tau> t) \<Longrightarrow> \<sigma> s = the ( \<tau> t s)"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "signal_of (\<sigma> A) (\<tau>(t := 0)) A i = signal_of (\<sigma> A) \<tau> A i"
proof (cases "inf_time (to_trans_raw_sig \<tau>) A i = Some t")
  case True
  hence el: "t \<in> dom (to_trans_raw_sig \<tau> A)"
    unfolding to_trans_raw_sig_def 
    by (auto dest!: inf_time_some_exists simp add: keys_def  zero_option_def)
  hence "signal_of (\<sigma> A) \<tau> A i =  the ( (to_trans_raw_sig \<tau> A) t)"
    using True unfolding to_signal_def comp_def by auto
  also have "... = \<sigma> A"
    using assms el  unfolding to_trans_raw_sig_def by auto
  finally have "signal_of (\<sigma> A) \<tau> A i = \<sigma> A"
    by auto
  have "inf_time (to_trans_raw_sig (\<tau> (t := 0))) A i = None"
    using inf_time_rem_curr_trans_at_t[OF True] assms(2) unfolding rem_curr_trans_to_trans_raw_sig
    by (metis to_trans_raw_sig_def zero_fun_def zero_option_def)  
  hence "signal_of (\<sigma> A) (\<tau>(t:=0)) A i = \<sigma> A"
    unfolding to_signal_def comp_def by auto
  then show ?thesis
    using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` by auto
next
  case False
  have "inf_time (to_trans_raw_sig (\<tau>(t:=0))) A i = inf_time (to_trans_raw_sig \<tau>) A i"
    using inf_time_rem_curr_trans[OF False] by auto
  moreover have "\<And>t'. t' \<noteq> t \<Longrightarrow> the ((to_trans_raw_sig (\<tau>(t:=0)) A) t') = the ((to_trans_raw_sig \<tau> A) t')"
    unfolding rem_curr_trans_def  unfolding to_trans_raw_sig_def by auto
  ultimately show ?thesis
    using False unfolding to_signal_def comp_def
    by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.expand option.sel)
qed

lemma signal_of2_rem_curr_trans_at_0:
  fixes \<tau> :: "'a trans_raw"
  assumes "\<And>s. s \<in> dom (\<tau> 0) \<Longrightarrow> \<sigma> s = the (\<tau> 0 s)"
  shows "signal_of (\<sigma> A) (\<tau>(0:=0)) A i = signal_of (\<sigma> A) \<tau> A i"
  using signal_of_rem_curr_trans_at_t[of "\<tau>", OF assms] unfolding rem_curr_trans_def 
  by auto  

lemma clean_zip_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>  n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>1 n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>2 n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (clean_zip_raw \<tau> (\<tau>1,s1) (\<tau>2,s2)) n = 0"
  using assms  unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)

lemma b_conc_exec_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) n = 0"
  using assms
proof (induction cs arbitrary: \<tau>)
  case (Bpar cs1 cs2)
  let ?\<tau>1 = "b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  let ?\<tau>2 = "b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = clean_zip_raw \<tau> (?\<tau>1, set (signals_from cs1)) (?\<tau>2, set (signals_from cs2))"
    by auto
  have "\<And>n. n < t \<Longrightarrow>  (clean_zip_raw \<tau> (?\<tau>1, set (signals_from cs1)) (?\<tau>2, set (signals_from cs2))) n = 0"
    using clean_zip_raw_preserve_trans_removal[OF Bpar(4)] Bpar by auto
  then show ?case  using Bpar(3) by auto
next
  case (Bsingle x1 x2)
  then show ?case by (auto simp add: b_seq_exec_preserve_trans_removal)
qed

lemma  rem_curr_trans_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow>  (\<tau>(t:=0)) n = 0"
  using assms by auto

lemma b_conc_exec_rem_curr_trans_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs (\<tau>(t:=0))) n = 0"
  using assms
  by (simp add: b_conc_exec_preserve_trans_removal rem_curr_trans_preserve_trans_removal)

lemma b_conc_exec_modifies_local:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i \<ge> t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  obtain \<tau>1 \<tau>2 where "b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau> = \<tau>1" and \<tau>2_def: "b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau> = \<tau>2"
    and \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar(5) by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using Bpar `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using \<tau>2_def `s \<notin> set (signals_from cs2)` Bpar(2) `i \<ge> t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by (transfer', simp add: clean_zip_raw_def)
  then show ?case
    by (auto simp add: \<tau>'_def)
next
  case (Bsingle x1 x2)
  hence "s \<notin> set (signals_in x2)"
    by auto
  have "disjnt x1 \<gamma> \<or> \<not> disjnt x1 \<gamma>" by auto
  moreover
  { assume "disjnt x1 \<gamma>"
    hence "\<tau>' = \<tau>"
      using Bsingle by auto
    hence ?case by auto }
  moreover
  { assume "\<not> disjnt x1 \<gamma>"
    hence \<tau>'_def: "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> x2 \<tau>"
      using Bsingle by auto
    hence ?case
      using b_seq_exec_modifies_local[OF _ `s \<notin> set (signals_in x2)` `t \<le> i`] by metis }
  ultimately show ?case by auto
qed

lemma b_conc_exec_modifies_local_before_now:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i < t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  obtain \<tau>1 \<tau>2 where "b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau> = \<tau>1" and \<tau>2_def: "b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau> = \<tau>2"
    and \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar(5) by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using Bpar `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using \<tau>2_def `s \<notin> set (signals_from cs2)` Bpar(2) `i < t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by (transfer', simp add: clean_zip_raw_def)
  then show ?case
    by (auto simp add: \<tau>'_def)
next
  case (Bsingle x1 x2)
  hence "s \<notin> set (signals_in x2)"
    by auto
  have "disjnt x1 \<gamma> \<or> \<not> disjnt x1 \<gamma>" by auto
  moreover
  { assume "disjnt x1 \<gamma>"
    hence "\<tau>' = \<tau>"
      using Bsingle by auto
    hence ?case by auto }
  moreover
  { assume "\<not> disjnt x1 \<gamma>"
    hence \<tau>'_def: "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> x2 \<tau>"
      using Bsingle by auto
    hence ?case
      using b_seq_exec_modifies_local_before_now[OF _ `s \<notin> set (signals_in x2)` `i < t`] by metis }
  ultimately show ?case by auto
qed

lemma b_conc_exec_modifies_local':
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
  by (metis b_conc_exec_modifies_local b_conc_exec_preserve_trans_removal not_le)

lemma b_conc_exec_modifies_local_strongest:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  by (metis assms b_conc_exec_modifies_local b_conc_exec_modifies_local_before_now not_le)

lemma b_conc_exec_empty_event:
  "b_conc_exec t \<sigma> {} \<theta> cs \<tau> = \<tau>"
  by (induction cs, auto simp add: clean_zip_same)

fun disjnts where
  "disjnts \<gamma> (Bsingle sl ss) \<longleftrightarrow> disjnt \<gamma> sl"
| "disjnts \<gamma> (Bpar cs1 cs2) \<longleftrightarrow> disjnts \<gamma> cs1 \<and> disjnts \<gamma> cs2"

lemma b_conc_exec_disjnts_event:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  assumes "disjnts \<gamma> cs"
  shows "\<tau> = \<tau>'"
  using assms
proof (induction cs arbitrary:\<tau>')
  case (Bpar cs1 cs2)
  then show ?case
    by (metis b_conc_exec.simps(2) clean_zip_same disjnts.simps(2))
next
  case (Bsingle x1 x2)
  then show ?case by (simp add: disjnt_sym)
qed

lemma b_conc_exec_trans_unchanged:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<gamma> = {} \<or> disjnts \<gamma> cs"
  shows "\<tau> = \<tau>'"
  using assms b_conc_exec_empty_event b_conc_exec_disjnts_event by metis

lemma same_trans_means_is_stable_eq:
  assumes "\<And>k. \<tau>1 k sig =  \<tau>2 k sig"
  shows "is_stable_raw dly \<tau>1 t sig (\<sigma> sig) = is_stable_raw dly \<tau>2 t sig (\<sigma> sig)"
proof -
  { fix m
    assume "t < m \<and> m \<le> t + dly"
    have "check (\<tau>1 m) sig (\<sigma> sig) = check (\<tau>2 m) sig (\<sigma> sig)"
      using assms(1) by auto }
  thus ?thesis
    unfolding  is_stable_raw_correct by auto
qed

lemma b_seq_exec_trans_post_raw_same:
  fixes sig e dly
  defines "ss \<equiv> Bassign_trans sig e dly"
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1) k s =   (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) k s"
  using assms
proof (induction ss)
  case (Bassign_trans)
  hence "s = sig"
    by auto
  have "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_trans sig e dly) \<tau>1 = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly"
    by auto
  hence " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_trans sig e dly) \<tau>1) k s =
          (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly) k s"
    by auto
  also have "... =  (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly) k s"
  proof -
    have "post_necessary_raw (dly-1) \<tau>1 t sig (beval_raw t \<sigma> \<gamma> \<theta> e) = post_necessary_raw (dly-1) \<tau> t sig (beval_raw t \<sigma> \<gamma> \<theta> e)"
      using Bassign_trans(2) by(auto intro!: post_necessary_raw_same)
    moreover have "preempt_raw sig \<tau>1 (t + dly) k s = preempt_raw sig \<tau> (t + dly) k s"
      using Bassign_trans(2) unfolding preempt_raw_def using `s = sig` by auto
    moreover have "post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) \<tau>1 (t + dly) k s = post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) \<tau> (t + dly) k s"
      using Bassign_trans(2) unfolding post_raw_def using `s = sig` by auto
    ultimately show ?thesis 
      unfolding trans_post_raw_def by auto
  qed
  also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_trans sig e dly) \<tau>) k s"
    by auto
  finally show ?case by auto
qed

lemma b_seq_exec_inr_post_same:
  fixes sig e dly
  defines "ss \<equiv> Bassign_inert sig e dly"
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1) k s =   (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) k s"
proof -
  fix k s
  assume "s \<in> set (signals_in ss)"
  hence "s = sig"
    unfolding ss_def by auto
  hence 2: "\<And>k.  \<tau> k s =  \<tau>1 k s"
    using assms(2) unfolding ss_def by auto
  have 3: "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>1 = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly"
    by auto
  have "is_stable_raw dly \<tau>1 t sig (\<sigma> sig) \<or> \<not> is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
    hence "is_stable_raw dly \<tau> t sig (\<sigma> sig)"
      by (metis "2" \<open>s = sig\<close> same_trans_means_is_stable_eq)
    have "inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly"
      using `is_stable_raw dly \<tau>1 t sig (\<sigma> sig)` unfolding inr_post_raw_def by auto
    hence " (inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly) k s =
            (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly) k s"
      by auto
    also have "... =  (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly) k s"
      using `s = sig` 2 unfolding trans_post_raw_def
      by (smt fun_upd_same post_necessary_raw_same preempt_raw_def post_raw_def)
    also have "... =  (inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly) k s"
      using `is_stable_raw dly \<tau> t sig (\<sigma> sig)` unfolding inr_post_raw_def by auto
    also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>) k s"
      by auto
    finally have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>1) k s =
                   (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>) k s"
      using 3 by auto }
  moreover
  { assume "\<not> is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
    hence "\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
      by (metis "2" \<open>s = sig\<close> same_trans_means_is_stable_eq)
    have in_tr: "inr_post_raw  sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly =
          trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau>1 t dly sig) t dly "
      using `\<not> is_stable_raw dly \<tau>1 t sig (\<sigma> sig)` unfolding inr_post_raw_def by auto
    have *: "\<And>k. (purge_raw \<tau>1 t dly sig) k s = (purge_raw \<tau> t dly sig) k s"
      using 2 `s = sig` unfolding purge_raw_def by (simp add: override_on_def)
    define purge_rawd1 where "purge_rawd1 = purge_raw \<tau>1 t dly sig"
    define purge_rawd  where "purge_rawd  = purge_raw \<tau>  t dly sig"
    hence "\<And>k.  purge_rawd1 k s =  purge_rawd k s"
      using * unfolding purge_rawd1_def by auto
    hence tr_tr: " (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) purge_rawd1 t dly) k s =
           (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) purge_rawd t dly) k s "
      using `s = sig`
    proof -
      have "post_necessary_raw (dly-1) purge_rawd1 t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) =
            post_necessary_raw (dly-1) purge_rawd t sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)"
        using post_necessary_raw_same[of "purge_rawd1" "s" "purge_rawd"] *
        by (simp add: \<open>s = sig\<close> purge_rawd1_def purge_rawd_def)
      thus ?thesis 
        by (smt "*" \<open>s = sig\<close> fun_upd_same preempt_raw_def purge_rawd1_def purge_rawd_def
        post_raw_def trans_post_raw_def)
    qed
    have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>1) k s =
           (inr_post_raw  sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau>1 t dly) k s"
      by auto
    also have "... =   (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau>1 t dly sig) t dly) k s"
      using in_tr by auto
    also have "... =   (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly) k s"
      using tr_tr unfolding purge_rawd1_def purge_rawd_def by auto
    also have "... =   (inr_post_raw  sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly) k s"
      using `\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)` unfolding inr_post_raw_def by auto
    also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>) k s"
      by auto
    finally have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>1) k s =
                   (b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau>) k s"
      by auto }
  ultimately show " (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1) k s =   (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) k s"
    unfolding ss_def by auto
qed

lemma b_seq_exec_same:
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1) k s =   (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) k s"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>1)
  case (Bcomp ss1 ss2)
  define \<tau>' where "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  define \<tau>1' where "\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>1"
  hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
    by auto
  have *: "\<And>k s. s \<in> set (signals_in ss1) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s" and
       **: "\<And>k s. s \<in> set (signals_in ss2) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
    using Bcomp by auto
  hence inss1: "\<And>k s. s \<in> set (signals_in ss1) \<Longrightarrow>  \<tau>' k s =  \<tau>1' k s"
    using Bcomp(1) unfolding \<tau>'_def \<tau>1'_def by metis
  have ninss1: "\<And>k s. s \<notin> set (signals_in ss1) \<Longrightarrow>  \<tau>' k s =  \<tau> k s"
    using b_seq_exec_modifies_local_strongest[OF `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`] by auto
  have ninss1': "\<And>k s. s \<notin> set (signals_in ss1) \<Longrightarrow>  \<tau>1' k s =  \<tau>1 k s"
    using b_seq_exec_modifies_local_strongest[OF `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'`] by auto

  have "s \<in> set (signals_in ss1) \<or> s \<notin> set (signals_in ss1)"
    by auto
  moreover
  { assume "s \<in> set (signals_in ss1)"
    have  " (b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>) k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>1) k s"
      using Bcomp(1)[OF `s \<in> set (signals_in ss1)` *]  by auto
    hence " \<tau>' k s =  \<tau>1' k s"
      unfolding \<tau>'_def \<tau>1'_def by auto
    have " s \<in> set (signals_in ss2) \<or> s \<notin> set (signals_in ss2)"
      by auto
    moreover
    { assume "s \<in> set (signals_in ss2)"
      have "\<And>k s. s \<in> set (signals_in ss2) \<Longrightarrow>  \<tau>' k s =  \<tau>1' k s"
      proof -
        fix k' s'
        assume "s' \<in> set (signals_in ss2)"
        have "s' \<in> set (signals_in ss1) \<or> s' \<notin> set (signals_in ss1)"
          by auto
        moreover
        { assume "s' \<in> set (signals_in ss1)"
          with inss1 have " \<tau>' k' s' =  \<tau>1' k' s'"
            by auto }
        moreover
        { assume "s' \<notin> set (signals_in ss1)"
          hence " \<tau>' k' s' =  \<tau> k' s'" and " \<tau>1' k' s' =  \<tau>1 k' s'"
            using ninss1' ninss1 by auto
          hence " \<tau>' k' s' =  \<tau>1' k' s'"
            using **[OF `s' \<in> set (signals_in ss2)`] by auto }
        ultimately show " \<tau>' k' s' =  \<tau>1' k' s'"
          by auto
      qed
      hence ***: " (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>') k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>1') k s"
        using Bcomp(2)[OF `s \<in> set (signals_in ss2)`] by metis

      have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>) k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>') k s"
        unfolding \<tau>'_def by auto
      also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>1') k s"
        using *** by auto
      also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>1) k s"
        unfolding \<tau>1'_def by auto
      finally have ?case by auto }
    moreover
    { assume "s \<notin> set (signals_in ss2)"
      have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>) k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>') k s"
        unfolding \<tau>'_def by auto
      also have "... =  \<tau>' k s"
        using `s \<notin> set (signals_in ss2)` b_seq_exec_modifies_local_strongest by metis
      also have "... =  \<tau>1' k s"
        using inss1[OF `s \<in> set (signals_in ss1)`] by auto
      also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>1') k s"
        using `s \<notin> set (signals_in ss2)` b_seq_exec_modifies_local_strongest by  metis
      also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>1) k s"
        unfolding \<tau>1'_def by auto
      finally have ?case by auto }
    ultimately have ?case by auto }
  moreover
  { assume "s \<notin> set (signals_in ss1)"
    hence "s \<in> set (signals_in ss2)"
      using Bcomp by auto
    have "\<And>k s. s \<in> set (signals_in ss2) \<Longrightarrow>  \<tau>' k s =  \<tau>1' k s"
    proof -
      fix k' s'
      assume "s' \<in> set (signals_in ss2)"
      have "s' \<in> set (signals_in ss1) \<or> s' \<notin> set (signals_in ss1)"
        by auto
      moreover
      { assume "s' \<in> set (signals_in ss1)"
        with inss1 have " \<tau>' k' s' =  \<tau>1' k' s'"
          by auto }
      moreover
      { assume "s' \<notin> set (signals_in ss1)"
        hence " \<tau>' k' s' =  \<tau> k' s'" and " \<tau>1' k' s' =  \<tau>1 k' s'"
          using ninss1' ninss1 by auto
        hence " \<tau>' k' s' =  \<tau>1' k' s'"
          using **[OF `s' \<in> set (signals_in ss2)`] by auto }
      ultimately show " \<tau>' k' s' =  \<tau>1' k' s'"
        by auto
    qed
    hence ***: " (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>') k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>1') k s"
      using Bcomp(2)[OF `s \<in> set (signals_in ss2)`] by metis
    have " (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>) k s =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>') k s"
      unfolding \<tau>'_def by auto
    also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>1') k s"
      using *** by auto
    also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau>1) k s"
      unfolding \<tau>1'_def by auto
    finally have ?case by auto }
  ultimately show ?case by auto
next
  case (Bguarded g ss1 ss2)
  then show ?case
    by (smt Un_iff b_seq_exec.simps(3) b_seq_exec_modifies_local_strongest set_append set_remdups
        signals_in.simps(4))
next
  case (Bassign_trans sig e dly)
  then show ?case
    by (meson b_seq_exec_trans_post_raw_same)
next
  case (Bassign_inert sig e dly)
  then show ?case
    by (meson b_seq_exec_inr_post_same)
next
  case Bnull
  then show ?case by auto
qed

lemma b_conc_exec_same:
  assumes "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  assumes "conc_stmt_wf cs"
  shows "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>1) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) k s"
  using assms
proof (induction cs)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs2" and "conc_stmt_wf cs1"
    by (simp add: conc_stmt_wf_def)+
  define \<tau>a where "\<tau>a = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>1"
  define \<tau>b where "\<tau>b = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1"

  define \<tau>a' where "\<tau>a' = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  define \<tau>b' where "\<tau>b' = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  have "\<And>k.  \<tau> k s =  \<tau>1 k s"
    using Bpar by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau>1 = clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))"
    unfolding \<tau>a_def \<tau>b_def by auto
  hence *: " (b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau>1) k s =
          (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s"
    by auto
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2)"
    using Bpar by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence " (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s =
            \<tau>a k s"
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    also have "... =  \<tau>a' k s"
      using Bpar(1)[OF `s \<in> set (signals_from cs1)`] Bpar(4) `conc_stmt_wf cs1` unfolding \<tau>a_def \<tau>a'_def by auto
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs1)`
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using *  by (simp add: \<tau>a'_def \<tau>b'_def) }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    moreover hence "s \<notin> set (signals_from cs1)"
      using ` conc_stmt_wf (cs1 || cs2)`
      by (metis conc_stmt_wf_def disjnt_def disjnt_iff distinct_append signals_from.simps(2))
    ultimately have " (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s =
            \<tau>b k s"
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    also have "... =  \<tau>b' k s"
      using Bpar(2)[OF `s \<in> set (signals_from cs2)`] Bpar(4) `conc_stmt_wf cs2` unfolding \<tau>b_def \<tau>b'_def
      by auto
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs2)` `s \<notin> set (signals_from cs1)`
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using *  by (simp add: \<tau>a'_def \<tau>b'_def) }
  ultimately show ?case
    by auto
next
  case (Bsingle sl ss)
  hence *: "\<And>k s.  s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
    by auto
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence "b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>1 = \<tau>1"
      by auto
    hence " (b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>1) k s =
            \<tau>1 k s"
      by auto
    also have "... =  \<tau> k s"
      using * Bsingle by auto
    also have "... =  (b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>) k s"
      using `disjnt sl \<gamma>` by auto
    finally have ?case by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence "b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>1 = b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1"
      by auto
    hence " (b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>1) k s =
            (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>1) k s"
      by auto
    also have "... =  (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) k s"
      using b_seq_exec_same[OF *] Bsingle by auto
    also have "... =  (b_conc_exec t \<sigma> \<gamma> \<theta> (Bsingle sl ss) \<tau>) k s"
      using `\<not> disjnt sl \<gamma>` by auto
    finally have ?case
      by auto }
  ultimately show ?case by auto
qed

lemma b_conc_exec_sequential:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 (b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>)"
proof -
  have "conc_stmt_wf cs2"
    using assms by (simp add: conc_stmt_wf_def)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  define s1 where "s1 = set (signals_from cs1)"
  define s2 where "s2 = set (signals_from cs2)"
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)"
    unfolding \<tau>1_def \<tau>2_def s1_def s2_def by auto
  also have "... = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1"
  proof (rule ext, rule)
    fix k s
    have "s \<in> s1 \<or> s \<in> s2 \<or> s \<notin> s1 \<and> s \<notin> s2"
      by auto
    moreover
    { assume "s \<in> s1"
      hence *: " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>1 k s"
         unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
      moreover have "s \<notin> set (signals_from cs2)"
        using `s \<in> s1` assms(1)
        by (metis conc_stmt_wf_def disjoint_insert(1) distinct_append mk_disjoint_insert s1_def
            signals_from.simps(2))
      have " (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s =  \<tau>1 k s"
        by (metis \<open>s \<notin> set (signals_from cs2)\<close> b_conc_exec_modifies_local_strongest)
      with * have "  (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s"
        by auto }
    moreover
    { assume "s \<in> s2"
      moreover have "s \<notin> s1" using assms(1)
        by (metis calculation conc_stmt_wf_def disjoint_insert(1) distinct_append mk_disjoint_insert
            s1_def s2_def signals_from.simps(2))
      ultimately have *: " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>2 k s"
         unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
      have "s \<in> set (signals_from cs2)" and "s \<notin> set (signals_from cs1)"
        using `s \<in> s2` `s \<notin> s1` unfolding s2_def s1_def by auto
      have "\<And>k s. s \<in> set (signals_from cs2) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
        using b_conc_exec_modifies_local_strongest[OF _ `s \<notin> set (signals_from cs1)`]
        by (metis \<tau>1_def assms b_conc_exec_modifies_local_strongest conc_stmt_wf_def disjoint_insert(1)
            distinct_append mk_disjoint_insert signals_from.simps(2))
      hence " (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>) k s"
        using b_conc_exec_same[OF _ `conc_stmt_wf cs2` `s \<in> set (signals_from cs2)`] by blast
      also have "... =  \<tau>2 k s"
        unfolding \<tau>2_def by auto
      finally have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s"
        using * by auto }
    moreover
    { assume "s \<notin> s1 \<and> s \<notin> s2"
      hence *: " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau> k s"
         unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
      have "s \<notin> set (signals_from cs2)" and "s \<notin> set (signals_from cs1)"
        using `s \<notin> s1 \<and> s \<notin> s2` unfolding s2_def s1_def by auto
      have " (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s =  \<tau>1 k s"
        using b_conc_exec_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs2)`]  by presburger
      also have "... =  \<tau> k s"
        unfolding \<tau>1_def  using b_conc_exec_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs1)`]
        by presburger
      finally have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s"
        using * by auto }
    ultimately show " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1) k s"
      by auto
  qed
  finally show ?thesis
    unfolding \<tau>1_def by auto
qed

subsection \<open>Semantics of simulation\<close>

text \<open>The other aspect of the semantics is how to simulate, or in a sense execute, VHDL text. One
has to deal with the advance of simulation time. Rather than advancing time naturally, the
simulation proceeds to the "next interesting point of computation" @{cite "VanTassel1995"}. The
following function does exactly this purpose.\<close>

definition next_time :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> nat" where
  "next_time t \<tau> = (if \<tau> = 0 then t + 1 else LEAST n. dom (\<tau> n) \<noteq> {})"

lemma until_next_time_zero:
  "\<forall>n. t < n \<and> n < next_time t \<tau>' \<longrightarrow> \<tau>' n = 0"
proof (cases "\<tau>' = 0")
  case True
  then show ?thesis  by (auto simp add: zero_fun_def)
next
  case False
  hence "next_time t \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
    unfolding next_time_def by auto
  hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow> dom (\<tau>' n) = {}"
    using not_less_Least by auto
  thus  ?thesis 
    by (auto simp add: zero_fun_def zero_option_def)
qed
  
lemma [simp]:
  "next_time t 0 = t + 1"
  unfolding next_time_def by auto

lemma next_time_at_least:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
  shows "t \<le> next_time t \<tau>'"
proof (cases "\<tau>' = 0")
  case True
  then show ?thesis by auto
next
  case False
  hence *: "\<exists>n. dom (\<tau>' n) \<noteq> {}"
    unfolding zero_fun_def zero_option_def by auto
  have "t \<le> (LEAST n. dom ( \<tau>' n) \<noteq> {})"
  proof (rule ccontr)
    assume "\<not> t \<le> (LEAST n. dom ( \<tau>' n) \<noteq> {})"
    hence "(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t" (is "?least < _")
      by auto
    with assms have " \<tau>' ?least = 0"
      by auto
    have "dom ( \<tau>' ?least) \<noteq> {}"
      using LeastI_ex[OF *] by auto
    thus "False"
      by (metis \<open> \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {}) = 0\<close> dom_eq_empty_conv
                zero_fun_def zero_option_def)
  qed
  then show ?thesis
    unfolding next_time_def by auto
qed

lemma next_time_at_least2:
  assumes "next_time t \<tau>' = t'"
  shows "\<forall>n. n < t' \<longrightarrow>  \<tau>' n = 0"
  using assms
proof (cases "\<tau>' = 0")
  case True
  then show ?thesis by (auto simp add: zero_fun_def zero_option_def)
next
  case False
  hence "t' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
    using assms by (auto simp add: next_time_def)
  moreover have "\<And>n. dom ( \<tau>' n) = {} \<longleftrightarrow>  \<tau>' n = 0"
    by (simp add: zero_fun_def zero_option_def)
  ultimately have "t' = (LEAST n.  \<tau>' n \<noteq> 0)"
    by auto
  then show ?thesis
    using not_less_Least by blast
qed

lemma signal_of2_init:
  assumes "t \<le> i"
  assumes "i < next_time t \<tau>'"
  assumes "s \<in> dom ( \<tau>' t) \<Longrightarrow> \<sigma> s = the ( \<tau>' t s)"
  assumes *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
  shows "signal_of (\<sigma> s) \<tau>' s i = \<sigma> s"
proof -
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *] by auto
  obtain t' where "inf_time (to_trans_raw_sig \<tau>') s i = Some t' \<or> inf_time (to_trans_raw_sig \<tau>') s i = None"
    by auto
  moreover
  { assume "inf_time (to_trans_raw_sig \<tau>') s i = None"
    hence "signal_of (\<sigma> s) \<tau>' s i = \<sigma> s"
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume "inf_time (to_trans_raw_sig \<tau>') s i = Some t'"
    hence "t' < next_time t \<tau>'"
      by (meson assms(2) inf_time_at_most order.strict_trans1)
    have "t' \<in> dom ( (to_trans_raw_sig \<tau>' s))"
      using inf_time_some_exists[OF `inf_time (to_trans_raw_sig \<tau>') s i = Some t'`] 
      by (auto simp add: dom_is_keys)
    hence " \<tau>' t' \<noteq> 0"
       unfolding to_trans_raw_sig_def zero_fun_def zero_option_def by auto
    have **: "\<And>n. n < t \<Longrightarrow>  (to_trans_raw_sig \<tau>' s) n = 0"
      using *  unfolding to_trans_raw_sig_def  by (simp add: zero_fun_def)
    have "t \<le> t'"
    proof (rule ccontr)
      assume "\<not> t \<le> t'" hence "t' < t" by auto
      with ** have " (to_trans_raw_sig \<tau>' s) t' = 0" by auto
      with `t' \<in> dom ( (to_trans_raw_sig \<tau>' s))` show False
         unfolding to_trans_raw_sig_def by (simp add: domIff zero_option_def)
    qed
    moreover have "\<And>n. t < n \<Longrightarrow> n < next_time t \<tau>' \<Longrightarrow>  \<tau>' t = 0"
      using next_time_at_least2 order.strict_trans by blast
    ultimately have "t' = t"
      using `t' < next_time t \<tau>'` ` \<tau>' t' \<noteq> 0`  by (simp add: next_time_at_least2)
    hence "inf_time (to_trans_raw_sig \<tau>') s i = Some t"
      using `inf_time (to_trans_raw_sig \<tau>') s i = Some t'` by auto
    hence "signal_of (\<sigma> s) \<tau>' s i = \<sigma> s"
      using assms(3) unfolding to_signal_def comp_def
      using \<open> \<tau>' t' \<noteq> 0\<close> \<open>t' < next_time t \<tau>'\<close> next_time_at_least2 by blast }
  ultimately show "signal_of (\<sigma> s) \<tau>' s i = \<sigma> s"
    by auto
qed

lemma next_time_eq_next_rem_curr_trans:
  fixes \<tau> :: "'a trans_raw"
  assumes "next_time t \<tau> \<noteq> t"
  assumes *: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "next_time t \<tau> = next_time t (\<tau>(t:=0))"
proof (cases "\<tau> \<noteq> 0")
  case True
  hence "(LEAST n. dom ( \<tau> n) \<noteq> {}) \<noteq> t"
    using assms unfolding next_time_def by auto
  hence " \<tau> t = 0"
    using assms   by (metis le_neq_trans next_time_at_least next_time_at_least2)
  hence "\<tau>(t:=0) = \<tau>"
    by auto
  thus ?thesis by auto
next
  case False
  hence "\<tau> = 0"
    by auto
  have "\<tau>(t:=0) = \<tau>"
    unfolding `\<tau> = 0` by (auto simp add: zero_fun_def)
  thus ?thesis
    by auto
qed

lemma signal_of2_init':
  fixes \<tau> :: "'a trans_raw"
  assumes "t \<le> i"
  assumes "i < next_time t (\<tau>(t:=0))"
  assumes "s \<in> dom ( \<tau> t) \<Longrightarrow> \<sigma> s = the ( \<tau> t s)"
  assumes *: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "signal_of (\<sigma> s) \<tau> s i = \<sigma> s"
proof -
  have "t \<le> next_time t \<tau>"
    using next_time_at_least[OF *] by auto
  have "\<And>n. n < t \<Longrightarrow>  (\<tau>(t:=0)) n = 0"
    using * by  auto
  hence "t \<le> next_time t (\<tau>(t:=0))"
    using next_time_at_least by metis
  obtain t' where "inf_time (to_trans_raw_sig \<tau>) s i = Some t' \<or> inf_time (to_trans_raw_sig \<tau>) s i = None"
    by auto
  moreover
  { assume "inf_time (to_trans_raw_sig \<tau>) s i = None"
    hence "signal_of (\<sigma> s) \<tau> s i = \<sigma> s"
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume "inf_time (to_trans_raw_sig \<tau>) s i = Some t'"
    hence "t' < next_time t (\<tau>(t:=0))"
      by (meson assms(2) inf_time_at_most order.strict_trans1)
    have "t' \<in> dom ( (to_trans_raw_sig \<tau> s))"
      using inf_time_some_exists[OF `inf_time (to_trans_raw_sig \<tau>) s i = Some t'`] by (auto simp add: dom_is_keys)
    hence " \<tau> t' \<noteq> 0"
       unfolding to_trans_raw_sig_def zero_fun_def zero_option_def by auto
    have **: "\<And>n. n < t \<Longrightarrow>  (to_trans_raw_sig \<tau> s) n = 0"
      using *  unfolding to_trans_raw_sig_def  by (simp add: zero_fun_def)
    have "t \<le> t'"
    proof (rule ccontr)
      assume "\<not> t \<le> t'" hence "t' < t" by auto
      with ** have " (to_trans_raw_sig \<tau> s) t' = 0" by auto
      with `t' \<in> dom ( (to_trans_raw_sig \<tau> s))` show False
         unfolding to_trans_raw_sig_def by (simp add: domIff zero_option_def)
    qed
    hence "next_time t (\<tau>(t:=0)) \<noteq> t"
      using `t' < next_time t (\<tau>(t:=0))` by auto
    hence "t < next_time t (\<tau>(t:=0))"
      using `t \<le> next_time t (\<tau>(t:=0))` by auto
    have h: "\<And>n. t < n \<Longrightarrow> n < next_time t (\<tau>(t:=0)) \<Longrightarrow>  (\<tau>(t:=0)) n = 0"
      using next_time_at_least2 order.strict_trans  by blast
    have h0: "\<And>n. t < n \<Longrightarrow> n < next_time t (\<tau>(t:=0)) \<Longrightarrow> next_time t \<tau> \<noteq> t \<Longrightarrow>  \<tau> n = 0"
    proof (rule ccontr)
      fix n
      assume "t < n"
      assume "n < next_time t (\<tau>(t:=0))"
      assume "next_time t \<tau> \<noteq> t"
      assume " \<tau> n \<noteq> 0"
      hence "dom ( \<tau> n) \<noteq> {}"
        unfolding zero_fun_def zero_option_def by auto
      hence "next_time t \<tau> \<le> n"
        unfolding next_time_def using `t < n`  by (simp add: Least_le)
      have "next_time t \<tau> = next_time t (\<tau>(t:=0))"
          using "*" \<open>next_time t \<tau> \<noteq> t\<close> next_time_eq_next_rem_curr_trans by auto
      hence "next_time t (\<tau>(t:=0)) \<le> n"
          using `next_time t \<tau> \<le> n` by auto
      with `n < next_time t (\<tau>(t:=0))` show "False" by auto
    qed
    have h0': "\<And>n. t < n \<Longrightarrow> n < next_time t (\<tau>(t:=0)) \<Longrightarrow> next_time t \<tau> = t \<Longrightarrow>  \<tau> n = 0"
    proof -
      fix n
      assume "t < n"
      assume "n < next_time t (\<tau>(t:=0))"
      assume "next_time t \<tau> = t"
      hence "\<tau> = 0 \<or> (LEAST n. dom ( \<tau> n) \<noteq> {}) = t"
        unfolding next_time_def by metis
      moreover
      { assume "\<tau> = 0"
        hence "\<tau>(t:=0) = \<tau>"
          using \<open> \<tau> t' \<noteq> 0\<close> by (auto simp add: zero_fun_def)
        hence " \<tau> n = 0" using h[OF `t < n`] `n < next_time t (\<tau>(t:=0))`
          by auto }
      moreover
      { assume "(LEAST n. dom ( \<tau> n) \<noteq> {}) = t"
        hence " (\<tau>(t:=0)) n = 0"
          using h[OF `t < n` `n < next_time t (\<tau>(t:=0))`] by auto
        have " (\<tau>(t:=0)) n =  \<tau> n"
          using `t < n` by  auto
        hence " \<tau> n = 0"
          using ` (\<tau>(t:=0)) n = 0` by auto }
      ultimately  show " \<tau> n = 0"
        by auto
    qed
    hence h1: "\<And>n. t < n \<Longrightarrow> n < next_time t (\<tau>(t:=0))  \<Longrightarrow>  \<tau> n = 0"
      using h0 h0' by auto
    hence "t' = t"
      using `t \<le> t'` `t' < next_time t (\<tau>(t:=0))` ` \<tau> t' \<noteq> 0` le_neq_trans
      by blast
    hence "inf_time (to_trans_raw_sig \<tau>) s i = Some t"
      using `inf_time (to_trans_raw_sig \<tau>) s i = Some t'` by auto
    have "s \<in> dom ( \<tau> t)"
      using inf_time_some_exists[OF `inf_time (to_trans_raw_sig \<tau>) s i = Some t`]
      unfolding to_trans_raw_sig_def by (auto simp add: dom_is_keys keys_def zero_option_def)
    hence "the ( (to_trans_raw_sig \<tau> s) t) = \<sigma> s"
      using assms(3)[OF `s \<in> dom ( \<tau> t)`]  unfolding to_trans_raw_sig_def by auto
    hence "signal_of (\<sigma> s) \<tau> s i = \<sigma> s"
      using `inf_time (to_trans_raw_sig \<tau>) s i = Some t` unfolding to_signal_def comp_def
      by auto }
  ultimately show "signal_of (\<sigma> s) \<tau> s i = \<sigma> s"
    by auto
qed

text \<open>At some point, a normal VHDL text would contain no more interesting computations. We check
this with the following @{term "quiet"} function. \<close>

definition quiet :: "'signal trans_raw \<Rightarrow> 'signal event \<Rightarrow> bool" where
  "quiet \<tau> evt = (if \<tau> = 0 \<and> evt = {} then True else False)"

text \<open>The function @{term "next_state"} is to update the state of computation in the next
interesting point of computation. \<close>

definition next_state :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal state" where
  "next_state t \<tau>' \<sigma> = (let m = \<tau>' (next_time t \<tau>') in override_on \<sigma> (the o m) (dom m))"

lemma [simp]:
  "override_on \<sigma> (the o (0 :: 'a \<rightharpoonup> bool)) (dom (0 :: 'a \<rightharpoonup> bool)) = \<sigma>"
  by (simp add: zero_fun_def zero_option_def)

text \<open>The function @{term "next_event"} checks whether the state at the next interesting point of
computation differs from the current state. Any signal which is different is listed as event.\<close>

definition next_event :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal event" where
  "next_event t \<tau>' \<sigma> = (let m =  \<tau>' (next_time t \<tau>') in {sig. sig \<in> dom m \<and> (the o m) sig \<noteq> \<sigma> sig})"

lemma [simp]:
  "{sig. sig \<in> dom (0 :: 'a \<rightharpoonup> bool) \<and> (the o (0 :: 'a \<rightharpoonup> bool)) sig \<noteq> \<sigma> sig} = {}"
  by (simp add:zero_option_def zero_fun_def)

lemma next_event_alt_def:
  "next_event t \<tau>' \<sigma> = {sig. \<sigma> sig \<noteq> next_state t \<tau>' \<sigma> sig}"
  by (smt Collect_cong next_event_def next_state_def override_on_def)

lemma next_state_fixed_point:
  assumes "sig \<notin> next_event t \<tau>' \<sigma>"
  shows "next_state t \<tau>' \<sigma> sig = \<sigma> sig"
  using assms next_event_alt_def by force

text \<open>After we advance to the next interesting computation point, we need to save the behaviour so
that we can return this as the result in the end of the computation (either when it is quiet or
the maximum simulation time is reached).\<close>

definition add_to_beh :: "'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal trans_raw" where
  "add_to_beh \<sigma> \<theta> st fi = (if st < fi then \<theta>(st := Some o \<sigma>) else \<theta>)"

lemma [simp]:
  "add_to_beh \<sigma> \<theta> t t = \<theta>"
  unfolding add_to_beh_def by (transfer, auto)

text \<open>The judgement or simulation rule. Three cases are considered here: 1) whether the maximum
simulation time has not reached yet and there are transactions to process; 2) whether there is no
more interesting computation (quiesced or quiet); and 3) whether the maximum simulation time is up.

The following semantic rule use a turnstile notation --- as in logic --- to determine what is the
context (or environment so to speak), what concurrent statement is being considered, what is the
predicted behaviour in the future (transaction), and lastly the result of the execution of VHDL text.
Check the mixfix notation used in the semantics below.

The left hand side of the turnstile contains simulation elements: time @{term "t :: nat"},
state @{term "\<sigma> :: 'signal state"}, event @{term "\<gamma> :: 'signal event"}, and trace
@{term "\<theta> :: 'signal trans_raw"}. This is the context to determine how a VHDL text shall progress.
The right hand side of the turnstile is divided further into two parts to the left and right of
the squiggle. The left of the squiggle is a pair of the concurrent statements (a list of processes)
and the  current transaction store. The right part is of course the result of executing the
semantics.

In the following definition, @{term "t"} denotes the current computation time. During the first case
any transaction posted at time @{term "t"} is removed; this is because the normative way of the
simulation process is that transaction posted at this time has been processed previously. But what
if this is the rule encountered in the first step of the simulation? Remember that according to the
language reference manual, the whole VHDL text is executed via @{term "init'"} first regardless of
the sensitivity list in each process.

It is possible for the judgement rule below to advance into time that is later than the maximum
time. Checking whether the current computation time is within the maximum simulation time appears
later. It is possible to avoid this but it would clutter the first rule (business as usual rule).
In case the current time is much later than the maximum time, we just have to delete the behaviours
from @{term "maxtime + 1"} to @{term "t"}.
\<close>


inductive b_simulate_fin :: "nat \<Rightarrow> nat \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  ("_, _ , _ , _ , _ \<turnstile> <_ , _> \<leadsto> _") where

  \<comment> \<open>Business as usual: not quiesced yet and there is still time\<close>
  "    (t \<le> maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')
   \<Longrightarrow> (maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"

  \<comment> \<open>The simulation has quiesced and there is still time\<close>
| "    (t \<le> maxtime)
   \<Longrightarrow> (quiet \<tau> \<gamma>)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> \<theta>(t:= Some o \<sigma>))"

  \<comment> \<open>Time is up\<close>
| "  \<not> (t \<le> maxtime)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> \<theta>)"

lemma b_simulate_fin_almost_all_zero:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. res x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have "\<forall>\<^sub>\<infinity>x. add_to_beh \<sigma> \<theta> t (next_time t \<tau>') x = 0"
    using 1(6) unfolding add_to_beh_def by (metis (mono_tags) upd_eventually_cofinite)
  then show ?case 
    using 1(5) by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs)
  then show ?case 
    by (metis (mono_tags) upd_eventually_cofinite)
next
  case (3 t maxtime \<sigma> \<gamma> \<theta> cs \<tau>)
  then show ?case by auto
qed

inductive_cases bau: "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"

lemma case_quiesce:
  assumes "t \<le> maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "res = \<theta> (t:= (Some o \<sigma>))"
  using bau[OF assms(3)] assms by auto

lemma case_timesup:
  assumes "\<not> (t \<le> maxtime)"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "res = \<theta>"
  using bau[OF assms(2)] assms by auto

lemma case_bau:
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  shows "(maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> beh)"
  using bau[OF assms(4)] assms by auto

lemma case_bau2:
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  obtains \<tau>' where "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and
                   "(maxtime,
                       next_time t \<tau>',
                          next_state t \<tau>' \<sigma>,
                              next_event t \<tau>' \<sigma>,
                                  add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> beh)"
  using bau[OF assms(3)] assms by auto

lemma beh_res:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "t \<le> maxtime"
  shows "\<And>n. n < t \<Longrightarrow>  \<theta> n =  beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF 1(7)] 1(3) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  hence ind1: "n < next_time t \<tau>'"
    using `n < t` by auto
  have ind2: "(\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0) "
    by (metis next_time_at_least2 rem_curr_trans_preserve_trans_removal)
  have "next_time t \<tau>' \<le> maxtime \<or> \<not> next_time t \<tau>' \<le> maxtime"
    by auto
  moreover
  { assume ind3: "next_time t \<tau>' \<le> maxtime"
    with 1(5)[OF ind1 ind2] have " (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  res n"
      by auto
    hence ?case using `n < t`
      unfolding add_to_beh_def  by (metis (full_types) fun_upd_apply nat_neq_iff) }
  moreover
  { assume "\<not> next_time t \<tau>' \<le> maxtime" hence "maxtime < next_time t \<tau>'" by auto
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t := Some o \<sigma>)"
      using `t \<le> maxtime` unfolding add_to_beh_def by auto
    define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
    define \<gamma>' where "\<gamma>' = next_event t \<tau>' \<sigma>"
    define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
    hence \<theta>'_def2: "\<theta>' = \<theta>(t:= Some o \<sigma>)"
      using `add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t :=(Some o \<sigma>))` by auto
    hence "maxtime, next_time t \<tau>', \<sigma>', \<gamma>', \<theta>' \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res"
      using 1(4) unfolding \<theta>'_def \<sigma>'_def \<gamma>'_def by auto
    hence "res = \<theta>'"
      using case_timesup[OF `\<not> next_time t \<tau>' \<le> maxtime`] by metis
    hence ?case
      unfolding \<theta>'_def2 using `n < t` `t \<le> maxtime` `maxtime < next_time t \<tau>'`
      by transfer' auto }
  ultimately  show ?case
    by auto
qed(auto)

lemma borderline_big_step:
  fixes \<tau>' :: "'a trans_raw"
  assumes "maxtime, t', \<sigma>', \<gamma>', \<theta>' \<turnstile> <cs, \<tau>'(t':=0)> \<leadsto> beh"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t \<le> maxtime" and "maxtime < t'"
  assumes "\<And>n. t < n \<Longrightarrow> \<theta> n = 0"
  assumes "\<theta>' = add_to_beh \<sigma> \<theta> t t'"
  shows "\<And>n. n \<le> t' \<Longrightarrow> \<theta>' n = beh n"
  using assms
  by (induction rule:b_simulate_fin.induct, auto)


lemma beh_and_res_same_until_now:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>i. i < t \<Longrightarrow> i \<le> maxtime \<Longrightarrow>  \<theta> i = res i"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have "i < next_time t \<tau>"
    using `i < t` next_time_at_least[OF 1(8), of "t"] "1.prems"(3) less_le_trans next_time_at_least 
    by blast
  moreover have "i \<le> maxtime"
    using `i < t` `t \<le> maxtime` by auto
  moreover have "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0"
  proof -
    fix n
    assume "n < next_time t \<tau>'"
    hence "n < t \<or> t \<le> n \<and> n < next_time t \<tau>'"
      by auto
    moreover
    { assume "n < t"
      hence " \<tau>' n = 0"
        using b_conc_exec_preserve_trans_removal[OF 1(8), of "t"] 1(3)
        by auto }
    moreover
    { assume "t \<le> n \<and> n < next_time t \<tau>'"
      have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
      moreover
      { assume "\<tau>' = 0"
        hence " \<tau>' n = 0" by (auto simp add: zero_fun_def)}
      moreover
      { assume "\<tau>' \<noteq> 0"
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        with `t \<le> n \<and> n < next_time t \<tau>'` have " \<tau>' n = 0"
          using next_time_at_least2 by blast }
      ultimately have " \<tau>' n = 0" by blast
    }
    ultimately show " (\<tau>'(next_time t \<tau>' := 0)) n = 0"
      by auto
  qed
  ultimately have IH: " (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) i =  res i"
    using 1(5)[of "i"] 
    by (metis (full_types) "1.hyps"(3) "1.prems"(1) "1.prems"(3) b_conc_exec_preserve_trans_removal
    le_less_trans next_time_at_least not_le)
  have "t < next_time t \<tau>' \<or> \<not> t < next_time t \<tau>'"
    by auto
  moreover
  { assume "t < next_time t \<tau>'"
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') =  \<theta>(t :=(Some o \<sigma>))"
      unfolding add_to_beh_def by auto
    hence ?case
      using IH `i < t` by (simp) }
  moreover
  { assume "\<not> t < next_time t \<tau>'"
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>"
      unfolding add_to_beh_def by auto
    hence ?case
      using IH by auto }
  ultimately show ?case by auto
qed (auto)

lemma b_conc_exec_does_not_modify_signals2:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  assumes "s \<notin> set (signals_from cs)"
  shows   "\<And>i. next_time t \<tau>' \<le> i \<Longrightarrow> signal_of (\<sigma> s) \<tau> s i = signal_of (next_state t \<tau>' \<sigma> s) \<tau>' s i"
proof -
  have *: "\<And>i. \<tau> i s =  \<tau>' i s"
    using b_conc_exec_modifies_local'[OF assms(1-3)] by auto
  hence *: "to_trans_raw_sig \<tau> s = to_trans_raw_sig \<tau>' s"
    by (transfer', auto simp add: to_trans_raw_sig_def)
  hence **: "\<And>i. inf_time (to_trans_raw_sig \<tau>) s i = inf_time (to_trans_raw_sig \<tau>') s i"
    unfolding inf_time_def by auto
  fix i
  assume "next_time t \<tau>' \<le> i"
  { assume "inf_time (to_trans_raw_sig \<tau>') s i = None"
    hence "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>' s) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence 0: " (to_trans_raw_sig \<tau>' s) (next_time t \<tau>') = 0"
      using `next_time t \<tau>' \<le> i` by auto
    have "next_state t \<tau>' \<sigma> s = \<sigma> s"
    proof -
      define t' where "t' = next_time t \<tau>'"
      define m where "m =  \<tau>' t'"
      hence **: "next_state t \<tau>' \<sigma> s = override_on \<sigma> (the o m) (dom m) s"
        unfolding next_state_def t'_def m_def Let_def by auto
      have "s \<notin> dom m"
        using 0 unfolding t'_def[THEN sym] m_def  unfolding to_trans_raw_sig_def
        by (simp add: domIff zero_option_def)
      thus "next_state t \<tau>' \<sigma> s = \<sigma> s"
        unfolding ** by auto
    qed }
  note case_none = this
  have "to_signal (\<sigma> s) (to_trans_raw_sig \<tau>) s i =
                                           to_signal (next_state t \<tau>' \<sigma> s) (to_trans_raw_sig \<tau>') s i"
    using ** case_none unfolding to_signal_def  by (auto simp add: * split:option.splits)
  thus "signal_of (\<sigma> s) \<tau> s i = signal_of (next_state t \<tau>' \<sigma> s) \<tau>' s i"
    by auto
qed

definition context_invariant :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool" where
  "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<equiv> (\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0)
                               \<and> (\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)})
                               \<and> (\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0)"

lemma context_invariant_rem_curr_trans:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" shows "context_invariant t \<sigma> \<gamma> \<theta> (\<tau>(t:=0))"
  using assms unfolding context_invariant_def rem_curr_trans_def
  by (simp add: domIff)

lemma nonneg_delay_seq_next_time_strict:
  assumes "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0" 
  shows "(LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  obtain \<tau>'' where \<tau>''_def: "\<tau>'' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
    by auto
  have \<tau>'_def: "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def using Bcomp(3) by auto
  have "\<tau>'' \<noteq> 0 \<or> \<tau>'' = 0" by auto
  moreover
  { assume "\<tau>'' = 0"
    hence ?case
      using Bcomp(2) \<tau>'_def `\<tau>' \<noteq> 0` `nonneg_delay (Bcomp ss1 ss2)`  by (simp add: zero_fun_def) }
  moreover
  { assume "\<tau>'' \<noteq> 0"
    hence t_less: "(LEAST n. dom ( \<tau>'' n) \<noteq> {}) > t"
      using Bcomp(1) \<tau>''_def `nonneg_delay (Bcomp ss1 ss2)`  Bcomp(5) by auto
    have "\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0"
      using Bcomp(5)  unfolding \<tau>''_def  by (simp add: b_seq_exec_preserve_trans_removal)
    have "dom ( \<tau>'' t) = {}"
      using not_less_Least[OF t_less] by auto
    hence " \<tau>'' t = 0"
      by (transfer', auto simp add: zero_fun_def zero_option_def)
    hence "\<And>n. n \<le> t \<Longrightarrow>  \<tau>'' n = 0"
      using `\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0`  le_imp_less_or_eq by auto
    hence ?case
      using Bcomp(2) `nonneg_delay (Bcomp ss1 ss2)` \<tau>'_def `\<tau>' \<noteq> 0` by auto }
  ultimately show ?case by auto
next
  case (Bguarded x1 ss1 ss2)
  moreover hence "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  ultimately show ?case
    by (metis b_seq_exec.simps(3))
next
  case (Bassign_trans sig exp dly)
  hence "0 < dly" by auto
  have \<tau>'_def: "\<tau>' =  trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    using Bassign_trans by auto
  hence "\<tau>' \<noteq> 0"
    using Bassign_trans by auto
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_seq_exec_preserve_trans_removal Bassign_trans(3) Bassign_trans(1)
    by (metis dual_order.strict_implies_order)
  show ?case
  proof (rule ccontr)
    assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
    hence **: "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t"
      by auto
    with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      by (auto simp add: ext zero_fun_def zero_option_def)
    have " \<tau>' t =  (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly) t"
      unfolding \<tau>'_def by auto
    also have "... =  \<tau> t"
      using `0 < dly` unfolding rem_curr_trans_def
      by (auto simp add : trans_post_raw_def preempt_raw_def post_raw_def)
    also have "... = 0"
      using Bassign_trans(3) by auto
    finally have " \<tau>' t = 0"
      by auto
    with `\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0` have "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
      using antisym_conv2 by auto
    with ** have " \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {}) = 0"
      by auto
    hence "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) = {}"
      by (simp add: dom_def zero_fun_def zero_option_def)
    with LeastI_ex[OF *] show "False"
      by auto
  qed
next
  case (Bassign_inert sig exp dly)
  hence "0 < dly" by auto
  have \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    using Bassign_inert by auto
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_seq_exec_preserve_trans_removal Bassign_inert(1) Bassign_inert(3)
    by (metis dual_order.strict_implies_order)
  show ?case
  proof (rule ccontr)
    assume "\<not> t < (LEAST n. dom ( \<tau>' n) \<noteq> {})"
    hence **: "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t"
      by auto
    with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      by (auto simp add: ext zero_fun_def zero_option_def)
    have " \<tau>' t =  (inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly) t"
      unfolding \<tau>'_def by auto
    also have "... = 0"
    proof (cases "is_stable_raw dly \<tau> t sig (\<sigma> sig)")
      case True
      hence "inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
        (is "?lhs = ?rhs") unfolding inr_post_raw_def by auto
      hence " ?lhs t =  ?rhs t"
        by auto
      also have "... = 0"
        using Bassign_inert(3) `0 < dly`  by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
      finally show ?thesis
        by auto
    next
      case False
      hence "inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly"
        (is "?lhs = ?rhs") unfolding inr_post_raw_def by auto
      hence " ?lhs t =  ?rhs t"
        by auto
      also have "... = 0"
        using Bassign_inert(3) `0 < dly` using purge_raw_before_now_unchanged[of "\<tau>" "t" "dly" "sig" "purge_raw \<tau> t dly sig"]
         unfolding trans_post_raw_def post_raw_def
        by (smt add_cancel_right_right le_eq_less_or_eq not_add_less1 preempt_raw_def)
      finally show ?thesis
        by auto
    qed
    finally have " \<tau>' t = 0"
      by auto
    with `\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0` have "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
      using antisym_conv2 by auto
    with ** have " \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {}) = 0"
      by auto
    hence "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) = {}"
      by (simp add: dom_def zero_fun_def zero_option_def)
    with LeastI_ex[OF *] show "False"
      by auto
  qed
next
  case Bnull
  hence "\<tau>' = \<tau>"
    by auto
  hence 0: "\<And>n. n \<le> t \<Longrightarrow> dom ( \<tau>' n) = {}"
    using Bnull by (simp add: zero_fun_def zero_option_def)
  show ?case
  proof (rule ccontr)
    assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
    hence "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t"
      by auto
    moreover with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      unfolding zero_fun_def zero_option_def by auto
    ultimately have "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) \<noteq> {}"
      using LeastI_ex[OF *] by auto
    with 0 show "False"
      using `(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t` by auto
  qed
qed

lemma context_invariant:
  fixes \<tau> :: "'a trans_raw" 
  fixes t' :: "nat"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t < next_time t \<tau>'"
  defines "t' \<equiv> next_time t \<tau>'" and "\<sigma>' \<equiv> next_state t \<tau>' \<sigma>" and "\<gamma>' \<equiv> next_event t \<tau>' \<sigma>"
      and "\<theta>' \<equiv> add_to_beh \<sigma> \<theta> t t'" and "\<tau>'' \<equiv> \<tau>' (t' := 0)"
  shows "context_invariant t' \<sigma>' \<gamma>' \<theta>' \<tau>''"
proof -
  have 0: "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  hence 1: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
    using assms(3) next_time_at_least2 order.strict_trans1 by blast  
  have 2: "\<And>n. t \<le> n \<Longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  have " t \<le> next_time t \<tau>'"
    using assms(3) by auto
  have "\<forall>n. n < t' \<longrightarrow>  \<tau>' n = 0"
    using next_time_at_least2 t'_def by metis
  hence 3:  "\<forall>n. n \<le> t' \<longrightarrow> \<tau>'' n = 0"
    unfolding \<tau>''_def by auto
  have 4: "\<forall>n. t' \<le> n \<longrightarrow>  \<theta>' n = 0"
    unfolding \<theta>'_def add_to_beh_def t'_def using 2 `t \<le> next_time t \<tau>'`
    by auto
  have "\<And>s. signal_of False \<theta>' s (t' - 1) = \<sigma> s"
  proof -
    have "t \<le> t' - 1"
      using assms(3) unfolding t'_def by auto
    have "\<And>n. t < n \<Longrightarrow> n \<le> t' - 1 \<Longrightarrow>  \<theta>' n = 0"
      by (auto simp add: \<theta>'_def add_to_beh_def 2 `t < next_time t \<tau>'` t'_def)
    hence "\<And>s. signal_of  False \<theta>' s (t' - 1) = signal_of False \<theta>' s t"
      using signal_of_less_ind[OF _ `t \<le> t' - 1`] by metis 
    moreover have "\<And>s. signal_of False \<theta>' s t = \<sigma> s"
      using trans_some_signal_of unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'`
      by (metis (full_types) fun_upd_same t'_def)
    finally show "\<And>s. signal_of False \<theta>' s (t' - 1) = \<sigma> s"
      by auto
  qed
  hence "\<gamma>' = {s. \<sigma>' s \<noteq> signal_of False \<theta>' s (t' - 1)}"
    unfolding \<gamma>'_def next_event_alt_def \<sigma>'_def by auto
  thus ?thesis
    using 3 4 unfolding \<gamma>'_def t'_def \<theta>'_def \<sigma>'_def context_invariant_def by auto
qed

lemma nonneg_delay_conc_next_time_strict:
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs"
  assumes "conc_stmt_wf cs" (* this is only to make the proof about parallel composition easier; try to remove this *)
  shows "t < next_time t \<tau>'"
proof (cases "\<tau>' \<noteq> 0")
  case True
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(1)] assms(2)
    by (meson assms(1) b_conc_exec_preserve_trans_removal order.strict_implies_order)
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least by auto
  moreover have "(LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
    using assms True
  proof (induction cs arbitrary: \<tau> \<tau>')
    case (Bpar cs1 cs2)
    obtain \<tau>'' where \<tau>''_def: "\<tau>'' = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
      by auto
    hence \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>''"
      using Bpar(4) unfolding \<tau>''_def using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)`]
      by auto
    have "\<tau>'' = 0 \<or> \<tau>'' \<noteq> 0" by auto
    moreover
    { assume "\<tau>'' = 0"
      hence *: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>'' n = 0"
        by (auto simp add: zero_fun_def zero_option_def)
      have ?case
        using Bpar(2)[OF * _ _ _ `\<tau>' \<noteq> 0`] \<tau>'_def `nonneg_delay_conc (cs1 || cs2)` `conc_stmt_wf (cs1 || cs2)`
        by (simp add: conc_stmt_wf_def) }
    moreover
    { assume "\<tau>'' \<noteq> 0"
      hence t_less: "t < (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
        using Bpar(1)[OF Bpar(3)] \<tau>''_def `nonneg_delay_conc (cs1 || cs2)` `conc_stmt_wf (cs1 || cs2)`
        unfolding conc_stmt_wf_def by auto
      have "\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0"
        using \<tau>''_def Bpar(3) by (simp add: b_conc_exec_preserve_trans_removal)
      have "dom ( \<tau>'' t) = {}"
        using not_less_Least[OF t_less] by auto
      hence " \<tau>'' t = 0"
        by (transfer', auto simp add: zero_fun_def zero_option_def)
      hence "\<And>n. n \<le> t \<Longrightarrow>  \<tau>'' n = 0"
        using `\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0`  le_imp_less_or_eq by auto
      hence ?case
        using Bpar(2) `nonneg_delay_conc (cs1 || cs2)` \<tau>'_def `\<tau>' \<noteq> 0`  `conc_stmt_wf (cs1 || cs2)`
        unfolding conc_stmt_wf_def by auto }
    ultimately show ?case
      by auto
  next
    case (Bsingle sl ss)
    have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>" by auto
    moreover
    { assume "disjnt sl \<gamma>"
      hence "\<tau>' = \<tau>"
        using Bsingle by auto
      hence 0: "\<And>n. n \<le> t \<Longrightarrow> dom ( \<tau>' n) = {}"
        using Bsingle by (simp add: zero_fun_def zero_option_def)
      have ?case
      proof (rule ccontr)
        assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
        hence "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t"
          by auto
        moreover with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
          unfolding zero_fun_def zero_option_def by auto
        ultimately have "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) \<noteq> {}"
          using LeastI_ex[OF *] by auto
        with 0 show "False"
          using `(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<le> t` by auto
      qed }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "t , \<sigma> , \<gamma> , \<theta> \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
        using Bsingle by auto
      moreover have "nonneg_delay ss"
        using Bsingle by auto
      ultimately have ?case
        using Bsingle `\<tau>' \<noteq> 0` using nonneg_delay_seq_next_time_strict by metis }
    ultimately show ?case by auto
  qed
  ultimately show ?thesis
    using `\<tau>' \<noteq> 0` unfolding next_time_def by auto
next
  case False
  hence "\<tau>' = 0"
    by auto
  thus ?thesis
    unfolding next_time_def by auto
qed

lemma context_invariant':
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>':=0))"
proof -
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using assms(1) unfolding context_invariant_def by auto
  hence "t < next_time t \<tau>'"
    using nonneg_delay_conc_next_time_strict[OF _ assms(2) assms(3) assms(4)]
    by auto
  with context_invariant[OF assms(1-2)] show ?thesis by auto
qed

lemma context_invariant_hist:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "\<forall>n\<ge>next_time t \<tau>'. (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
proof -
  have *: "\<forall>n\<ge>t.  \<theta> n = 0" and "\<forall>n<t.  \<tau> n = 0"
    using assms(2) unfolding context_invariant_def by auto
  hence "\<forall>n < t.  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal assms(1) by blast
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least by auto
  show ?thesis
    unfolding add_to_beh_def using * `t \<le> next_time t \<tau>'`
    by  auto
qed

lemma context_invariant_event:
  assumes "\<forall>n \<le> t.  \<tau> n = 0"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "\<forall>n \<ge> t.  \<theta> n = 0"
  shows "next_event t \<tau>' \<sigma> = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)} "
proof -
  have "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    using assms(1) by auto
  hence 3: "t < next_time t \<tau>'"
    using nonneg_delay_conc_next_time_strict[OF _ assms(2) assms(3) assms(4)]
    by auto
  define \<theta>' where \<theta>'_def: "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
  define t' where t'_def: "t' = next_time t \<tau>'"
  have "\<And>s. signal_of False \<theta>' s (t' - 1) = \<sigma> s"
  proof -
    have "t \<le> t' - 1"
      using 3 unfolding t'_def by auto
    have "\<And>n. t < n \<Longrightarrow> n \<le> t' - 1 \<Longrightarrow>  \<theta>' n = 0"
      by (auto simp add: assms `t < next_time t \<tau>'` t'_def \<theta>'_def add_to_beh_def) 
    hence "\<And>s. signal_of  False \<theta>' s (t' - 1) = signal_of False \<theta>' s t"
      using signal_of_less_ind[OF _ `t \<le> t' - 1`] by metis
    moreover have "\<And>s. signal_of False \<theta>' s t = \<sigma> s"
      using trans_some_signal_of unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'`
      by (metis (full_types) fun_upd_same)
    finally show "\<And>s. signal_of False \<theta>' s (t' - 1) = \<sigma> s"
      by auto 
  qed
  hence "next_event t \<tau>' \<sigma> = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of False \<theta>' s (t' - 1)}"
    unfolding next_event_alt_def by auto
  thus ?thesis
    unfolding \<theta>'_def t'_def by auto
qed

lemma nonneg_delay_same:
  assumes "nonneg_delay ss"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  shows " \<tau> t =  \<tau>' t"
  using assms
proof (induction ss arbitrary:\<tau> \<tau>')
  case (Bcomp ss1 ss2)
  thus ?case
    by (metis b_seq_exec.simps(2) nonneg_delay.simps(2))
next
  case (Bguarded x1 ss1 ss2)
  then show ?case
    by (metis b_seq_exec.simps(3) nonneg_delay.simps(3))
next
  case (Bassign_trans sig exp dly)
  hence \<tau>'_def: "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence "t < t + dly"
    by auto
  then show ?case
    unfolding \<tau>'_def by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
next
  case (Bassign_inert sig exp dly)
  hence \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  have "is_stable_raw dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence \<tau>'_def': "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
      unfolding \<tau>'_def inr_post_raw_def by auto
    have "t < t + dly"
      using `0 < dly` by auto
    hence ?case
      unfolding \<tau>'_def' by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def) }
  moreover
  { assume "\<not> is_stable_raw dly \<tau> t sig (\<sigma> sig)"
    hence \<tau>'_def': "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) (purge_raw \<tau> t dly sig) t dly"
      unfolding \<tau>'_def inr_post_raw_def by auto
    have "t < t + dly"
      using `0 < dly` by auto
    hence " \<tau>' t =  (purge_raw \<tau> t dly sig) t"
      unfolding \<tau>'_def' by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def)
    also have "... =  \<tau> t"
      using purge_raw_before_now_unchanged by (metis order_refl)
    finally have " \<tau> t =  \<tau>' t"
      by auto }
  ultimately show ?case by auto
next
  case Bnull
  then show ?case by auto
qed

text \<open>Again, the context invariant is preserved when we have non-negative delay in the sequential
statement.\<close>

lemma b_seq_exec_preserves_context_invariant:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  shows "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
proof -
  have "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    using assms(1) unfolding context_invariant_def by auto
  hence 0: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
    using assms(2) b_seq_exec_preserve_trans_removal 
    by (metis assms(3) le_less nonneg_delay_same)
  thus ?thesis
    using assms(1) unfolding context_invariant_def by auto
qed

lemma nonneg_delay_conc_same:
  assumes "nonneg_delay_conc cs"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  shows " \<tau> t =  \<tau>' t"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar \<tau>1_def by (meson b_conc_exec.simps(2))
  moreover have "\<tau>1 t = \<tau> t" and "\<tau>2 t = \<tau> t"
    using Bpar \<tau>1_def \<tau>2_def by (metis nonneg_delay_conc.simps(2))+
  ultimately have "\<tau>' t = \<tau> t"
    by (auto simp add: clean_zip_raw_def)
  then show ?case 
    by auto
next
  case (Bsingle x1 x2)
  then show ?case 
    using nonneg_delay_same by fastforce
qed

lemma b_conc_exec_preserves_context_invariant:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs"
  shows "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  have \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar(4) unfolding \<tau>1_def \<tau>2_def by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    using Bpar(1) Bpar(3) Bpar(5)  using \<tau>1_def nonneg_delay_conc.simps(2) by blast
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>2"
    using Bpar.IH(2) Bpar.prems(1) Bpar.prems(3) \<tau>2_def nonneg_delay_conc.simps(2) by blast
  have "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    using Bpar(3) unfolding context_invariant_def by auto
  hence "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal Bpar(4)  
    by (metis Bpar.prems(3) dual_order.order_iff_strict nonneg_delay_conc_same)
  then show ?case
    using Bpar(3) unfolding context_invariant_def by auto
next
  case (Bsingle sl ss)
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence "\<tau>' = \<tau>"
      using Bsingle by auto
    hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
      using Bsingle(1) by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
      using Bsingle by auto
    moreover have "nonneg_delay ss"
      using Bsingle by auto
    hence ?case
      using b_seq_exec_preserves_context_invariant Bsingle by fastforce }
  ultimately show ?case by auto
qed

definition degree :: "'a trans_raw \<Rightarrow> nat" where
  "degree \<tau> = (LEAST n. \<forall>t \<ge>n. \<tau> t = 0)"

lemma
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" shows "degree \<theta> \<le> t"
proof -
  have "\<forall>k \<ge> t. \<theta> k = 0"
    using assms unfolding context_invariant_def by auto
  thus ?thesis
    unfolding degree_def by (simp add: Least_le)
qed  

text \<open>An important theorem for any inductive definition; the computation should be deterministic.\<close>

theorem b_simulate_fin_deterministic:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res2"
  shows "res2 = res1"
  using assms apply (induction arbitrary: res2 rule:b_simulate_fin.induct)
  using case_bau apply blast
  using case_quiesce apply blast
  using case_timesup by blast

inductive b_simulate :: "nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  where
  "     init' 0 def_state {} 0 cs \<tau> = \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def_state = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def_state = \<gamma>'
   \<Longrightarrow>  add_to_beh def_state 0 0 t' = beh'
   \<Longrightarrow>  maxtime, t', \<sigma>', \<gamma>', beh' \<turnstile> <cs, \<tau>'(t' := 0)> \<leadsto> res
   \<Longrightarrow>  b_simulate maxtime cs \<tau> res"

text \<open>Judgement @{term "b_simulate"} contains one rule only: executing the @{term "init'"} rule
before @{term "b_simulate_fin"}.\<close>

inductive_cases bsim : "b_simulate maxtime cs \<tau> res"

lemma bsimulate_obt_big_step:
  assumes "b_simulate maxtime cs \<tau> res"
  assumes "init' 0 def_state {} 0 cs \<tau> = \<tau>'"
  shows "maxtime, next_time  0 \<tau>', next_state 0 \<tau>' def_state, next_event 0 \<tau>' def_state,
                             add_to_beh def_state 0 0 (next_time  0 \<tau>') \<turnstile> <cs, \<tau>'(next_time 0 \<tau>' := 0)> \<leadsto> res"
  using bsim[OF assms(1)] assms by auto

text \<open>Similar to the theorem accompanying @{term "b_simulate_fin"}, i.e.
@{thm "b_simulate_fin_deterministic"}, the rule @{term "b_simulate"} is also deterministic.\<close>

theorem b_sim_init_deterministic:
  assumes "b_simulate maxtime cs \<tau> res1"
  assumes "b_simulate maxtime cs \<tau> res2"
  shows "res2 = res1"
  using assms apply (induction arbitrary:res2 rule:b_simulate.induct)
  using bsimulate_obt_big_step b_simulate_fin_deterministic by blast

subsection \<open>Small step semantics of simulation\<close>

text \<open>The motivation behind the formulation of small step semantic is due to code generation. We
want to simulate the behaviour of a VHDL text in Isabelle. Because the simulation function is
defined with inductive definition (we could not formalise it with function because it is possible
to have non terminating VHDL text), the property that the corresponding code is the same with
@{term "b_simulate_fin"} or @{term "b_simulate"} depends whether the VHDL text terminates or not.
We cannot talk about termination with big step semantics. Hence, we also formalise the small-step
semantics and prove (only one way) that the small step implies the big step semantics.\<close>

type_synonym 'signal configuration_raw = "nat \<times> 'signal  state \<times> 'signal event \<times> 'signal trans_raw"

fun update_config_raw :: "'signal configuration_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal configuration_raw"
  where
  "update_config_raw (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (let t' = next_time t \<tau>';
                                        \<sigma>' = next_state t \<tau>' \<sigma>;
                                        \<gamma>' = next_event t \<tau>' \<sigma>;
                                        \<theta>' = add_to_beh \<sigma> \<theta> t t'
                                    in (t', \<sigma>', \<gamma>', \<theta>'))"

inductive b_simulate_fin_ss :: "nat \<Rightarrow> 'signal conc_stmt \<Rightarrow>
  'signal trans_raw \<times> 'signal configuration_raw  \<Rightarrow>  'signal trans_raw \<times> 'signal configuration_raw \<Rightarrow> bool"
  where
   \<comment> \<open>Time is up\<close>
 "  \<not>  t \<le> maxnat
   \<Longrightarrow> b_simulate_fin_ss maxnat cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxnat + 1, \<sigma>, \<gamma>, \<theta>)"

   \<comment> \<open>The simulation has quiesced and there is still nat\<close>
| "    t \<le> maxnat
   \<Longrightarrow> quiet \<tau> \<gamma>
   \<Longrightarrow> b_simulate_fin_ss maxnat cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxnat + 1, \<sigma>, \<gamma>, \<theta>(t:= Some o \<sigma>))"

   \<comment> \<open>Business as usual: not quiesced yet and there is still nat\<close>
| "    t \<le> maxnat
   \<Longrightarrow> \<not> quiet \<tau> \<gamma>
   \<Longrightarrow> t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'
   \<Longrightarrow> update_config_raw (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>')
   \<Longrightarrow> b_simulate_fin_ss maxnat cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>'(t':=0), t', \<sigma>', \<gamma>', \<theta>')"

inductive_cases sim_ss_ic : "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"

lemma
  assumes "t \<le> maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxtime, \<sigma>, \<gamma>, res')"
  shows "\<theta>(t:= Some o \<sigma>) = res'"
  using assms by (auto intro:sim_ss_ic)

lemma
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  shows "update_config_raw (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>')"
  using assms by (auto intro:sim_ss_ic)

theorem b_simulate_fin_ss_deterministic:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1)"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2)"
  shows "(\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1) = (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2)"
  using assms
proof (induction arbitrary: \<tau>2 t2 \<sigma>2 \<gamma>2 \<theta>2 rule: b_simulate_fin_ss.induct)
  case (1 t maxtime \<theta> res' cs \<tau> \<sigma> \<gamma>)
  thus ?case
    by (auto intro!: sim_ss_ic[OF 1(2)])
next
  case (2 t maxtime \<tau> \<gamma> \<theta> \<sigma> res' cs)
  thus ?case
    by (auto intro!: sim_ss_ic[OF 2(3)])
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' t' \<sigma>' \<gamma>' \<theta>')
  show ?case
    by (smt "3.hyps"(1) "3.hyps"(2) "3.hyps"(3) "3.hyps"(4) "3.prems" sim_ss_ic update_config_raw.simps)
qed

abbreviation
  simulate_ss :: "nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trans_raw \<times> 'signal configuration_raw
                                             \<Rightarrow>  'signal trans_raw \<times> 'signal configuration_raw \<Rightarrow> bool"
  where "simulate_ss maxnat cs \<rho> \<rho>' \<equiv> star (b_simulate_fin_ss maxnat cs) \<rho> \<rho>'"


lemma b_simulate_fin_ss_preserve_hist:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "\<And>n. (min (maxtime+1) t)  \<le> n \<Longrightarrow>  \<theta> n = 0"
  assumes "\<And>n. n  < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. (min (maxtime+1) t') \<le> n \<Longrightarrow>  \<theta>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "min (maxtime+1) t' \<le> n" and " t' = Suc maxtime " and "\<not> t \<le> maxtime" and "\<theta>' = \<theta>"
  thus "  \<theta>' n = 0"
    using assms(2) by auto
next
  fix n
  assume "min (maxtime+1) t' \<le> n"
  assume "t \<le> maxtime"
  assume *: " \<theta>' =  \<theta>(t:=(Some \<circ> \<sigma>))"
  assume t'_def: "t' = Suc maxtime"
  hence "maxtime < n"
    using `min (maxtime+1) t' \<le> n` by auto
  hence " \<theta>' n =  \<theta> n"
    using * `min (maxtime+1) t' \<le> n` `t \<le> maxtime` by  auto
  thus " \<theta>' n = 0"
    using `min (maxtime+1) t' \<le> n` t'_def `t \<le> maxtime` assms(2) by auto
next
  fix n
  assume "t \<le> maxtime"
  assume "min (maxtime + 1) t' \<le> n"
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)
          in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
                , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
                , add_to_beh \<sigma> \<theta> t t')) =
         (t', \<sigma>', \<gamma>', \<theta>')"
  hence t'_def: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)"
    and \<theta>'_def: "\<theta>' = (if t < t' then \<theta>(t:=(Some o \<sigma>)) else \<theta>)"
    unfolding Let_def add_to_beh_def by auto
  have "t' \<le> maxtime+1 \<or> maxtime+1 < t'"
    by auto
  moreover
  { assume "t' \<le> maxtime+1"
    hence "t' \<le> n"
      using `min (maxtime+1) t' \<le> n` by auto
    have "t < t' \<or> t' \<le> t" by auto
    moreover
    { assume "t < t'"
      hence **: " \<theta>' n =  \<theta> n"
        using `t' \<le> n` `t < t'` \<theta>'_def unfolding add_to_beh_def
        by  auto
      have *: "\<And>n. n < t \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) n = 0"
        using b_conc_exec_preserve_trans_removal[OF assms(3)] by auto
      have "t \<le> t'"
        using next_time_at_least[OF *] t'_def by auto
      with `t' \<le> n` have "t \<le> n" by auto
      with assms(2) have "  \<theta>' n = 0"
        using ** by auto }
    moreover
    { assume "t' \<le> t"
      define \<tau>'' where "\<tau>'' = b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>"
      have temp : "\<And>n. n  < t \<Longrightarrow>  \<tau>'' n = 0"
        using b_conc_exec_preserve_trans_removal[OF assms(3), of "t"] unfolding \<tau>''_def by auto
      have "t' = t" using next_time_at_least[OF temp, of "t"] t'_def `t' \<le> t` unfolding \<tau>''_def
        by (simp add: dual_order.antisym)
      hence "\<theta>' = \<theta>" using \<theta>'_def by auto
      hence " \<theta>' n = 0"
        using assms(2) `t' \<le> n` `t' = t` by auto }
    ultimately have " \<theta>' n = 0" by auto }
  moreover
  { assume "maxtime + 1 < t'"
    hence "maxtime + 1 \<le> n"
      using `min (maxtime+1) t' \<le> n` by auto
    hence "t < t'"
      using `t \<le> maxtime` `maxtime + 1 < t'` by auto
    hence "\<theta>' = \<theta>(t := (Some o \<sigma>))"
      using \<theta>'_def by auto
    moreover have "t < n"
      using `t \<le> maxtime` and `maxtime + 1 \<le> n` by auto
    ultimately have " \<theta>' n =  \<theta> n"
      by  auto
    hence "\<theta>' n = 0"
      using assms(2) `maxtime + 1 \<le> n` `t \<le> maxtime` by auto }
  ultimately show " \<theta>' n = 0"
    by auto
qed

lemma small_step_preserve_trans_removal:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "\<And>n. n < t  \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t' \<Longrightarrow>  \<tau>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "t' = Suc maxtime"
  assume "\<not> t \<le> maxtime" hence "maxtime < t" by auto
  hence "t' \<le> t" using `t' = Suc maxtime` by auto
  assume "n < t'" and "\<tau>' = \<tau>"
  hence "n < t" using `t' \<le> t` by auto
  thus " \<tau>' n = 0"
    using assms(2) `\<tau>' = \<tau>` by auto
next
  fix n
  assume "t' = Suc maxtime" and "t \<le> maxtime"
  assume "quiet \<tau> \<gamma>"
  hence "\<tau> = 0"  by (meson quiet_def)
  moreover assume "\<tau>' = \<tau>"
  ultimately have "\<tau>' = 0" by auto
  thus " \<tau>' n = 0" by (auto simp add: zero_fun_def)
next
  fix n
  assume "n < t'"
  assume \<tau>'_def: "\<tau>' = (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)(t':=0)"
  have *: "\<And>n. n < t \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) n = 0"
    using assms(2)  by (simp add: b_conc_exec_preserve_trans_removal)
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)
          in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
                , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
                , add_to_beh \<sigma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
  hence **: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)"
    unfolding Let_def \<tau>'_def by auto
  hence "t \<le> t'"
    using next_time_at_least[OF *] by auto
  hence "\<And>n. n < t' \<Longrightarrow>  (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) n = 0"
    using next_time_at_least2[OF sym[OF **]] by auto
  thus " \<tau>' n = 0"
    using `n < t'` unfolding \<tau>'_def  by (simp add: rem_curr_trans_preserve_trans_removal)
qed


lemma ss_big_continue:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "b_simulate_fin maxtime t' \<sigma>' \<gamma>' \<theta>' cs \<tau>' res"
  assumes "\<forall>n. (min (maxtime+1) t)  \<le> n \<longrightarrow> \<theta> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> res"
proof (rule sim_ss_ic[OF assms(1)])
  assume "\<not> t \<le> maxtime" hence "maxtime < t" by auto
  hence "Suc (maxtime) \<le> t" by auto
  assume **: "\<theta>' = \<theta>"
  hence *: " \<theta>' (Suc maxtime) = 0"
    using assms(3) by auto
  assume t'suc: "t' = Suc maxtime"
  have "res = \<theta>' "
    using case_timesup[OF _ assms(2)] t'suc by auto
  with `\<not> t \<le> maxtime` show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    by (simp add: "**" b_simulate_fin.intros(3))
next
  \<comment> \<open>from small step\<close>
  assume t'suc: "t' = Suc maxtime"
  assume "t \<le> maxtime"
  assume "(quiet \<tau> \<gamma>)"
  assume **: "\<theta>' = \<theta>(t:= (Some \<circ> \<sigma>))"
  hence *: " \<theta>' (Suc maxtime) = 0"
    using assms(1) assms(3) t'suc \<open>t \<le> maxtime\<close> by auto

  \<comment> \<open>from big step\<close>
  have "res = \<theta>'"
    using t'suc case_timesup[OF _ assms(2)] t'suc by auto
  hence "\<theta>(t:=(Some o \<sigma>)) = res" by (simp add: "**")
  with `t \<le> maxtime` show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    using `quiet \<tau> \<gamma>` by (auto intro: b_simulate_fin.intros)
next
  assume asm1: "t \<le> maxtime"
  assume asm2: "\<not> quiet \<tau> \<gamma>"
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)
     in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
           , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>
           , add_to_beh \<sigma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
  hence t'_def: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)" and
        \<sigma>'_def: "\<sigma>' = next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>" and
        \<gamma>'_def: "\<gamma>' = next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) \<sigma>" and
        \<theta>'_def: "\<theta>' = add_to_beh \<sigma> \<theta> t t'"
    unfolding Let_def by auto
  assume \<tau>'_def: "\<tau>' = (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>)(t':=0)"
  from b_simulate_fin.intros(1)[OF asm1 asm2] assms(2)
  show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    unfolding t'_def \<sigma>'_def \<gamma>'_def \<theta>'_def \<tau>'_def by auto
qed

theorem small_step_implies_big_step:
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  assumes "\<forall>n. (min (maxtime+1) t) \<le> n \<longrightarrow>  \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> \<tau> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> (\<theta>'(maxtime + 1:= 0))"
  using assms
proof (induction "(\<tau>, t, \<sigma>, \<gamma>, \<theta>)" "(\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')" arbitrary: \<tau> t \<sigma> \<gamma> \<theta>
                                                                                  rule: star.induct)
  case refl
  hence " \<theta>'(maxtime + 1:= 0)= \<theta>'"
     unfolding override_on_def by auto
  then show ?case
    using b_simulate_fin.intros(3)[of "maxtime + 1" "maxtime" "\<sigma>'" "\<gamma>'" "\<theta>'(maxtime+1 := 0)" "cs" "\<tau>'"]
    by auto
next
  case (step y)
  obtain \<tau>'' t'' \<sigma>'' \<gamma>'' \<theta>'' where y_def: "y = (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'')"
    using prod_cases5 by blast
  hence *: "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'')"
    using step(1) by auto
  have **: "\<forall>n\<ge> (min (maxtime+1) t'').  \<theta>'' n = 0"
    using b_simulate_fin_ss_preserve_hist[OF *] step.prems by auto   
  have ***: "\<forall>n<t''.  \<tau>'' n = 0"
    using "*" small_step_preserve_trans_removal step.prems(2) by blast
  show ?case
    using ss_big_continue[OF * step(3)[OF y_def ** ***] step(4)] by auto
qed

end